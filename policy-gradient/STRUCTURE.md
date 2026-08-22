# Structure: making gaps fall out of the build

`GAPS.md` lists ten gaps found by an audit — reading proofs and grepping for
callers. The build reported none of them. `lake build` was green, `sorry` count
was zero, `#print axioms` was clean.

That is the actual problem. An audit is a one-shot, human-attention-bounded
process that finds what the auditor thought to look for. This document proposes
making the same findings **fall out of the build**, so they are continuous,
exhaustive over the property they check, and cannot silently regress.

The mechanism below is **not a proposal — it is implemented and validated.**
Output from a working run is quoted verbatim.

---

## The one distinction that generates almost every gap

Every theorem here is one of two kinds:

- **Grounded** — its conclusion says something about an actual `FiniteMDP`.
- **Abstract** — it is a fact about real numbers, sequences, or functions.

Abstract theorems are *legitimate and valuable*: `Rate.lean`'s `1/t` induction is
the cleanest thing in the repo and no paper writes it out. The failure is not
having abstract lemmas. **The failure is naming an abstract lemma after a paper
theorem and never instantiating it.**

`mei_theorem4` is a true theorem about real sequences, instantiable at `f = 0`.
`mei_theorem6` mentions no entropy, no policy, no MDP. Both are named after
results in a paper about softmax policy gradient. Nothing in the build objected.

So the invariant to enforce is:

> **A declaration that claims to formalize a paper result must have a conclusion
> that mentions the object the paper is about, and must declare every assumption
> it makes about that object.**

---

## Implemented: the `@[paper]` attribute

`PolicyGradient/Meta/Paper.lean` (built and working):

```lean
@[paper "Mei2020" "Theorem 4"]
theorem mei_theorem4 ... 
```

The attribute stores `(declName, paper, result)` in a persistent environment
extension. Two things follow that grep cannot do:

1. **The claim is machine-readable**, so it can be checked.
2. **The claim is separated from the docstring**, so prose drifting away from
   content (seven cases in `GAPS.md`) becomes detectable rather than invisible.

### The grounding linter

For each `@[paper]` declaration, walk the binder telescope; collect binders whose
type mentions `FiniteMDP`; then ask whether the **conclusion actually depends on
one of those binders** (an `fvar` dependency check — *not* a syntactic scan of the
type, which wrongly passes everything since `M` appears as a local variable).

Verbatim output on the current repo:

```
UNGROUNDED PolicyGradient.mei_theorem4  [Mei2020 Theorem 4]  -- conclusion says nothing about any MDP
UNGROUNDED PolicyGradient.mei_theorem6  [Mei2020 Theorem 6]  -- conclusion says nothing about any MDP
UNGROUNDED PolicyGradient.domination_rate  [AKM2021 Theorem 4.1]  -- conclusion says nothing about any MDP
GROUNDED PolicyGradient.smoothAt_V_final  [AKM2021 Lemma E.4]   (MDP-level hypotheses: 4)
      assumes: ∀ (t : ℝ) (j : ℕ) (s' : S), |dLocalTerm M PF t j s'| ≤ 3 / (1 - M.γ)
      assumes: ∀ (s' : S) (a : A), |M.r s' a| ≤ 1
      assumes: 0 ≤ M.γ
      assumes: M.γ < 1
GROUNDED PolicyGradient.policy_gradient  [Sutton1999 Policy Gradient]   (MDP-level hypotheses: 0)
GROUNDED PolicyGradient.performance_difference  [Kakade2002 Performance Difference]   (MDP-level hypotheses: 0)
```

This separates all four cases correctly and with no tuning:

| Verdict | Meaning |
|---|---|
| `GROUNDED`, 0 MDP-hypotheses | fully proved about the MDP (`policy_gradient`) |
| `GROUNDED`, *n* MDP-hypotheses | real, but *n* declared gaps — **`hdloc` (G7) is printed verbatim** |
| `UNGROUNDED` | **G1, G2, G10** — the critical finding |

The audit's headline conclusion is reproduced mechanically, in one build step.

### What must accompany it

An `UNGROUNDED` claim should not merely warn, or it will be ignored. The rule:

- `@[paper]` **requires** grounding. Ungrounded ⇒ **build error**.
- An abstract lemma supporting a paper result gets `@[paper_tool "Mei2020" "Theorem 4"]`
  instead — asserting only "this is machinery *for*", never "this *is*".
- Every MDP-level hypothesis on a `@[paper]` theorem must carry a
  `@[gap "G7"]`-style justification or a pointer to the theorem that discharges
  it, so the count in the linter output is never silently nonzero.

Under this rule, `mei_theorem4` could not keep its name. **This was carried out
on 2026-08-22:** it is now
`@[paper_tool "Mei2020" "Theorem 4"] theorem smooth_loja_rate`, and the name
`mei_theorem4` is reserved for the grounded statement that does not yet exist.
**That is the property we want: the missing work is named and visibly absent,
instead of being silently occupied by something weaker.**

---

## Second check: instantiation reachability

Grounding is necessary, not sufficient. `smoothAt_V_final` is grounded and has
**zero callers** — its content terminates in nothing (G-note in `GAPS.md`).

The naive check ("MDP theorem nobody uses") is too noisy: it flags every headline
result, since `policy_gradient` legitimately has no callers. Tested — it returned
40 declarations including all the good ones.

The precise check uses the `@[paper]` data:

> Every `@[paper_tool]` lemma must be **transitively used by** at least one
> `@[paper]`-grounded theorem.

An abstract lemma that no grounded theorem depends on is, by construction, doing
no work for any paper claim. That flags today's entire `AKM.lean` rate track and
`smoothAt_V_final`'s dead end, while leaving `policy_gradient` alone. The
implementation is the `getUsedConstants` traversal already prototyped (it
correctly computed the full use-set of the repo).

---

## Third check: concrete-instance obligations

G6 — no softmax `DiffPolicy` exists — is a different species. Nothing is
mis-stated; a required *object* is missing, so every softmax-specific lemma
(`sum_abs_score_le_one`) is stranded with nothing to attach to.

The general principle:

> A parameterized development must be accompanied by at least one concrete
> instance, and the headline theorems must be instantiated at it.

Concretely: a `Instances.lean` that constructs `softmaxC2Policy` and *applies*
the headline theorems to it. This is the same discipline as the existing
`independent_check.py` — which exists precisely because Lean cannot verify that
definitions are the intended ones — extended from definitions to theorems.

The build then fails when `V` is right but the theorem about it is vacuous.

---

## Fourth check: hypothesis provenance

The subtlest gap, G3 (`hlt : ∀ t, f (x t) < fstar`), was nearly missed by the
audit. It is not exotic-looking; it reads like a side condition, and it is false
whenever the algorithm reaches the optimum exactly.

A hypothesis on a `@[paper]` theorem should be classifiable, and the
classification recorded in the source:

| Class | Meaning | Example |
|---|---|---|
| `structural` | side condition | `0 ≤ γ`, `γ < 1`, `1 ≤ T` |
| `paper_assumes` | the paper assumes it too | `\|r\| ≤ 1` |
| `discharged_by n` | theorem `n` proves it | `hscore` ← `sum_abs_score_le_one` |
| `gap "Gk"` | **known unproved content** | `hloja` ← G1 |

The linter requires every hypothesis to be classified, and reports the `gap` set
as the repo's honest debt. `GAPS.md` then becomes *generated*, not hand-written —
which matters, because a hand-written gap list drifts exactly the way the
docstrings did.

---

## What this would have caught, and what it would have missed

**Caught, mechanically:** G1, G2, G10 (ungrounded); G7 and the `hscore` link
(printed as MDP-level hypotheses); the `smoothAt_V_final` dead end
(reachability); G6 (no concrete instance); G3 (unclassified hypothesis).

**Not caught:** G4 (transfer error / concentrability undefined) and G5 (scalar
parameter). Both are cases where the formalization is *self-consistent but models
the wrong thing*. No linter detects "the paper's `θ ∈ ℝ^(S×A)` was rendered as
`θ ∈ ℝ`" — that requires a human comparing to the paper.

This is worth stating plainly rather than overselling the tooling: **structure
catches drift between claim and content; it does not catch a faithful
formalization of the wrong statement.** For that, the only real defence is the
one already in use here — pinning statements numerically against an independent
implementation before proving them, which is how the `1/(1-γ)` normalization trap
and the closed-form indexing were caught.

The honest split is roughly: **8 of 10 gaps become build failures; 2 remain human
work.** That is a large gain and not a complete one.

---

## Ordering

1. ~~**Correct the seven overclaiming docstrings**~~ — **done 2026-08-22.**
2. **Land `@[paper]` + the grounding linter** — implemented, validated, and
   wired into CI as a required step (2026-08-22).
3. ~~**Rename** `mei_theorem4`/`mei_theorem6`/`domination_rate`~~ — **done
   2026-08-22**: now `smooth_loja_rate`, `geometric_rate`,
   `domination_rate_abstract`. The paper names are free and unoccupied.
4. **Hypothesis classification**, generating `GAPS.md`.
5. **Reachability check**, once `@[paper_tool]` annotations exist.
6. Then the mathematics: **G5 → G6 → {G7, G1 → G2} , G8, G10**.

Steps 1–5 are days, not weeks, and they make step 6's progress *visible* — each
closed gap flips a linter line from `gap` to `discharged_by`, and the count of
ungrounded paper claims is a number that should only ever go down.
