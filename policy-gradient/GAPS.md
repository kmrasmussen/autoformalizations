# Gaps: what is assumed rather than proved

**Status: 2026-08-22.** The repo has zero `sorry` and `#print axioms` is clean on
every theorem. Neither fact means what a reader is likely to assume.

Unproved content in this repo does not live in `sorry`. It lives in **hypothesis
positions**. A `sorry` is a hole Lean reports; a hypothesis is a hole Lean
type-checks happily, because the obligation moves to the caller. When there is no
caller, it is never paid. Several central results here have no caller.

This document lists every such gap, states an exact acceptance criterion for
each, and records which docstrings currently claim more than the code proves.

---

## The structural finding

**`mei_theorem4`, `mei_theorem6`, and all seven theorems in `AKM.lean` never
mention the MDP.** They quantify over an abstract `f f' : ℝ → ℝ`.

```
AKM.lean  — abstract: ascent_step, quad_decrease_of_domination, domination_rate,
            approx_domination_floor, ascent_monotone, subopt_antitone,
            ascent_converges
Mei.lean  — abstract: mei_theorem4, geometric_decay, geometric_tendsto_zero,
            entropy_value_converges, mei_theorem6
Rate.lean — abstract: all three
```

In `mei_theorem4` the discount `γ` is a free real constrained only by `0 ≤ γ < 1`.
Nothing forces `f` to be a value function. **The theorem is instantiable at
`f = 0`.** It is a true and non-trivial theorem about real sequences; it is not
Mei's Theorem 4.

Two facts make this decisive:

1. **`smoothAt_V_final` has zero callers.** `grep -rn smoothAt_V_final` returns
   its own definition and three *doc-comment* mentions in `Mei.lean`. Every
   `SmoothAt` hypothesis in `AKM.lean` and `Mei.lean` is discharged by the
   caller, never by `smoothAt_V_final`. The bridge is prose.
2. **No concrete softmax `DiffPolicy`/`C2Policy` is ever constructed.** `PF` is an
   abstract `variable` in every file. `softmaxPolicy` returns a bare
   `ℝ → Policy S A` and is never fed to any smoothness theorem. So even
   `smoothAt_V_final` is not about the softmax value function — it is about an
   arbitrary `C2Policy` satisfying assumed bounds.

---

## What *is* genuinely proved

Stated first, because the gaps below are not the whole picture.

| Result | Location | Note |
|---|---|---|
| `policy_gradient` | `Theorem.lean` | unconditional, about `V M` |
| `performance_difference` | `PerformanceDifference.lean` | unconditional |
| Infinite-horizon development (`Vinf`, `dinf`, `Vinf_bellman`, `policy_gradient_infinite`) | `Infinite.lean`, `InfiniteGradient.lean` | real |
| The `1/t` induction | `Rate.lean` | **fully clean, no gaps**; no paper writes it out |
| Ascent lemma and consequences | `AKM.lean` | correct from `SmoothAt` |
| Sharp `\|f''\| ≤ β ⟹ SmoothAt f f' β` | `SecondDeriv.lean:350` | non-trivial, sharp constant |
| `8/(1-γ)³` second-derivative bound | `SecondDeriv.lean:225` | the paper's exact constant |
| Optimality certificates | `GradientDomination.lean` | correct |

`Rate.lean` and `GradientDomination.lean` have **no load-bearing gaps**.
`smoothAt_V_final` is the strongest MDP-level result in the repo — and is unused.

---

## G1 — Mei Lemma 8: the non-uniform Łojasiewicz inequality

**Severity: critical. This is the paper's central technical contribution.**

`mei_theorem4` (`Mei.lean:174`) assumes

```lean
(hloja : ∀ t, c * (fstar - f (x t)) ≤ |f' (x t)|)
```

There is **no theorem anywhere in the repo lower-bounding `|dV|`.** Confirmed by
grep: nothing concludes a lower bound on a gradient.

`loja_pointwise` (`Mei.lean:96`) is not this lemma and does not approach it. It
is a one-line `mul_le_mul_of_nonneg_right` stating
`min_s π(a*|s) · A ≤ π(a*|s) · A` — a triviality about `⨅`, **with no gradient in
it at all**. It involves no `√|S|` and no distribution-mismatch coefficient. Its
docstring calls it "the Łojasiewicz mechanism", which oversells a monotonicity
fact. The distance from `loja_pointwise` to `hloja` is the entirety of Lemma 8.

**Acceptance criterion.** A theorem whose statement mentions `V M`, a softmax
`C2Policy`, and a gradient, of the shape

```lean
theorem mei_lemma8 (M : FiniteMDP S A) (θ : E) (astar : S → A) ... :
    (lojaCoeff (softmaxPolicy logits θ) astar / Real.sqrt (Fintype.card S))
      * (1 / mismatchCoeff ...) * (Vstar M μ - Vinf M (softmaxPolicy logits θ) μ)
    ≤ ‖gradV M PF θ μ‖
```

Required: real `‖·‖` on the parameter space (blocked by **G5**); `mismatchCoeff`
defined (see **G4**); the softmax gradient in closed form (blocked by **G6**).
Not accepted: any restatement not mentioning a gradient of `V`.

---

## G2 — AKM Lemma 4.1: gradient domination

**Severity: critical.**

`domination_rate` (`AKM.lean:104`) assumes

```lean
(hdom : ∀ t, c * (fstar - f (x t)) ≤ |f' (x t)|)
```

**`GradientDomination.lean` contains no gradient-domination inequality.** Despite
the filename it proves `suboptimality_eq` (a restatement of
`performance_difference`) and a chain of *sign* lemmas — the
"advantage ≤ 0 ⟹ optimal" direction. AKM Lemma 4.1 — suboptimality bounded by a
distribution-mismatch-weighted gradient norm — is absent. The filename promises
content the file does not deliver.

**Acceptance criterion.** A theorem mentioning `V M` and a gradient, of the shape
`suboptimality ≤ mismatch · ‖∇V‖`, plus `GradientDomination.lean` either
containing it or being renamed (`OptimalityCertificates.lean`).

---

## G3 — `hlt`: strict suboptimality at every iterate

**Severity: moderate. Easy to miss.**

`mei_theorem4` and `domination_rate` assume `∀ t, f (x t) < fstar` — strict
suboptimality at *every* iterate, forever. It is **false if the algorithm ever
reaches the optimum exactly**, and nothing in the repo proves `V < V*` along a
trajectory.

It is load-bearing: `domination_rate` needs `0 < δ t` for the reciprocal
recursion (`AKM.lean:112`).

**Acceptance criterion.** Either prove it for softmax (true: softmax never
attains a deterministic optimum, so `Vinf < Vstar` strictly unless the MDP is
degenerate — needs a non-degeneracy side condition), or restructure the rate
theorems to conclude `min (fstar - f (x T)) 0` / handle the `δ t = 0` case by
early termination. The second is more honest and less work.

---

## G4 — AKM Section 6: transfer error and concentrability are undefined

**Severity: high — this is a docstring asserting content that does not exist.**

`approx_domination_floor` (`AKM.lean:144`) assumes
`(hdom : c * (fstar - f x) - ε ≤ |f' x|)` and its docstring says the `ε/c` floor
"is where the function-approximation error and the distribution-mismatch
coefficient enter."

**Neither transfer error nor concentrability is defined anywhere in the repo.**
Grep finds only prose. This is a paraphrase of AKM Section 6 with all its actual
content absent.

**Acceptance criterion.** Definitions of the concentrability coefficient
`‖d^{π*}_ρ / μ‖_∞` and the transfer error `L(θ; ...)`, plus a theorem bounding
suboptimality by optimization error + transfer error × concentrability. Until
then the docstring must be corrected to say the constants are *not* modelled.

---

## G5 — The parameter is a scalar, not a vector

**Severity: critical, and blocks G1, G2, G4, G6.**

```lean
structure DiffPolicy (S A : Type*) [Fintype A] where
  toPolicy : ℝ → Policy S A
  dπ : ℝ → S → A → ℝ
  hasDeriv : ∀ θ s a, HasDerivAt (fun t => (toPolicy t s) a) (dπ θ s a) θ
```

Both papers optimize over `θ ∈ ℝ^(S×A)`. A one-dimensional parameter cannot
express per-state-action softmax logits, and "gradient norm" degenerates to
`|f'|` — so **G1 and G2 cannot even be stated** in the current setting.

**Acceptance criterion.** `toPolicy : E → Policy S A` for
`E := EuclideanSpace ℝ (S × A)` (or `(S × A) → ℝ` with `PiLp 2`), `HasDerivAt`
→ `HasFDerivAt`, and `SmoothAt` restated with `‖·‖`. Touches every file. This is
the largest single change and should be done first.

---

## G6 — No softmax `DiffPolicy` instance

**Severity: high. Small and closable; blocks G1 and G7.**

`softmaxPolicy` (`Softmax.lean:93`) returns `ℝ → Policy S A`. **The
differentiability proof was never written.** So softmax — the subject of both
papers — is never differentiated. `Softmax.lean:87` claims it "packages a
`DiffPolicy`"; it does not.

Consequence: `sum_abs_score_le_one` proves `∑ₐ |softmaxScore w a b| ≤ 1`, but the
`hscore` hypothesis of `smoothAt_V_final` is about the abstract field `PF.dπ`.
**The proved lemma and the required hypothesis have no Lean-level connection.**

**Acceptance criterion.** A `def softmaxC2Policy (logits : E → S → A → ℝ) ... :
C2Policy S A` with `hasDeriv`/`hasDeriv2` proved and a theorem
`softmaxC2Policy.dπ = softmaxScore ...`. Then `hscore` discharges by
`sum_abs_score_le_one`.

---

## G7 — `hdloc` is never discharged

**Severity: moderate. Provable once G6 lands.**

`smoothAt_V_final` (`SecondDeriv.lean:591`) assumes

```lean
(hdloc : ∀ (t : ℝ) (j : ℕ) (s' : S), |dLocalTerm M PF t j s'| ≤ 3 / (1 - M.γ))
```

`dLocalTerm` is concrete (`SecondDeriv.lean:282`), so this is provable in
principle — but it needs a bound on `d2π` that the abstract `C2Policy` structure
does not carry. **No theorem in the repo proves it.** Its docstring says inputs
are "the paper's standing assumptions plus the bound on the local-term
derivative"; that "plus" is doing heavy lifting.

**Acceptance criterion.** `theorem abs_dLocalTerm_le_softmax ... :
|dLocalTerm M (softmaxC2Policy logits) θ j s| ≤ 3 / (1 - M.γ)`, and
`smoothAt_V_final` restated without `hdloc`.

---

## G8 — Wrong horizon

**Severity: high.**

All rate results use finite-horizon `V`. **Both papers are infinite-horizon.**
`Vinf` appears nowhere in `AKM.lean`, `Mei.lean`, or `SecondDeriv.lean`.

The infinite-horizon development exists (`Infinite.lean`,
`InfiniteGradient.lean`) but is disconnected from the rate track.

**Acceptance criterion.** `smoothAt_Vinf_final` about `Vinf`, and the final rate
theorems stated for `Vinf`. Uniform-in-`m` bounds plus `tendsto_V_Vinf` should
transfer the smoothness constant, since `8/(1-γ)³` is already horizon-uniform.

---

## G9 — Mei Lemma 9 (`c > 0`): hypothesis is faithful, docstring is not

**Severity: low as a gap, high as an overclaim.**

Carrying `hc : 0 < c` matches the paper — Mei's statement reads "`c` the positive
constant from Lemma 9", and their Lemma 9 is proved by citing AKM Theorem 5.1
rather than from first principles. **The hypothesis is defensible.**

The docstring is not. `Mei.lean:23–32` claims:

> We have that content (`ascent_converges`, `optimal_of_greedy`), so Theorem 4 is
> reachable here in a way it is not from Mei alone.

**That bridge does not exist in Lean.** `ascent_converges` yields only
`∃ L ≤ fstar` with `Tendsto`. It never identifies `L = fstar`, never shows the
limit policy is greedy, and is never composed with `optimal_of_greedy`.

**Acceptance criterion.** Either compose them into
`theorem c_pos ... : 0 < lojaCoeff ...`, or delete the claim. Deleting is
correct until the composition exists.

---

## G10 — `mei_theorem6` does not state the entropy result

**Severity: high.**

```lean
theorem mei_theorem6 {K : ℝ} (hK₀ : 0 ≤ 1 - K) (hK₁ : 1 - K < 1)
    (δ : ℕ → ℝ) (hnn : ∀ t, 0 ≤ δ t)
    (hstep : ∀ t, δ (t + 1) ≤ (1 - K) * δ t) : ...
```

No `f`, no `V`, no MDP, **no entropy, no `τ`, no policy** — just an abstract real
sequence. `hstep` *is* Mei Theorem 6: everything the paper proves exists to
establish that contraction — Lemma 14 (entropy smoothness `(4+8logA)/(1-γ)³`,
which the authors call "a somewhat lengthy calculation"), Lemma 15 (entropy
Łojasiewicz with exponent 1/2, needing the soft greedy policy and a Pinsker-type
argument), Lemma 16. What remains and is proved is a three-line induction.

`entropy_value_converges` is `ascent_converges` verbatim. Labeled "Mei Lemma 16,
the self-contained part" — but it proves only that *a* limit exists, not Lemma
16's claim that `c > 0`.

**Acceptance criterion.** Define the entropy-regularized objective
`Vsoft = Vinf + τ·H`, prove Lemma 14 and Lemma 15, derive `hstep`. This is the
largest item after G5. Until then, rename to `geometric_rate` — the current name
attributes a paper theorem to a fact about geometric sequences.

---

## Docstrings that currently overclaim

Independent of the proof work, these assert connections the code does not make
and should be corrected first.

| Location | Claim | Reality |
|---|---|---|
| `SecondDeriv.lean:588` | "This is what `ascent_step` and `domination_rate` consume, so AKM Theorem 4.1 is instantiable for a concrete MDP." | Zero callers; no concrete MDP or softmax family anywhere. |
| `Mei.lean:26` | "We have that content ... so Theorem 4 is reachable here" | Composition does not exist (**G9**). |
| `Mei.lean:88` | `loja_pointwise` = "The Łojasiewicz mechanism" | One-line monotonicity, no gradient (**G1**). |
| `AKM.lean:142` | "the `ε/c` floor is where the function-approximation error and the distribution-mismatch coefficient enter" | Neither is defined (**G4**). |
| `Softmax.lean:87` | "packages a `DiffPolicy`" | Returns a bare `Policy` (**G6**). |
| `Mei.lean:16` | Lemma 7 "Already proved as `smoothAt_V_final`" | True, but with `hdloc`/`hscore` undischarged and never applied. |
| `README.md` | claims both papers formalized | Overstated on the rate results. |

---

## Ordering

```
G5 (vector parameter)  ──┬──> G6 (softmax instance) ──> G7 (hdloc)
                         │                          └──> G1 (Lemma 8) ──> G2
                         └──> G8 (infinite horizon)
G4, G10 independent, large.   G3, G9 small.
```

G5 first: G1 and G2 cannot be *stated* without it. G6 is small and unblocks the
two cheapest closures (G7, and the `hscore` link). G1 and G10 are the real
mathematics.

---

## Why the audit was needed, and why it should not have been

Every gap above was found by reading proofs and grepping for callers — not by
anything the build reports. `lake build` is green, `sorry` count is zero,
`#print axioms` is clean. The signal that would have caught all of this is
**"which theorems mention `FiniteMDP`, and which of those are ever applied?"**,
and nothing computes it.

See `STRUCTURE.md` for the proposed fix: making the gaps fall out of the build
rather than out of an audit.
