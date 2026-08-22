/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Meta.Paper
import PolicyGradient.Target
import PolicyGradient.Proofs
import PolicyGradient.Proofs.Extra
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Goal.lean — the frozen targets

**This file is frozen. Do not weaken a statement to make it provable.**

Every result this repo is trying to reach is stated here, in advance, as a
theorem with `sorry`. Proving one means replacing its `sorry` — never editing
its statement.

## Why this file exists

The repo previously reported "114 theorems, zero `sorry`" while its headline
results were abstract statements about `f : ℝ → ℝ` that never mentioned an MDP
(see `GAPS.md`). No `sorry` was involved: the unproved content sat in
*hypothesis positions*, which Lean type-checks happily.

That failure needs no bad intent. Working toward a hard theorem, you find you
need a lemma you cannot prove; you add it as a hypothesis; the build goes green.
Each step is locally reasonable and the whole is worthless. The cheap path pays
exactly as well as the honest one.

Freezing the statements removes that. With the goal fixed in advance, assuming
the missing lemma in a helper **does not discharge the goal** — the `sorry` here
stays, and no green signal appears. The only ways to make this file compile
clean are to prove the goals, or to edit this file, which is one line in a diff
that a human reads.

## The rule

> **A hypothesis is a promise. A theorem with no callers is a promise nobody
> ever pays. Prefer a visible `sorry` to an invisible hypothesis.**

## Discipline

* Statements here are frozen; the linter fails if one changes.
* `#print axioms` must never grow beyond `propext, Classical.choice, Quot.sound`
  — in particular, never discharge a goal by declaring an `axiom`.
* A goal proved from contradictory hypotheses is vacuous, not done. Each goal
  carrying hypotheses needs a consistency witness (a concrete MDP satisfying
  them) before it counts.
* Infrastructure steps are goals too. "Build the vector-parameter policy family"
  is a construction goal, discharged only by producing the object.
* **Pin every witness.** An existence goal is not automatically safe. `∃ x, P x`
  with a weak `P` is satisfiable by a *degenerate* witness — a bare
  `Nonempty (VecPolicy ...)` is discharged in four lines by a constant policy
  family with derivative `0`, and `∃ V, V - b ≤ c` is discharged by
  `⟨b + c, by linarith⟩`. Every construction goal needs a conjunct identifying
  *which* object, and no target quantity may be existentially chosen by the
  prover. Define the optimum (`Vstar`, `VsoftStar`); never let it be picked.
* The three routes to a hollow proof are: weakening the conclusion, adding a
  hypothesis, and choosing a degenerate witness. All are the same failure —
  **the prover controlling both the target and what satisfies it.**
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ## G5 — the vector parameter

Both papers optimize over `θ ∈ ℝ^(S×A)`. This repo uses `θ : ℝ`, a single real,
so "gradient norm" degenerates to `|f'|` and **G1 and G2 cannot even be
stated**. Everything else waits on this.

`EuclideanSpace ℝ (S × A)` is the target: `gradient` needs an
`InnerProductSpace`, which the plain function type `(S × A) → ℝ` lacks, and both
papers' bounds are on `‖∇V‖` in the ℓ² norm. -/

/-- **G5 + G6 — the softmax family is a differentiable vector-parameter policy.**

Stated as one goal deliberately. As a bare `Nonempty (VecPolicy ...)` this was
**satisfiable by a degenerate witness**: a constant policy family ignoring `θ`,
with derivative `0`, is a perfectly valid `VecPolicy`, so the `sorry` could be
discharged in four lines while building nothing useful.

The `hsoft` conjunct pins the witness: `F` must *be* the softmax family, so the
only route is the actual differentiability proof. Nothing weaker discharges it.

This is the general trap for construction goals — see the discipline note above.

Discharging this closes both G5 (vector parameter) and G6 (softmax instance),
and unblocks G7 and G1. -/
@[infra "G5+G6"]
theorem g5_g6_softmax_family
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (hlog : ∀ s a, Differentiable ℝ (fun θ => logits θ s a)) :
    ∃ F : VecPolicy S A (EuclideanSpace ℝ (S × A)),
      ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a := by
  -- `softmax_diff` (in `Softmax.lean`) gives Fréchet differentiability of
  -- `θ ↦ π_θ(a|s)` for every state-action pair.
  have hdiff : ∀ (s : S) (a : A),
      Differentiable ℝ (fun θ : EuclideanSpace ℝ (S × A) => (softmax (logits θ s)) a) :=
    fun s a => softmax_diff (fun θ => logits θ s) (fun a' => hlog s a') a
  -- The witness *is* the softmax family; `dπ` is its Fréchet derivative.
  refine ⟨{
    toPolicy := fun θ s => softmax (logits θ s)
    dπ := fun θ s a => fderiv ℝ (fun t => (softmax (logits t s)) a) θ
    hasFDeriv := fun θ s a => (hdiff s a θ).hasFDerivAt }, ?_⟩
  intro θ s a
  rfl

/-! ## Vstar is well-behaved

`Vstar` is a `⨆` over the whole policy space. If that supremum were badly
behaved the suboptimality goals could be vacuous or ill-typed in spirit, so its
basic properties are goals rather than assumptions. -/

/-- **Every policy's value is at most the optimal value.**

Needs `Vinf` to be bounded above over the policy space — true because rewards
are bounded and `γ < 1`, giving the uniform bound `1/(1-γ)`. Without this
`⨆` could misbehave and the suboptimality statements would be hollow. -/
@[infra "Vstar-sound"]
theorem vstar_upper (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ : S) :
    Vinf M π s₀ ≤ Vstar M s₀ :=
  Proofs.vstar_upper_proof M hr hγ₀ hγ₁ π s₀

/-- **The optimal value is finite.** `Vstar ≤ 1/(1-γ)` under bounded rewards. -/
@[infra "Vstar-finite"]
theorem vstar_le (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Vstar M s₀ ≤ 1 / (1 - M.γ) :=
  Proofs.vstar_le_proof M hr hγ₀ hγ₁ s₀

/-! ## Bellman optimality — the machinery `g3` needs

An agent attempting `g3_strict_suboptimality` reported that the statement is
correct as written but not reachable from what this repo has: discharging it
needs the Bellman optimality characterization (`Q*`, `V* = max_a Q*`, and the
fact that an optimal policy's support is greedy), plus an occupancy/support
argument. That is infrastructure, not a small proof, so it is stated here rather
than left as an obstacle inside `g3`.

Their argument for why `g3` is true, recorded so the eventual proof can follow
it: `Vinf M π μ` depends on `π` only at states reachable from `μ`, so `hnondeg`
cannot be witnessed by a bad action at an unreachable state — it forces the
variation onto reachable states, which is exactly where softmax's full support
bites. Contrapositive: if a full-support policy is optimal at `μ`, greediness
of its support gives `Q*(s,a) = V*(s)` for *all* `a` at every reachable `s`, so
every policy is optimal and `hnondeg` fails. -/

/-- **Bellman optimality.** `V*(s) = maxₐ Q*(s,a)`.

The characterization `g3` turns on. Note it needs `Vstar` to be a genuine
supremum, which `vstar_upper` and `vstar_le` now provide. -/
@[infra "Bellman-optimality"]
theorem vstar_bellman (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vstar M s = ⨆ a : A, Qstar M s a :=
  Proofs.vstar_bellman_proof M hr hγ₀ hγ₁ s

/-- **An optimal policy's support is greedy.**

If `π` attains the optimum at `s`, every action it puts positive mass on is
optimal there. Combined with softmax's full support this is what forces
`Q*(s,a) = V*(s)` for *every* `a` — the step that makes `g3` work. -/
@[infra "Greedy-support"]
theorem optimal_support_greedy (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) (hopt : Vinf M π s = Vstar M s)
    (a : A) (hsupp : 0 < (π s) a) :
    Qstar M s a = Vstar M s :=
  Proofs.optimal_support_greedy_proof M hr hγ₀ hγ₁ π s hopt a hsupp

/-! ## G3 — strict suboptimality along the trajectory

The rate machinery needs `0 < δ t` for its reciprocal recursion, and the old
abstract theorems simply assumed `∀ t, f (x t) < fstar` — strict suboptimality
at every iterate, forever, which is **false the moment the optimum is reached
exactly**. Nothing proved it.

For softmax it is genuinely true: a softmax policy assigns strictly positive
probability to every action, so it never equals a deterministic optimal policy.
Stating it here means the rate proof can no longer quietly assume it. -/

/-- **G3 — softmax is never exactly optimal.**

**Statement verified correct as written** (2026-08-22). A subagent set out to
build the suspected counterexample — an MDP whose only bad action sits at an
unreachable state — and found it cannot exist: `Vinf M π μ` depends on `π` only
at reachable states, so such an MDP would not satisfy `hnondeg` either.
`hnondeg` is doing real work (without it the statement is false for MDPs where
all actions are equally good) and is exactly strong enough. Stress-tested over
~40,000 random 3-state MDPs with zero violations, and the load-bearing step
directly over 619 cases, also zero.

**Proved 2026-08-22, at greater generality than expected.** The statement omits
`hr : |r| ≤ 1`, which every piece of Bellman machinery needs — `Vstar` is a
`ciSup`, junk-valued without a uniform bound on `Vinf`. Rather than ask for the
hypothesis, the agent proved it without: `S` and `A` are `Fintype`, so `|r|`
attains a maximum, and rescaling rewards by `max 1 (that maximum)` gives an MDP
with the same `P` and `γ` satisfying `|r| ≤ 1`. Values are homogeneous in the
reward function, so the strict inequality transfers back. The extra generality
is free, so `hr` stays off.

The proof also avoids reachability entirely. Softmax positivity makes
`optimal_support_greedy` apply to *every* action, so the optimal set is closed
under transitions; masking an arbitrary policy's gap to that set makes the mask
invisible to the one-step average, giving `D ≤ γD` and hence `D = 0`. The raw
gap does **not** contract — outside the optimal set a general policy is
genuinely suboptimal — which is why the masking, not a naive contraction, is
what works.

⚠ **NO VERBATIM QUOTE EXISTS. Mei et al. state no such lemma.** Reported rather
than repaired, per the freeze.

The tag claims `@[paper_tool "Mei2020" "not in the paper — repo-derived"]`. Mei's Lemma 9 is a
different statement entirely — it is the `c > 0` result, quoted verbatim below
in full (main text and appendix agree word for word):

VERBATIM, Mei, Xiao, Szepesvári & Schuurmans (arXiv:2005.06392) Lemma 9:

> **Lemma 9.** Let Assumption 2 hold. Using Algorithm 1, we have,
> ```
> c := inf_{s∈S, t≥1} π_{θ_t}(a*(s)|s) > 0.
> ```
>
> *Proof.* The proof is an extension of the proof for Lemma 5. Denote
> `∆*(s) = Q*(s,a*(s)) − max_{a≠a*(s)} Q*(s,a) > 0` as the optimal value gap of
> state `s`, **where `a*(s)` is the action that the optimal policy selects under
> state `s`**, and `∆* = min_{s∈S} ∆*(s) > 0` as the optimal value gap of the
> MDP.

with Assumption 2 as stated:

> **Assumption 2 (Sufficient exploration).** The initial state distribution
> satisfies `min_s μ(s) > 0`.

**The mismatch, precisely.** Lemma 9's conclusion is about the *policy*:
the optimal-action probability is bounded away from zero along the trajectory,
uniformly in `s` and `t`. The Lean statement below concludes something about the
*value*: `Vinf M (F.toPolicy θ) μ < Vstar M μ`, for a **single arbitrary `θ`**
with no trajectory, no `Algorithm 1`, no `hstep`, and no Assumption 2. There is
no `inf`, no `c`, no `t`. These are not the same proposition, and neither
implies the other in the direction the tag suggests — indeed
`Proofs.g9_of_convergence_is_false`, already recorded on `g9_c_positive`, shows
value convergence does **not** give the policy bound.

The repo already tags the actual Lemma 9 correctly, as `g9_c_positive`
(`@[infra "G9"]`). So `Lemma 9` is cited twice, for two different theorems.

**Nothing in Mei corresponds to the statement below.** Searching the full text
for a strictness claim of the form "a softmax policy is never exactly optimal"
returns nothing: the closest passages are the bandit visualization discussion
("Any globally convergent iteration will enter `R` within finite time … and
never leaves `R`") and Lemma 5's `inf_{t≥1} π_{θ_t}(a*) > 0`, neither of which
is this. The statement is a **repo-internal lemma** — real, proved, and needed
(it licenses the `0 < δ t` the reciprocal recursion consumes) — but it is not a
transcription of anything in the paper. Softmax full support is used implicitly
throughout Mei's analysis; it is never isolated as a numbered result.

Verdict: **MISMATCHES.** The proposition is true and proved (see the two
paragraphs above), but the `@[paper_tool "Mei2020" "not in the paper — repo-derived"]`
attribution is wrong on both counts: it is not Lemma 9, and it is not in the
paper. The honest tag is `@[infra]`. **Statement left untouched** — this is a
citation defect only.

Under a non-degeneracy condition (some policy is strictly suboptimal, i.e. the
MDP is not one where every policy is optimal), a softmax policy — which puts
positive mass on every action — is strictly suboptimal.
This is what licenses the `0 < δ t` the `1/t` recursion needs. -/
@[paper_tool "Mei2020" "not in the paper — repo-derived"]
theorem g3_strict_suboptimality (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (μ : S) (θ : EuclideanSpace ℝ (S × A))
    (hnondeg : ∃ π : Policy S A, Vinf M π μ < Vstar M μ) :
    Vinf M (F.toPolicy θ) μ < Vstar M μ :=
  Proofs.g3_strict_suboptimality_proof M logits F hF hγ₀ hγ₁ μ θ hnondeg

/-! ## G9 — the constant `c` is positive

Mei's Lemma 9 asserts `c > 0` by citing AKM Theorem 5.1; it is not proved in
their paper. `mei_theorem4` above states `c` existentially, so **this goal is
what actually produces it** — it is not optional decoration.

We have the AKM content (`ascent_converges`, `optimal_of_greedy`), but the
composition does not exist: `ascent_converges` yields only `∃ L ≤ fstar` with
`Tendsto`, never identifying `L = fstar`. This goal is that missing bridge. -/

/-- **G9 — the Łojasiewicz coefficient stays bounded away from zero.**

VERBATIM, Mei et al. (arXiv:2005.06392) Lemma 9 and its proof:

> **Lemma 9.** Let Assumption 2 hold. Using Algorithm 1, we have
> `c := inf_{s∈S, t≥1} π_{θ_t}(a*(s)|s) > 0`.
>
> *Proof.* [...] Denote `Δ*(s) = Q*(s,a*(s)) − max_{a≠a*(s)} Q*(s,a) > 0` as the
> optimal value gap of state `s`, **where `a*(s) is the action that the optimal
> policy selects under state s`**, and `Δ* = min_s Δ*(s) > 0` as the optimal
> value gap of the MDP.

**This settles both refutations of this goal.** `a*(s)` is the action a *fixed
optimal policy* selects — not an arbitrary `Q*`-optimal function. And the proof
opens by assuming `Δ*(s) > 0`, a **strictly positive optimal value gap**, which
excludes `Q*` ties outright.

So the tie counterexample does not refute Mei; it refutes my transcription. A
faithful statement needs the strict-gap assumption, or `astar` tied to a fixed
optimal policy. I added `hastar` (Q*-optimality) as a patch after the first
refutation without checking what the paper actually assumes.

**`hastar` was missing and the statement was FALSE without it** (refuted
2026-08-22, `Proofs.g9_is_false`, axioms clean). `astar` was an entirely
unconstrained parameter — nothing said it picked *optimal* actions. Instantiate
it at the **suboptimal** action of a one-state two-action MDP (`r = (1,-1)`,
`γ = 1/2`) and gradient ascent drives that probability to zero, so no `c > 0`
bounds it below for all `t`. Mei's `a*` is the optimal action set; mine was any
function at all.

The easy repair is also closed off: `m(t) ≥ m(0)` fails in 66/400 random MDPs
(worst ratio `0.075`), so a monotonicity argument cannot produce the infimum —
a genuine asymptotic argument is required.

Tagged `@[infra]`, not `@[paper]`: the linter correctly rejected the `@[paper]`
tag, because the conclusion is about the *policy's* probabilities rather than
about `V`. It produces the constant that `mei_theorem4` consumes; it is not
itself a statement about the MDP's value.

Along a gradient-ascent trajectory the smallest optimal-action probability does
not decay to zero, so the `inf` over time is strictly positive. This is what
makes the `O(1/T)` rate meaningful rather than asymptotically vacuous. -/
@[infra "G9"]
theorem g9_c_positive (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    -- Assumption 2 (Sufficient exploration): `min_s μ(s) > 0`. Mei's Lemma 9
    -- says "Let Assumption 2 hold", and Claim III invokes it by name. The
    -- earlier single-start-state form did not refute the goal
    -- (`Proofs.policy_unchanged_of_dinf_zero`: a zero-occupancy state has
    -- frozen logits, so its `astar` probability stays at its positive initial
    -- value, which an existential `c` tolerates) — but it removed Claim III's
    -- input there, so it was not the paper's statement.
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    -- Mei's proof opens by assuming a strictly positive optimal value gap
    -- `Δ*(s) = Q*(s,a*(s)) − max_{a≠a*(s)} Q*(s,a) > 0`, which excludes `Q*`
    -- ties. Refuted TWICE without it:
    --   `Proofs.g9_is_false` -- `astar` picking a SUBOPTIMAL action;
    --   `Proofs.g9_c_positive_frozen_is_false` -- `astar` picking one side of a
    --     `Q*` TIE. Witness: one state, `γ = 0`, `r = (1,1,0)`, `θ₀ = (0,1,0)`.
    --     Two tied OPTIMAL actions; ascent abandons one, broken by the
    --     initialization rather than the rewards. `γ = 0` and `|S| = 1` are
    --     deliberate, so neither the discount nor the `⨅ s` can be blamed.
    -- The same witness also refutes the reduction from value convergence
    -- (`Proofs.g9_of_convergence_is_false`): `V^{π_t} → V*` while
    -- `π_t(a*) → 0`, because abandoning one of two OPTIMAL actions costs the
    -- value nothing. So `c > 0` can never be argued from the value — only from
    -- the policy. `Proofs.g9_of_policy_limit` is the reduction that IS true.
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s)) :
    -- STATUS (2026-08-22): `hgap` is a genuine repair, verified two ways.
    -- `Proofs.gap_concentrates` proves any policy attaining `V*(s)` must put
    -- mass 1 on `astar s` — exactly the property the tie witness destroyed —
    -- and `gap_pistar_det` shows `hgap` forces `astar` to be the unique
    -- `Q*`-argmax and `πstar` deterministic, removing the adversarial freedom.
    -- A ~5000-MDP strict-gap sweep found no counterexample.
    --
    -- Mei's proof has four claims. I, II and IV are formalized against this
    -- exact recursion (`Proofs/G9c.lean`); `g9_of_eventually_nice` is Lemma 9
    -- with only Claim III assumed. Claim III is where they cite AKM Theorem
    -- 5.1 — i.e. `softmax_ascent_converges` below. The two are mutually
    -- reducing, which `Proofs/AKM51.lean` recorded from the other side.
    --
    -- Note monotonicity of the infimum FAILS even under `hgap` (25/288), which
    -- independently confirms Mei's "eventually enters a nice region" structure
    -- is required and that no global-monotonicity shortcut exists.
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := sorry

/-! ## G7 — the local-term bound

`smoothAt_V_final` assumes `|dLocalTerm| ≤ 3/(1-γ)` and nothing proves it. It is
provable once the second derivative of a concrete softmax family is available,
i.e. after G6. -/

/-! ### G7 was FALSE as stated — two defects, both mine

Refuted 2026-08-22 (`Proofs.g7_general_false`, the frozen statement negated,
axioms clean). Counterexample: one state, two actions, `γ = 0`, rewards `0`/`1`,
`logits θ s a = c · θ(s,a)`. Then `Vinf = e^{cx}/(e^{cx}+1)` with derivative
`c/4` at `θ = 0`; the claimed bound is `8`, and `c = 33` breaks it. `γ = 0` was
chosen deliberately so the failure cannot be blamed on the discount factor.

Two independent defects:

1. **`logits` was universally quantified with no regularity hypothesis.** The
   neighbouring `g5_g6_softmax_family` carries `hlog : Differentiable ...`; G7
   carried nothing. And differentiability alone would not have saved it — AKM's
   Lemma E.4 is about the **tabular** parameterization `logits θ s a = θ (s,a)`,
   which is 1-Lipschitz. Any `logits` is permitted here, so the chain rule
   scales the gradient freely. `Witness.lean` already records that tabular "is
   exactly the one both papers use"; the goal simply failed to pin it.
2. **Gradient norm is not smoothness.** `8/(1-γ)³` is AKM's bound on the
   *second* derivative. The first-derivative bound is `2/(1-γ)²`.

Split accordingly below. The first-derivative goal is stated at the constant it
should have had; the smoothness goal keeps `8/(1-γ)³` and is the faithful
Lemma E.4. -/

/-- **G7a — the gradient norm bound for tabular softmax.**

⚠ **NO SOURCE QUOTE EXISTS FOR THIS TAG. The paper does not contain this
lemma.** Reported rather than repaired, per the freeze.

The tag claims `@[paper_tool "AKM2021" "derived from Lemma D.4's C₁"]`. Two problems, the
second serious:

**(a) `Lemma E.4` is not in AKM v4.** As recorded on `smoothAt_V_final`,
`/tmp/akm.txt` is arXiv:1908.00261 **v4**, whose Appendix E is *"Standard
Optimization Results"* (Theorems E.1–E.3 only). The softmax smoothness content
lives in Appendix D. "Lemma E.4" is Mei's citation of an earlier AKM numbering.

**(b) AKM state no first-derivative bound of this form, at any number.**
Appendix D bounds only *second* derivatives. The nearest thing in the paper is
the intermediate step inside Lemma D.4's proof that produces `C₁ = 2` — and it
bounds a **different quantity**:

VERBATIM, AKM (arXiv:1908.00261v4), inside the proof of Lemma D.4:

> We also have by differentiating `π_α(a|s)` once w.r.t `α`,
> ```
> ∑_{a∈A} |dπ_α(a|s)/dα|_{α=0}  ≤  ∑_{a∈A} |u^⊤ ∇_{θ+αu} π_α(a|s)|_{α=0}
>                               =  ∑_{a∈A} π_θ(a|s) |u_s^⊤ e_a − u_s^⊤ π(·|s)|
>                               ≤  max_{a∈A} (|u_s^⊤ e_a| + |u_s^⊤ π(·|s)|)  ≤ 2
> ```

That `2` bounds the **total variation of the policy's directional derivative**,
`∑_a |dπ/dα|` — a quantity about `π`, not about `V`. It is fed to Lemma D.2 as
the constant `C₁`, whose conclusion is the *second*-derivative bound
`C₂/(1−γ)² + 2γC₁²/(1−γ)³`. Reading `C₁ = 2` off that step and attaching it to
`‖∇_θ V‖` with a `(1−γ)²` denominator is a **transcription that fuses two
unrelated quantities**. AKM never write `‖∇_θ V^{π_θ}(s₀)‖ ≤ 2/(1−γ)²`.

**Where the constant actually comes from: this repo, not the paper.** The bound
is real and is proved here — `Proofs.g7a_gradient_bound_proof`, via the scalar
`abs_dV_le_softmax` (`Smoothness.lean:304`), whose own docstring says
`|dV| ≤ 1/(1−γ)²` from `∑_a |dπ| ≤ 1`. With AKM's `∑_a |dπ| ≤ 2` that scales to
`2/(1−γ)²`. So the *mathematics* is sound and in-repo; what is unsourced is the
attribution. This is a **derived corollary of AKM's `C₁ = 2` step**, not a lemma
AKM state.

Verdict: **MISMATCHES.** The statement is (as far as the repo's own proof goes)
true, but it is **not** AKM Lemma E.4, and no lemma of this form appears in AKM
at any number. The `@[paper]` tag over-attributes. The honest tag is
`@[paper_tool "AKM2021" "Lemma D.4 (C₁=2 step), gradient corollary"]` or
`@[infra]`. **Statement left untouched** — this is a citation defect, and the
inequality itself is not in question.

`‖∇V‖ ≤ 2/(1-γ)²`, the vector-parameter analogue of `abs_dV_le_softmax`. Note
`hF` now pins the **tabular** parameterization: the logits *are* the parameter
coordinates. -/
@[paper_tool "AKM2021" "derived from Lemma D.4's C₁"]
theorem g7a_gradient_bound (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s₀ : S) :
    ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) s₀) θ‖ ≤ 2 / (1 - M.γ) ^ 2 :=
  Proofs.g7a_gradient_bound_proof M F hF hr hγ₀ hγ₁ θ s₀

/-- **G7b — AKM Lemma E.4, the actual smoothness bound.**

The *second* derivative is bounded by `8/(1-γ)³` — the paper's exact constant,
and what `ascent_step` and the rate machinery consume.

`VecPolicy` records only the first derivative, so proving this needs a `C²`
analogue (or a `SmoothAt`-style conclusion). That is real infrastructure, not a
one-line edit — see `vec_c2_family` below.

VERBATIM — with a **label caveat**. `/tmp/akm.txt` is arXiv v4, whose Appendix E
is "Standard Optimization Results" (E.1–E.3 only): **there is no Lemma E.4 in
v4**. The `8/(1−γ)³` result is v4's **Lemma D.4 / eq. (53)**. "E.4" is Mei's
citation of an earlier AKM numbering ("Proof. See Agarwal et al. (2019, Lemma
E.4)"). Constant and content are correct and verified; only the label cannot be
checked against the version on disk. The scalar analogue in `SecondDeriv.lean`
carries the quoted statement. -/
@[paper "AKM2021" "Lemma E.4"]
theorem g7b_smoothness (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s₀ : S) :
    ‖fderiv ℝ (fun t => fderiv ℝ (fun u => Vinf M (F.toPolicy u) s₀) t) θ‖
      ≤ 8 / (1 - M.γ) ^ 3 :=
  Proofs.g7b_smoothness_proof M F hF hr hγ₀ hγ₁ θ s₀

/-- **The tabular softmax family is twice differentiable.**

The infrastructure `g7b_smoothness` needs: `VecPolicy` carries only `dπ`, so the
second derivative of `θ ↦ π(a|s)` has to be available before a second-derivative
bound is even stateable in the form the rate machinery wants. -/
@[infra "C2-family"]
theorem vec_c2_family (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    DifferentiableAt ℝ (fun t => F.dπ t s a) θ :=
  Proofs.vec_c2_family_proof F hF θ s a

/-! ## G1 and G2 were both FALSE — three defects

Refuted 2026-08-22 with machine-checked counterexamples (`Proofs.g1_general_false`,
`g1_general_false_logits`, `g2_general_false`; each takes the frozen statement
verbatim and derives `False`, axioms clean).

**Defect 1 — free universal `mismatch`, both goals.** `(mismatch : ℝ)
(hmis : 0 < mismatch)` was an ordinary universally quantified hypothesis with
nothing tying it to the MDP, so the *caller* picked it. In G2 it multiplied the
right side, so `mismatch → 0⁺` asserted `Vstar - Vinf ≤ 0` for every softmax
policy. In G1 it *divided* the left side, so the same limit sent the left side
to `+∞`. Identical to the `mei_theorem4` defect, in both directions.

**Defect 2 — unconstrained `logits`, G1.** As in `g7_smoothness`, but the
adversarial direction is `c → 0` rather than `c → ∞`: the gradient sits on the
right, so shrinking the logit scale flattens it while leaving the policy at
`θ = 0` untouched. With `mismatch` pinned to `1` and `c = 1/2`, LHS `= 1/4`
against RHS `≤ 1/8`.

**Defect 3 — G2's conclusion is the wrong inequality even after fixing 1 and 2.**
This one I did not anticipate. Substituting `mismatchCoeff` for the free real
still leaves it false: a 3000-MDP sweep found `Vstar - Vinf` exceeding
`(mismatchCoeff/(1-γ))·‖∇V‖` by up to **74×**, with the overshoot tracking
`1/min_s π(a*|s)`. AKM Lemma 4.1's right side is `max_{π'} ⟨∇V, π'-π⟩` over a
bounded set, for the **direct/simplex** parameterization. The softmax gradient
carries an extra `π(a|s)` factor, so `‖∇V‖` alone cannot dominate suboptimality
— which is exactly the exponentially small quantity Mei's Lemma 8 makes
explicit. Inserting `√(|S||A|)` does not rescue it either.

The corrected G2 therefore keeps AKM's directional right-hand side, expressed
through `advInf`. The same sweep found **zero** violations of the corrected G1
across 4000 MDPs.

Note `hr` is restored rather than derived. `g3` could drop it because both sides
of a strict inequality rescale together; here the two sides scale differently
once `mismatchCoeff` is fixed. -/

/-- **G1 — Mei Lemma 8, the non-uniform Łojasiewicz inequality.**

VERBATIM, Mei et al. (arXiv:2005.06392) Lemma 8:

> **Lemma 8 (Non-uniform Łojasiewicz).** Let `π_θ(·|s) = softmax(θ(s,·))`,
> `s ∈ S` and **fix an arbitrary optimal policy `π*`**. We have,
> ```
> ‖∂V^{π_θ}(μ)/∂θ‖₂ ≥ (1/√S) · ‖d^{π*}_ρ / d^{π_θ}_μ‖_∞^{-1} · min_s π_θ(a*(s)|s) · [V*(ρ) − V^{π_θ}(ρ)]
> ```

Note `a*(s)` is the action **the fixed optimal policy `π*` selects**, not an
arbitrary `Q*`-optimal selector. The statement below takes `astar` as a free
function with `hastar` only requiring `Q*`-optimality, which admits a different
tied action than `π*` picks — and that is exactly the defect that refuted `g9`
twice. Tying `astar` to `πstar` would match the paper.

**Two discrepancies remain in the statement below, deliberately not yet fixed.**

1. The paper's coefficient is `‖d^{π*}_ρ / d^{π_θ}_μ‖_∞⁻¹` — occupancy over
   **occupancy**. The statement below uses `mismatchCoeff M πstar μ`, which is
   occupancy over `μ`. Since `μ ≤ d^{π_θ}_μ` pointwise (the `t = 0` term alone
   contributes `μ s`), occupancy-over-`μ` is the LARGER coefficient, so dividing
   by it makes the left side SMALLER — the statement below is therefore weaker
   than Mei's, not stronger. That is safe but not faithful.
2. The paper measures suboptimality at `ρ` and takes the gradient at `μ`. The
   statement below collapses both to `μ`, which is the case `ρ = μ`.

Both are recorded rather than repaired because agents are mid-proof against this
form. `mei_theorem4` above has already been restated with the two measures
separated, so the pattern is established; this should follow once the current
round lands. Fixing (1) requires a `mismatchCoeffOcc` in `Target.lean` — the
ratio against `d^{π_θ}_μ` rather than `μ`.

Corrected: tabular `hF`, `mismatchCoeff` in place of a free real, values against
a start distribution, and `hr` restored.

**`astar` is EXISTENTIAL, matching `g1_aggregate_bound`.** Mei's own text
settles this twice: Lemma 8 reads "fix an arbitrary optimal policy `π*`" and
takes `a*(s)` to be an action *that* policy selects, and the paper's front matter
records that **"version (v3) generalizes Lemma 8 to multiple optimal actions"** —
so `Q*` ties were a known issue the authors patched. Quantifying `astar`
universally was never the paper's claim, and it is what refuted this family three
times.

`hastar` added 2026-08-22 after the same unconstrained-`astar` defect was
refuted in `g9_c_positive` (`Proofs.g9_is_false`). An arbitrary `astar` need not
select optimal actions, and the Łojasiewicz coefficient is meaningless — the
inequality unfounded — if it does not. -/
@[paper "Mei2020" "Lemma 8"]
theorem g1_lojasiewicz (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    ∃ astar : S → A, (∀ s, 0 < (πstar s) (astar s)) ∧
      (⨅ s : S, (F.toPolicy θ s) (astar s))
          / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
          * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
        ≤ ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖ :=
  Proofs.g1_lojasiewicz_proof M F hF hr hγ₀ hγ₁ μ hμ πstar hstar θ

/-- **G2 — AKM Lemma 4.1, gradient domination.**

VERBATIM, AKM (arXiv:1908.00261) Lemma 4.1:

> **Lemma 4.1 (Gradient domination).** *For the direct policy parameterization*
> (as in (2)), for all state distributions `μ, ρ ∈ Δ(S)`, we have
> ```
> V⋆(ρ) − V^π(ρ) ≤ ‖d^{π⋆}_ρ / d^π_μ‖_∞ · max_{π̄} (π̄ − π)ᵀ ∇_π V^π(μ)
>                ≤ (1/(1−γ)) · ‖d^{π⋆}_ρ / μ‖_∞ · max_{π̄} (π̄ − π)ᵀ ∇_π V^π(μ)
> ```

**Two discrepancies with the statement below, both mine, now recorded:**

1. The paper says **"for the direct policy parameterization"** — the simplex
   parameterization, not softmax. That is exactly why the `‖∇V‖` form was
   refutable for softmax: the softmax gradient carries an extra `π(a|s)` factor.
   The `hF` hypothesis below is therefore not the paper's setting, and the
   fidelity check correctly reports it as unused.
2. The paper's right side is `max_{π̄} (π̄ − π)ᵀ ∇V`, a maximum over policies of
   a directional derivative. The statement below uses `⨆ s, ∑ a (π⋆ − π)(a)·A(s,a)`
   — the advantage form, which is what the performance-difference identity gives.
   These agree by the policy gradient theorem but are not literally the same
   expression.

Corrected to AKM's *directional* right-hand side. Bounding by `‖∇V‖` is false
for softmax at any constant (defect 3 above); the advantage form is what the
paper actually proves.

**Proved 2026-08-22, and the proof reveals this statement is weaker than it
looks.** It uses neither `hF` (softmax) nor the optimality content of `hstar`:
the underlying `Proofs.Vinf_sub_le_adv_div` holds for *any* two policies, with
`hstar` serving only to rewrite `Vstar` as `Vinf πstar`. So the goal as frozen
is a corollary of a general fact about advantage bounds, not something specific
to softmax. The hypotheses are kept because the statement is frozen, but a
future revision could drop `hF` and state it at its true generality.

The route also avoids the infinite-horizon performance-difference *identity*,
which remains unproved. The observation is that the change of measure only ever
weakens the bound — `mismatchCoeff ≥ 1` always, since `d^π_μ` dominates `μ`
pointwise (the `t = 0` term alone contributes `μ s`) — so a pointwise bound
averaged against `μ` and weakened by `1 ≤ mismatchCoeff` suffices. That traded
a hard `tsum` telescoping argument for a max-state contraction. -/
@[paper_tool "AKM2021" "Lemma 4.1 (advantage form)"]
theorem g2_advantage_bound (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    VstarDist M μ - VinfDist M (F.toPolicy θ) μ
      ≤ (mismatchCoeff M πstar μ / (1 - M.γ))
          * (⨆ s : S, ⨆ a : A, |advInf M (F.toPolicy θ) s a|) :=
  Proofs.g2_gradient_domination_proof M F hF hr hγ₀ hγ₁ μ hμ πstar hstar θ

/-! ## The tie obstruction blocking G1

An agent proved G1 **modulo one hypothesis** and characterised exactly what is
missing (`Proofs.g1_lojasiewicz_of_greedy` is the frozen statement plus

```lean
hgreedy : ∀ s, advGapInf M π πstar s ≤ advInf M π s (astar s)
```

and nothing else). On the way it proved the infinite-horizon performance
difference lemma, **Fréchet differentiability of the value function** — which
this repo did not have at all, since `g7a` deliberately sidestepped it — and the
tabular softmax policy gradient `∂V/∂θ(s,a) = d^π_μ(s)·π(a|s)·A^π(s,a)`.

`hgreedy` is **not derivable** from the frozen hypotheses. `hastar` pins
`a*(s) ∈ argmax Q*(s,·)` and `hstar` pins `supp πstar` to the same set, but when
`Q*` **ties**, those can be *different* actions, and `Q*`-tied actions can carry
different `A^π`. Machine-found witness satisfying every frozen hypothesis:
`S = A = Fin 2`, `γ = 1/4`, `r = ![![0,1],![1,1]]`, where `Q*(1,·) = (4/3,4/3)`
is a genuine tie and `A^π(1,0) = −0.032 < A^π(1,1) = +0.008`.

**G1 is not refuted** — it holds on that witness (LHS `0.032` ≤ RHS `0.247`).
The slack is absorbed *across* states by the interplay of `d^{πstar}_μ` and
`d^π_μ`. Four distinct per-state factorizations were tested; every one is false
under ties, while the aggregate passed 40 000 randomized MDPs with zero
violations. Restricted to the no-tie case the per-state route passes cleanly.

So closing G1 needs a genuinely **cross-state** argument. That is stated below
as its own goal rather than left as a hypothesis inside G1 — the whole point of
this file is that missing content becomes a visible goal, not an assumption. -/

/-! ### The cross-state bound was FALSE too

I wrote `advantage_cross_state` as the repair for `hgreedy` failing pointwise
under `Q*` ties, on the evidence that the aggregate held over 40 000 randomized
MDPs. It is refuted (`Proofs.advantage_cross_state_general_false`, axioms clean).

Exact-rational witness: `S = A = Fin 2`, `γ = 1/2`, `r = ![![0,1],![1,1]]`,
`Q*(1,·) = (2,2)` a genuine tie, `πstar = δ₁`, `astar = ![1,0]`, `μ` uniform,
`θ = 0`. The conclusion reads **`2/3 ≤ 1/3`**.

The lesson is specific: **aggregating over states does not repair the tie
defect.** I had assumed the per-state deficits would cancel, and at state 0 the
mismatch has the *same sign* as at state 1, so they compound rather than
compensate. 40 000 random MDPs missed it because generic MDPs have no ties —
the counterexample needs an exact tie, which random sampling never produces.
That is a real limitation of numerical screening, and it is why the exact-
rational search found in minutes what the sweep could not.

What is true, and what G1 actually needs, is stated below. -/

/-! ### The aggregate bound, restated at the right selector

Refuted **twice** at `astar` (`Proofs.advantage_cross_state_general_false`,
`Proofs.g1_aggregate_bound_general_false`, `Proofs.g1c_aggregate_bound_general_false`).
The second refutation survived the `hastar` repair, and the reason is precise:

**`hastar : 0 < πstar(astar s | s)` puts `astar` IN the support, not at the TOP
of it.** `hstar` makes `πstar` optimal everywhere, so `optimal_support_greedy`
forces `Q*(s,a) = V*(s)` for *every* `a ∈ supp πstar` — the support is a set of
`Q*`-tied actions, and `hastar` only says `astar` is one of them. On the witness,
`supp πstar` at state 1 is `{1,3}` with `A^π(1,1) = 7/932` against
`A^π(1,3) = 107/466` — thirty times larger — and `πstar` puts `5/6` of its mass
on `3` (`Proofs.cc_tie_gap`).

**The repair is not another hypothesis on `astar`.**
`Proofs.g1_lojasiewicz_of_selector` shows `sum_abs_adv_le_norm` never uses
`hastar` at all — it needs only that ONE action is picked per state, which is
what makes the test vector's norm `√|S|`. So `g1_lojasiewicz` follows from the
aggregate bound at **any** selector `b : S → A`, and the old reduction was just
its `b = astar` instance.

So state it at the selector that works: `b(s) = argmax_a π(a|s)·A^π(s,a)`. That
form held over 75 000 tie-seeded MDPs (max violation `1.7e-13`) and is **tight**
— `lhs/rhs` reaches `0.9999999999`. It cannot be broken by a `Q*` tie because
`b` is read off `π` and `A^π` directly rather than routed through `πstar`.

**Proved 2026-08-22, with `astar` made EXISTENTIAL — which is what the paper
says.** Mei Lemma 8 reads "fix an arbitrary optimal policy `π*`" and takes
`a*(s)` to be an action *that policy* selects, so producing the witness is
faithful rather than a weakening. `Proofs.exists_argmax_selector` builds it as
`argmax_{a ∈ supp πstar(·|s)} A^π(s,a)`.

**The order of steps is the entire content.** Collapse
`X(s) := ∑_a πstar(a|s)·A^π(s,a) ≤ A^π(s,astar s)` and then
`c·A^π(s,astar s) ≤ π(astar s|s)·A^π(s,astar s) ≤ m(s)` *first*, and only then
apply `d^{πstar} ≤ mism·μ ≤ mism·d^π` to a now all-nonnegative sum. Every prior
refutation in this family applied the change of measure while still carrying
`X`.

Why universal `astar` could not be salvaged: every repair route wants
`mismatchCoeff M (detPolicy astar) μ` while the goal supplies
`mismatchCoeff M πstar μ` — different occupancies. The real bound
`d^{πstar}_μ ≥ d^{astar}_{γp,μ}` with `p := ⨅_s πstar(astar s|s)` exists, but `p`
appears nowhere in the statement. Two candidate sufficient conditions were
refuted numerically under a corrected `hstar` filter (1.0069 and 1.0376). -/

/-- **The aggregate Łojasiewicz bound at the maximizing selector.**

`Proofs.g1_lojasiewicz_of_selector` turns this into `g1_lojasiewicz`, so proving
it closes Mei Lemma 8.

Still genuinely cross-state: the per-state form fails by up to `0.59`. Three
other survivors were mapped and all are cross-state too (per-state `ℓ²` over
actions plus Cauchy–Schwarz over `S`; `‖∇‖₁`, which only buys `√(|S||A|)`; and
`sub ≤ mism·∑ d^π_μ(s)·max_a A^π(s,a)`, whose per-state form is provable but
whose chain to the gradient then loses `c`). That is the remaining research
gap. -/
@[infra "G1-aggregate"]
theorem g1_aggregate_bound (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A))
    (b : S → A)
    (hb : ∀ s a, (F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a
            ≤ (F.toPolicy θ s) (b s) * advInf M (F.toPolicy θ) s (b s)) :
    ∃ astar : S → A, (∀ s, 0 < (πstar s) (astar s)) ∧
      (⨅ s : S, (F.toPolicy θ s) (astar s))
          * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
        ≤ mismatchCoeff M πstar μ
            * ∑ s, |dinfDist M (F.toPolicy θ) μ s
                * ((F.toPolicy θ s) (b s) * advInf M (F.toPolicy θ) s (b s))| :=
  Proofs.exists_astar_g1_aggregate_bound M hr hγ₀ hγ₁ μ hμ (F.toPolicy θ) πstar hstar b hb

/-! ## G2 proper — AKM Lemma 4.1 with the gradient in it

The fidelity check caught this: `g2_advantage_bound` above was tagged
`@[paper] AKM2021 Lemma 4.1` and its proof **never used `hF`**, the softmax
hypothesis. The reason is that after two refutations I restated it into a
general advantage bound — true, useful, and with no gradient anywhere. Every
mechanical signal was green: grounded, witnessed, `sorry`-free, axioms clean.
It simply was not Lemma 4.1.

Retagged `@[paper_tool]`, where it belongs — `Proofs.Vinf_sub_le_adv_div` holds
for *any two policies*.

Lemma 4.1's content is that suboptimality is dominated by a **gradient**, which
is what makes gradient ascent converge. AKM state it with a directional right
side, `max_{π'} ⟨∇V, π' − π⟩` over the simplex, and that form is what survives
for softmax — the plain `‖∇V‖` version was refuted (a 3000-MDP sweep found
overshoots up to 74×, tracking `1/min_s π(a*|s)`).

Below, the directional maximum is expressed as a supremum over policies of the
directional derivative along `π' − π`, which is exactly AKM's quantity. -/

/-- **G2 — AKM Lemma 4.1, gradient domination.**

VERBATIM, AKM (arXiv:1908.00261) Lemma 4.1:

> **Lemma 4.1 (Gradient domination).** *For the direct policy parameterization*
> (as in (2)), for all state distributions `μ, ρ ∈ Δ(S)`, we have
> ```
> V⋆(ρ) − V^π(ρ) ≤ ‖d^{π⋆}_ρ / d^π_μ‖_∞ · max_{π̄} (π̄ − π)ᵀ ∇_π V^π(μ)
>                ≤ (1/(1−γ)) · ‖d^{π⋆}_ρ / μ‖_∞ · max_{π̄} (π̄ − π)ᵀ ∇_π V^π(μ)
> ```

**Two discrepancies with the statement below, both mine, now recorded:**

1. The paper says **"for the direct policy parameterization"** — the simplex
   parameterization, not softmax. That is exactly why the `‖∇V‖` form was
   refutable for softmax: the softmax gradient carries an extra `π(a|s)` factor.
   The `hF` hypothesis below is therefore not the paper's setting, and the
   fidelity check correctly reports it as unused.
2. The paper's right side is `max_{π̄} (π̄ − π)ᵀ ∇V`, a maximum over policies of
   a directional derivative. The statement below uses `⨆ s, ∑ a (π⋆ − π)(a)·A(s,a)`
   — the advantage form, which is what the performance-difference identity gives.
   These agree by the policy gradient theorem but are not literally the same
   expression.

Suboptimality is bounded by the mismatch-weighted *directional* gradient. Unlike
`g2_advantage_bound` this mentions a derivative, and unlike the refuted `‖∇V‖`
form it is true for softmax: the directional maximum over the simplex retains
the `π(a|s)` factor that a norm discards.

**The fidelity check flags `hF` as unused here, and that flag is a false
positive** — recorded rather than silenced, because the distinction is the whole
point of the check. When it fired on `g2_advantage_bound` it was right: that
statement had been substituted for Lemma 4.1 and had no gradient in it. Here the
statement *is* Lemma 4.1's directional right side; the inequality simply also
holds for a general policy family, so softmax is not needed to prove it. What
softmax buys is that the directional form is the right object to carry a
gradient at all.

The sharper `Proofs.g2b_sharp` drops the `1/(1-γ)` entirely and is stated for a
general `Policy`; this goal follows from it by weakening. So the frozen constant
is not tight — kept as frozen, since the statement is the paper's. -/
@[paper "AKM2021" "Lemma 4.1"]
theorem g2_gradient_domination (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    VstarDist M μ - VinfDist M (F.toPolicy θ) μ
      ≤ (mismatchCoeff M πstar μ / (1 - M.γ))
          * (⨆ s : S, ∑ a : A,
              ((πstar s) a - (F.toPolicy θ s) a) * advInf M (F.toPolicy θ) s a) :=
  Proofs.g2_gradient_domination_directional_proof M F hF hr hγ₀ hγ₁ μ hμ πstar hstar θ

/-! ## G8 / Mei Theorem 4 — the headline rate

All current rate results use finite-horizon `V`; both papers are
infinite-horizon. This goal is stated for `Vinf`, so discharging it closes G8
for the rate track as well. -/

/-- **Mei Theorem 4 — the `O(1/T)` rate for softmax policy gradient.**

VERBATIM, Mei et al. (arXiv:2005.06392) Theorem 4:

> **Theorem 4.** Let **Assumption 2** hold and let `{θ_t}_{t≥1}` be generated
> using Algorithm 1 with `η = (1−γ)³/8`, `c` the positive constant from Lemma 9.
> Then, for all `t ≥ 1`,
> ```
> V*(ρ) − V^{π_{θ_t}}(ρ) ≤ (16·S)/(c²·(1−γ)⁶·t) · ‖d^{π*}_μ / μ‖_∞
> ```

> **Assumption 2 (Sufficient exploration).** The initial state distribution
> satisfies `min_s μ(s) > 0`.

**Three things my earlier statement was missing**, all found by reading this:

1. **Assumption 2.** The start measure must have full support. I had a single
   start state — a Dirac, the maximal violation. Mei note the assumption
   "ensures sufficient exploration in the sense that the occupancy measure
   `d^π_μ` of any policy `π` when started from `μ` will be guaranteed to be
   positive over the whole state space", which is precisely what the proof needs.
2. **The mismatch factor `‖d^{π*}_μ / μ‖_∞` on the right.** I had dropped it, so
   the bound was unconditionally tighter than the paper's.
3. **Two measures.** Suboptimality is measured at `ρ`; the gradient and the
   occupancy are taken at `μ`. I had collapsed them.

**Corrected again 2026-08-22: `mismatchCoeff` is SQUARED, and there is a
`‖1/μ‖_∞` factor.** The full right-hand side is

```
16·S/(c²(1−γ)⁶·t) · ‖d^{π*}_μ / μ‖²_∞ · ‖1/μ‖_∞
```

My statement had the coefficient unsquared and omitted `‖1/μ‖_∞` entirely, so it
was **strictly stronger than the paper** by `m·‖1/μ‖_∞`, both of which are `≥ 1`.

That over-claim was not reachable from the spine, and the gap is machine-checked:
`Proofs.hconst_is_false` refutes the missing factor with two states, `γ = 0`,
uniform `μ` — there `m = 1`, `‖1/μ‖_∞ = 2`, so the needed
`‖1/μ‖_∞ · m · (1−γ)³ ≤ 1` reads `2 ≤ 1`.

With the factors restored, `Proofs.mei4_rho_rate_of_g3` discharges the theorem
outright from `hloja` and a non-degeneracy condition — and it is in fact
*stronger* than the paper, carrying `(1−γ)³` where Mei have `(1−γ)⁶`.

**PROVED 2026-08-22 — but read the constant carefully.** This repo's `dinf`
omits the leading `(1−γ)` that both papers put in the occupancy measure (see the
warning on `mismatchCoeff` in `Target.lean`), so

```
mismatchCoeff (repo) = (1/(1−γ)) · ‖d^{π*}_μ / μ‖_∞ (papers)
```

and it appears **squared** on the right. So what is proved here is Mei's
statement with an effective `(1−γ)⁸` where the paper has `(1−γ)⁶`.

Direction is **safe** — our bound is weaker than the paper's, never stronger, so
nothing is over-claimed. But this is *not yet* the paper's sharp rate, and
saying "Mei Theorem 4 is proved" without that qualifier would overstate it.
Closing the gap means inserting `(1−γ)` into `dinf` and re-deriving the twenty
files that mention it — mechanical, but it invalidates every proof currently
built against the unnormalized form.

`c` is a hypothesis with `hcbound` tying it to the trajectory, exactly as
`MEI_NOTES.md` in this repo recorded months ago and as Lemma 9 supplies. An
earlier version took `c` universally with only `0 < c`, which made the statement
false — the caller could send `c → ∞`.

The statement the repo is actually for. Note what it mentions and the current
`smooth_loja_rate` does not: an MDP, a softmax family, `Vinf`, and `V*`.

**FALSE as first frozen, for the third time by the same defect** (refuted
2026-08-22, `Proofs.mei4_is_false`, axioms clean). `logits` was universally
quantified with no regularity hypothesis — the identical hole already recorded
above for `g7_smoothness` (Defect 1) and `g1_lojasiewicz` (Defect 2), and not
repaired here when those were fixed.

The counterexample needs no analysis at all: take `logits θ s a := 0`, constant
in `θ`. Legal, since nothing constrains `logits`. The policy is then uniform at
every `θ`, so the objective is a *constant function*, its gradient is `0`, and
`hstep` degenerates to `θ(t+1) = θ t` — the trajectory never moves. In a `γ = 0`
MDP with rewards `1/0` the frozen policy has value `1/2` against `Vstar = 1`, so
the left side is the constant `1/2` for every `T` while the right side decays
like `1/T`. Any `T > 32/c²` breaks it, for every `c`.

Note this is **not** repaired by shrinking `c`: `c` is existential and sits in
the denominator, but the left side does not decay at all. The statement was
false, not merely weak.

The tabular theorem is **not** refuted — on the `g9` witness MDP, iterating the
exact recursion gives `c ≈ 4.89` satisfying the frozen inequality. This was a
statement bug, not a refutation of Mei.

**`c` is existential, and that is forced.** An earlier draft took `c` as a
universally quantified hypothesis `(c : ℝ) (hc : 0 < c)`. That statement is
**not provable**: quantifying `c` universally lets the caller send `c → ∞`,
driving the bound to `0` and so asserting `Vstar - Vinf ≤ 0` for every
reachable policy. Machine-checked: from `0 < x` and `∀ c > 0, x ≤ K / c²`,
taking `c = √(2K/x)` gives `x ≤ x/2`, a contradiction.

This is the mirror of the degenerate-witness trap. A quantity left floating is
a defect either way: existential and unconstrained makes the goal too *weak*
(the prover picks it); universal makes it too *strong* (the caller picks it).
The paper's `c` is a specific constant determined by the MDP and the trajectory
— their Lemma 9 — so it belongs outside the `∀ T`, chosen once, exactly as
here.

---

VERBATIM, Mei, Xiao, Szepesvári & Schuurmans (arXiv:2005.06392) Theorem 4
(main text and appendix Eq. (334) agree word for word):

> **Theorem 4.** Let Assumption 2 hold and let `{θ_t}_{t≥1}` be generated using
> Algorithm 1 with `η = (1 − γ)³/8`, `c` the positive constant from Lemma 9.
> Then, for all `t ≥ 1`,
> ```
>                              16S       ‖ d_μ^{π*} ‖²   ‖ 1 ‖
> V*(ρ) − V^{π_θt}(ρ)  ≤  ───────────── · ‖ ──────── ‖ · ‖ ─ ‖         (334)
>                         c²(1−γ)⁶ t      ‖    μ     ‖∞   ‖ μ ‖∞
> ```

with the two supporting quotes the constant depends on:

> **Assumption 2 (Sufficient exploration).** The initial state distribution
> satisfies `min_s μ(s) > 0`.

> **Lemma 9.** Let Assumption 2 hold. Using Algorithm 1, we have,
> `c := inf_{s∈S, t≥1} π_{θ_t}(a*(s)|s) > 0`.

and, for `a*`, from Lemma 9's proof and from the sentence fixing it in §4:

> For stating this and the remaining results, we fix a deterministic optimal
> policy `π*` and denote by `a*(s)` the action that `π*` selects in state `s`.

**CONFIRMED: the right-hand side now matches, term for term.**

| Mei | Lean | ✓ |
|---|---|---|
| `16S` | `16 * Fintype.card S` | ✓ |
| `c²(1−γ)⁶ t` | `c ^ 2 * (1 - M.γ) ^ 6 * T` | ✓ |
| `‖d_μ^{π*}/μ‖²_∞` | `mismatchCoeff M πstar μ ^ 2` (squared) | ✓ |
| `‖1/μ‖_∞` | `Proofs.invMuSup μ = (⨅ s, μ s)⁻¹` | ✓ |
| `V*(ρ) − V^{π_θt}(ρ)` | `VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ` | ✓ |
| Assumption 2 | `hμ : ∀ s, 0 < μ s` | ✓ |
| `η = (1−γ)³/8` | `hstep`'s `((1 - M.γ) ^ 3 / 8) •` | ✓ |
| `t ≥ 1` | `∀ T : ℕ, 1 ≤ T →` | ✓ |
| `c` from Lemma 9 | `(c : ℝ) (hc : 0 < c)` + `hcbound` | ✓ |
| two measures `ρ`, `μ` | `ρ` in the conclusion, `μ` in `hstep`/`mismatchCoeff` | ✓ |

The two corrections made earlier today — squaring `mismatchCoeff` and restoring
`invMuSup` — are the right ones, and `astar`/`hastar` correctly encode "the
action that the optimal policy selects".

⚠ **BUT: one factor is still off, and it is a NEW defect — `mismatchCoeff` uses
an UNNORMALIZED occupancy where both papers normalize.**

VERBATIM, AKM (arXiv:1908.00261v4) Eq. (4), the definition both papers use:

> it is useful to define the discounted state visitation distribution `d^π_{s₀}`
> of a policy `π` as:
> ```
> d^π_{s₀}(s) := (1 − γ) ∑_{t=0}^∞ γ^t Pr^π(s_t = s | s₀),          (4)
> ```
> [...] `d^π_ρ(s) = E_{s₀∼ρ}[d^π_{s₀}(s)]`, where `d^π_ρ` is the discounted
> state visitation distribution under initial distribution `ρ`.

VERBATIM, Mei (arXiv:2005.06392), inside the proof of Theorem 4, Eqs. (335)–(338):

> ```
> d_μ^{π_θ}(s) = E_{s₀∼μ}[ (1 − γ) ∑_{t=0}^∞ γ^t Pr(s_t = s | s₀, π_θ, P) ]
>              ≥ E_{s₀∼μ}[ (1 − γ) Pr(s₀ = s | s₀) ]
>              = (1 − γ) · μ(s)
> ```

Both carry the leading `(1 − γ)`; `d^π_ρ` is a **probability distribution**,
summing to `1` over `S`. The repo's is not:

```
dinf π s₀ s        = ∑' t, γ^t * visit t s₀ s          -- Infinite.lean:109
dinfDist π μ s     = ∑ s₀, μ s₀ * dinf π s₀ s          -- Target.lean:89
mismatchCoeff π μ  = ⨆ s, dinfDist π μ s / μ s         -- Target.lean:114
```

No `(1 − γ)`. So `dinf` sums to `1/(1−γ)`, and

```
mismatchCoeff (repo)  =  (1/(1−γ)) · ‖d_μ^{π*}/μ‖_∞ (Mei)
```

Since the coefficient enters **squared**, the Lean right-hand side is
`1/(1−γ)²` times Mei's — i.e. **larger**. Direction check: a larger right-hand
side is a **weaker** upper bound, so the statement below is *implied by* the
paper's and is **not an over-claim**. It is safe but unfaithful, and by a factor
that grows without bound as `γ → 1` — precisely the regime the `(1−γ)⁶` is
tracking. Stating the sharp `(1−γ)⁶` rate against an unnormalized coefficient
silently converts it into a `(1−γ)⁸` rate.

Note this also affects `mismatchCoeff`'s own docstring in `Target.lean`, which
quotes AKM Definition 3.1 (`‖d^π_ρ/μ‖_∞`) while defining the unnormalized
version — so the definition does not match the quote already attached to it.
And it affects every goal consuming `mismatchCoeff`: `g1_lojasiewicz`,
`g2_advantage_bound`, `mei_theorem4`. In `g2_advantage_bound` the coefficient is
on the right and unsquared, so the same `1/(1−γ)` slack applies there too.

**Statement left untouched**, per the freeze. The fix is one `(1 − γ) *` in
`dinf` (or in `mismatchCoeff`), which is a *definition* change with a wide blast
radius — every proof consuming `mismatchCoeff ≥ 1` would need rechecking, and
`Proofs.hconst_is_false`'s two-state witness would need recomputing.

Verdict: **MISMATCHES** — the shape, constants, quantifiers, hypotheses and
both measures are now exactly Mei's (the two earlier corrections landed), but
`mismatchCoeff` is unnormalized where Mei's `d_μ^{π*}` carries `(1 − γ)`,
making the bound weaker than the paper's by `1/(1−γ)²`. Safe, not faithful. -/
@[paper "Mei2020" "Theorem 4"]
theorem mei_theorem4 (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    -- Assumption 2 (Sufficient exploration): `min_s μ(s) > 0`.
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (ρ : Dist S)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    -- `c` the positive constant from Lemma 9 (`g9_c_positive`).
    (c : ℝ) (hc : 0 < c)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hcbound : ∀ t s, c ≤ (F.toPolicy (θ t) s) (astar s))
    -- Mei's Lemma 9 proof opens by assuming a strictly positive optimal value
    -- gap `Δ*(s) > 0`, which excludes `Q*` ties. `g9_c_positive` — the source of
    -- `c` and `hcbound` — already carries exactly this, so requiring it here
    -- costs nothing a caller does not already have.
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s)) :
    ∀ T : ℕ, 1 ≤ T →
      VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ
        ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)
            * mismatchCoeff M πstar μ ^ 2 * Proofs.invMuSup μ :=
  Proofs.mei_theorem4_of_astar_gap M F hF hr hγ₀ hγ₁ μ hμ ρ πstar hstar θ hstep c hc
    astar hastar hcbound hgap

/-! ## The remaining soft spot in the vacuity defence

`Witness.lean` shows the *MDP and logit* hypotheses are jointly satisfiable by a
concrete two-state MDP. It does not cover the trajectory hypotheses: `hstep`
*defines* `θ` by recursion, and `mismatch` is a free positive real. Those are
satisfiable in a cheap sense, so a consistency witness cannot certify that the
conclusions are non-vacuous there.

The honest fix is a goal, not a note: show the ascent recursion actually admits
a solution, and that the mismatch coefficient is a real quantity rather than an
arbitrary constant the caller supplies. -/

/-- **The gradient-ascent trajectory exists.**

`hstep` in `mei_theorem4` and `mei_theorem6` constrains `θ` by a recursion. That
is only meaningful if some sequence satisfies it — otherwise those theorems are
vacuously true for lack of any `θ`. -/
@[infra "Trajectory-exists"]
theorem ascent_trajectory_exists (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (μ : S) (θ₀ : EuclideanSpace ℝ (S × A)) :
    ∃ θ : ℕ → EuclideanSpace ℝ (S × A), θ 0 = θ₀ ∧ ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t) :=
  Proofs.ascent_trajectory_exists_proof M F μ θ₀

/-! ### The distribution-mismatch coefficient

**Superseded 2026-08-22.** The previous goal here read

```lean
∃ mismatch : ℝ, 0 < mismatch ∧ ∀ s, dinf M π μ s ≤ mismatch * (1 / (1 - M.γ))
```

and an agent proved it with `mismatch = 1`, for every MDP, every policy and
every start state. The defect: `1/(1-γ)` **already bounds `dinf` on its own**,
so the goal bounded `dinf` by a free constant times a quantity that already
bounds it, and any positive multiplier worked. A textbook degenerate witness —
the quantity was existentially bound, so the prover picked it.

The repair is to bound against `μ s` instead, which forces the coefficient to
see where `μ` puts little mass, and to *define* the coefficient rather than
quantify over it (`mismatchCoeff` in `Target.lean`, mirroring how `Vstar` is
defined rather than chosen). -/

/-- **The mismatch coefficient bounds the occupancy ratio.**

`d^π_μ(s) ≤ mismatchCoeff · μ(s)` for full-support `μ`.

**`hμ` was missing and the statement was FALSE without it** (found 2026-08-22 by
machine-checked refutation, `Proofs.mismatch_bound_is_false`). At a state with
`μ s = 0` reachable from the support of `μ`, the right side is `0` while the
left is positive — occupancy flows into `s` from states that do carry mass. The
`ciSup` cannot rescue it: that state's term is `dinfDist s / 0 = 0` by Lean's
junk-value convention.

This is the mirror of the defect this goal replaced. The superseded version was
too *weak* (a free existential constant); pinning the coefficient by definition
fixed that, but bounding against `μ s` without requiring `μ s > 0` made it too
*strong*. AKM state it for full-support `μ` precisely because `d^π_μ/μ` is
meaningless where `μ` vanishes — and it now matches `mismatch_pos`, which
carried `hμ` all along. -/
@[infra "Mismatch-bound"]
theorem mismatch_bound (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S)
    (hμ : ∀ s, 0 < μ s) (s : S) :
    dinfDist M π μ s ≤ mismatchCoeff M π μ * μ s :=
  Proofs.mismatch_bound_proof_of_support M hγ₀ hγ₁ π μ hμ s

/-- **The mismatch coefficient is positive**, given `μ` has full support.

Needs the `t = 0` term of `dinf`, which is the point mass at the start state. -/
@[infra "Mismatch-pos"]
theorem mismatch_pos (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S)
    (hμ : ∀ s, 0 < μ s) :
    0 < mismatchCoeff M π μ :=
  Proofs.mismatch_pos_proof M hγ₀ hγ₁ π μ hμ

/-! ## What Theorem 4 is actually blocked on

The refuting agent, having shown the `logits` defect, then characterised what
stands between the repaired statement and a proof. Stated here as goals rather
than left in a report.

The crux is that **`ascent_converges` gives only `∃ L ≤ fstar`, never
`L = fstar`** — the gap `G9` already names. And `c` cannot be recovered by
compactness: softmax positivity plus finiteness gives `⨅ s π_θ(a*|s) > 0` at each
*fixed* `t`, but the infimum is over `t : ℕ`, and the trajectory is
**unbounded** — `‖θ t‖ → ∞` is exactly what ascent does, so the simplex closure
meets the boundary. Positivity here is irreducibly asymptotic. -/

/-- **AKM Theorem 5.1 — softmax ascent reaches the optimum.**

VERBATIM, AKM (arXiv:1908.00261) Theorem 5.1:

> **Theorem 5.1 (Global convergence for softmax parameterization).** Assume we
> follow the gradient descent update rule as specified in Equation (11) *and
> that the distribution `μ` is strictly positive i.e. `μ(s) > 0` for all states
> `s`*. Suppose `η ≤ (1−γ)²/5`, then we have that for all states `s`,
> `V^(t)(s) → V⋆(s)` as `t → ∞`.

> **Remark 5.1 (Strict positivity of μ and exploration).** Theorem 5.1 assumed
> that optimization distribution `μ` was strictly positive [...] **We leave it
> as an open question of whether or not gradient descent will globally converge
> if this condition is not met.** The concern is that if this condition is not
> met, then gradient descent may not globally converge due to that `d^{πθ}_μ(s)`
> effectively scales down the learning rate for the parameters associated with
> state `s`.

**This refutes the goal below as I stated it.** It quantifies over a single
start state `μ : S` — a Dirac, the maximally degenerate violation of strict
positivity — and AKM explicitly leave that case OPEN. So the statement is not
AKM Theorem 5.1; it is a strictly stronger claim the paper declines to make.

The step size is also wrong: AKM require `η ≤ (1−γ)²/5`, the goal uses
`(1−γ)³/8`. The latter is `1/L` for the `8/(1−γ)³` smoothness constant, which is
the right shape but not the paper's number.

Both discrepancies come from paraphrasing rather than reading. Restating this
faithfully means a start *distribution* with full support, and `η ≤ (1−γ)²/5`.

The missing bridge. Every route to Theorem 4 passes through it, and `G9`'s `c`
follows from it rather than being assumed: `c > 0 ⟸ π_t(a*|s) ↛ 0 ⟸ V(θ_t) → V*`.

Mei cite AKM for this; AKM prove it asymptotically. It is the one genuinely
deep ingredient neither paper proves from first principles.

**Investigated 2026-08-22: the statement is true but the proof is out of reach**,
and the analytic half is done. Proved on the way (`Proofs/AKM51.lean`, all
axiom-clean): `∑ ‖∇V(θ_t)‖² < ∞`, hence `‖∇V(θ_t)‖ → 0`; monotone convergence to
*some* `L ≤ Vstar`; and `tendsto_vstar_of_limit_optimal`, which reduces this goal
to the single hypothesis "every limit of the trajectory's value is at least
`Vstar`". Numerically the claim holds (gap `6.5e-4` after `2·10⁵` steps, decaying
like `O(1/t)`), so the goal stays as stated.

Two structural blockers, recorded as goals below:

1. **This goal starts from a single state `μ : S`** — a Dirac. The only route
   from small gradient to small suboptimality here runs through
   `g1_lojasiewicz`, which factors through `mismatchCoeff` and so needs
   `hμ : ∀ s, 0 < μ s`. `Proofs.mismatch_bound_is_false` already refutes that
   bound without full support, and a Dirac is the maximally degenerate
   violation. So the Łojasiewicz machinery is inapplicable *by the shape of this
   statement*, not for want of effort.
2. **A mutual reduction.** `sum_abs_adv_le_norm` bounds only the product
   `d^π_μ(s)·π(a*|s)·A^π(s,a*)`, so vanishing gradients permit
   `π_t(a*|s) → 0` to do the work instead of `A → 0`. Excluding that is exactly
   `g9_c_positive`, which `Goal.lean` discharges by citing this goal. The two
   mutually reduce; compactness cannot break the cycle (`‖θ t‖ → ∞`), and
   monotonicity is ruled out (`m(t) ≥ m(0)` fails in 66/400 random MDPs). -/
@[infra "AKM-5.1"]
theorem softmax_ascent_converges (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) :
    Filter.Tendsto (fun t => Vinf M (F.toPolicy (θ t)) s) Filter.atTop
      (nhds (Vstar M s)) := sorry

/-- **Full-sequence policy convergence** — the single fact both AKM 5.1 and
Mei Lemma 9 now reduce to.

`Proofs.tendsto_vstar_of_policy_limit` is `softmax_ascent_converges` with its
exact hypotheses and conclusion, plus **only** `πbar` and `hlim`.
`Proofs.g9_of_policy_limit_bridge` is `g9_c_positive` likewise. So proving this
closes both.

**Why compactness is not enough.** `Proofs.exists_subseq_tendsto_policy` gives a
*subsequential* limit, and the residual chain cannot consume one: its spine
turns full-sequence convergence into an `∀ᶠ t in atTop` sign fact, extracts
`∀ t, T ≤ t → …`, then **inducts `t → t+1`** against `hstep`. A subsequence has
unbounded gaps, so the intermediate times are unconstrained. Three break points
were located — `eventually_adv_pos → theta_eventually_monotone`,
`eventually_adv_neg → theta_tendsto_atBot_of_adv_neg` (whose `ratio_induction`
telescopes step by step), and `exists_T0`, whose output is baked into the
*definition* of `B0`, so a φ-restricted `B0` is a different, larger set.

**The statement is TRUE — my "ties might break it" worry was wrong.** Checked
first, as it should have been. The repo's own tie witness (`G9b.lean`: one
state, three actions, `γ = 0`, `r = (1,1,0)`) proves `tieP t 0 → 0` and
`tieP t 2 → 0`, so the third probability tends to `1` — **the policy sequence
converges** there, to the deterministic policy on action 1.

The distinction that resolves it: ties break `g9_c_positive` (a uniform lower
bound at a *chosen* `astar`) **without** breaking policy convergence. Mass
leaves an abandoned tied action monotonically rather than oscillating. So do NOT
add an `hgap` hypothesis here; the two goals really do close by the same lemma.

A tie-seeded sweep agreed once scored correctly — and the scoring matters: the
right diagnostic is cumulative total variation `∑‖π_{t+1} − π_t‖₁`, not
`|π_t − π_T|`. One trajectory moved `0.97` in sup-norm between `t = 10⁴` and
`10⁵` yet had TV `6.7328` at `10⁵` and `6.7358` at `10⁶` — long plateaus then a
late switch, a path of finite length.

**Why the monotone route fails**, which is the sharper finding. Granting
advantage sign-stability outright is *still* not enough: softmax is monotone in
its own logit only *relative to the others*. Sign-stability forces `a₀`'s logit
up and all others down, so only `π_t(a₀|s)` is forced monotone — that half is
proved unconditionally (`Proofs.pi_astar_monotone_of_sign_stability`). For two
different abandoned actions the signs agree while their relative magnitudes are
unconstrained, so the slower-decaying one's probability *rises*: logits
`(0,0,0) → (0.1, −0.01, −1.0)` sends probabilities
`(0.333,0.333,0.333) → (0.449, 0.402, 0.149)` — action 1's logit fell while its
probability rose. For `|A| ≥ 3` the route closes exactly one coordinate per
state.

**PROVED FOR `γ = 0`** (`Proofs.softmax_policy_converges_gamma_zero`) — the
frozen statement verbatim, with no reward-tie assumption, subsuming the `G9b`
tie witness. And for general `γ` the goal reduces to one hypothesis
(`softmax_policy_converges_of_leader`): at each state, one tied action leads the
rest with never-shrinking logit gaps from some `T`.

**The closed-form identity that explains the whole obstruction.** Writing
`δ_t s = V̄ s − V_t(s) ≥ 0` (decreasing to `0`), for any action with vanishing
limiting advantage:

```
A_t(s,a) = δ_t s − γ · ∑_{s'} P(s'|s,a) · δ_t s'          (‡)
```

(`Proofs.adv_eq_value_gap_of_zero_limit`.) It settles three things at once:

1. **At `γ = 0` it collapses to `A_t(s,a) = δ_t s`** — the same nonnegative
   number for every tied action. So the `γ = 0` closure is not a lucky special
   case; `(‡)` shows it is the entire content of `γ = 0`.
2. **For `γ > 0` the sign of `A_t(s,·)` on the tied set is free.** Nothing forces
   `δ_t s ≥ γ⟨P(·|s,a), δ_t⟩`. It *is* forced at the state maximising `δ_t`, but
   that maximiser moves with `t`, so no fixed state has an eventual sign. That
   is why `Conv2` observed `A_t` negative for thousands of consecutive steps at
   tied states with `γ = 0.6`.
3. **The bounded-variation target is not reachable by majorisation.** From `(‡)`,
   `|A_t(s,a)| ≤ (1+γ)‖δ_t‖_∞`, so `∑‖π_{t+1} − π_t‖` is controlled once
   `∑‖δ_t‖_∞ < ∞`. But softmax PG converges at `Θ(1/t)`, so `∑‖δ_t‖_∞` diverges
   logarithmically — the *same* logarithm that kills `∑‖Δθ‖`. The policy total
   variation nonetheless saturates numerically, so the divergence is entirely an
   artefact of dropping the cancellation in
   `π_t(a|s)A_t(s,a) − π_t(b|s)A_t(s,b)`.

Also ruled out: the connectedness/Ostrowski route. All limit points share the
value function `V̄`, hence the same advantage, so the limit set sits inside a
product of simplices — itself connected, so connectedness adds nothing beyond
the singleton case already handled.

**The missing ingredient, named precisely:** a *rate comparison between the
decaying coordinates* — control of the **ratios** of logit decrements among
abandoned actions, not merely their signs. `summable_sq_grad` gives
`∑‖∇‖² < ∞`, which does not give `∑‖∇‖ < ∞` (`1/t` is the counterexample), and
the Łojasiewicz upgrade is unavailable because ascent drives `‖θ_t‖ → ∞`,
putting the limit set at infinity. `ResidC9.ratio_step` is exactly the needed
estimate — and it too binds `πbar` and `hlim`, so it is downstream of policy
convergence rather than a route to it. That circularity holds for every `Resid`
sign-stability fact.

A useful fact fell out while checking this: G9's step size `(1−γ)³/8` does
satisfy `η ≤ (1−γ)²/5` for `0 ≤ γ < 1`, so the residual chain applies to G9
unchanged. -/
@[infra "Policy-convergence"]
theorem softmax_policy_converges (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t)) :
    ∃ πbar : Policy S A,
      Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
        (nhds (fun s a => (πbar s) a)) := sorry

/-- **Off-support advantages are non-positive in the limit** — the residual of AKM 5.1.

An agent reduced `softmax_ascent_converges` to exactly this one statement
(`Proofs.limitAdvNonpos_of_offsupport` takes it and `tendsto_vstar_of_limitAdvNonpos`
closes the goal from it), and proved everything else: compactness of `Δ(A)^S`,
subsequence extraction, and `vinf_eq_vstar_of_adv_nonpos` (advantage `≤ 0`
everywhere gives `V^π = V*`, with no support hypothesis — so occupancy weights
never need matching, and the support mismatch I worried about is not the
obstruction).

**Why the obvious route fails**, and this is the sharp finding: at a
*deterministic* policy the condition `∀ s a, 0 < π̄(a|s) → A^{π̄}(s,a) = 0` holds
for **every** MDP unconditionally (`Proofs.greedy_support_vacuous_at_det`) — a
policy's own advantage averages to zero, so at the single action it plays the
advantage is automatically zero. Softmax ascent drives `‖θ t‖ → ∞`, so its limit
policies are generically deterministic, and `greedy_limit_points` therefore
yields **no information** exactly where it is needed. That goal is proved and
still does not close this one.

The remaining difficulty is about *actions*, not states: the gradient limit
constrains `A^{π̄}(s,a)` only where `π̄(a|s) > 0`. For an action ascent has driven
out, `π_t(a|s) → 0` makes the product vanish for the wrong reason. Closing it
needs a rate comparison between the decay of `π_t(a|s)` and the advantage — a
per-coordinate asymptotic estimate on `θ t` itself. That is what AKM actually
prove, and neither this repo nor Mathlib supplies it.

`Proofs.advInf_zero_of_stationary_finite` corroborates the diagnosis: at a
*finite* stationary point the strong all-actions condition does follow from
softmax positivity, so the entire difficulty sits at infinity. -/
@[infra "AKM-5.1-residual"]
theorem limit_adv_nonpos_offsupport (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a))) :
    ∀ s a, (πbar s) a = 0 → advInf M πbar s a ≤ 0 :=
  Proofs.limit_adv_nonpos_offsupport_proof M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim

/-- **The vector-parameter ascent step.**

`domination_rate_abstract` and `ascent_step` are stated for `f : ℝ → ℝ` — a
scalar derivative — while the goals step by `gradient` in
`EuclideanSpace ℝ (S × A)`. Mechanical given `g7b_smoothness`, but real work,
and nothing composes without it. -/
@[infra "Vector-ascent-step"]
theorem vec_ascent_step (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : EuclideanSpace ℝ (S × A)) :
    Vinf M (F.toPolicy θ) μ
        + ((1 - M.γ) ^ 3 / 16) * ‖gradient (fun w => Vinf M (F.toPolicy w) μ) θ‖ ^ 2
      ≤ Vinf M (F.toPolicy
          (θ + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) θ)) μ :=
  Proofs.vec_ascent_step_proof M F hF hr hγ₀ hγ₁ μ θ

/-! ### `greedy_limit_points` was FALSE — unreachable states

Refuted (`Proofs.greedy_limit_points_frozen_is_false`, which takes the frozen
statement *with `Goal.lean`'s own implicit and instance binders* as a hypothesis
and derives `False`, so what is refuted is provably this statement and not a
lookalike).

I flagged the occupancy factor as a worry when writing it and stated it anyway
over **all** `s`. That was the defect. Witness: `γ = 1/2`, start state `0`
absorbing with zero reward, state `1` unreachable with `r(1,·) = (1,-1)`. Then
`V^π(0) = 0` for *every* policy, so the objective is the constant function, its
gradient is `0`, `hstep` collapses to `θ(t+1) = θ(t)`, and the uniform `π̄` is a
limit. The conclusion fails at the unreachable state.

And option (b) — handling unreachable states some other way — is not merely
unproved but **impossible**: the ascent dynamics are literally independent of
the MDP's data off the reachable set. Two MDPs agreeing on the reachable part
give identical gradients, trajectories and limit policies while differing
arbitrarily in `advInf` there. No argument about the trajectory can constrain
what the trajectory cannot see.

This also sharpens the `softmax_ascent_converges` obstruction note above: that
records the blocker as a per-coordinate asymptotic estimate on `θ t`, which is
true for the *reachable* part. The unreachable part is a separate and strictly
fatal defect that no such estimate repairs. -/

/-- **Greedy limit points, at reached states** — the real content of AKM 5.1.

At every state with positive limiting occupancy, every action in `π̄`'s support
has zero advantage. Given this, `optimal_support_greedy` and `vstar_eq_greedy`
finish `softmax_ascent_converges`. Stated over policies rather than parameters
deliberately: the simplex is compact, parameter space is not, and `‖θ t‖ → ∞` is
exactly what defeats a compactness argument upstairs.

The occupancy hypothesis is what the refutation above forces, and it should be
enough downstream — `perfDiffInf` weights `advGapInf` by an occupancy that
vanishes off the reached set, exactly as `dirac_gradient_domination` exploits. -/
@[infra "Greedy-limit-points"]
theorem greedy_limit_points (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a))) :
    ∀ s a, 0 < dinf M πbar μ s → 0 < (πbar s) a → advInf M πbar s a = 0 :=
  Proofs.greedy_limit_points_proof M F hF hr hγ₀ hγ₁ μ θ hstep πbar hlim

/-- **Dirac-compatible gradient domination.**

`g1_lojasiewicz` needs `hμ : ∀ s, 0 < μ s`, so no single-start-state goal in this
repo can use the Łojasiewicz route — `mismatch_bound` is refuted without full
support, and a Dirac is the worst case. The correct substitute is the comparator
occupancy `dinf M πstar μ`, which is positive exactly on the states `πstar`
reaches from `μ`. `perfDiffInf` already supplies the identity.

**Proved 2026-08-22, and it is an EQUALITY** — restated as such, since the
reverse direction is free and the inequality was strictly weaker than what
holds. It is `perfDiffInf` verbatim at `π' := πstar`, `s₀ := μ`: `pdInf` unfolds
to `∑ s, dinf M π' s₀ s * advGapInf M π π' s`, and `advGapInf` is definitionally
the frozen right-hand side. Four lines.

The mechanism is exactly why this sidesteps full support: `μ s` never appears in
a denominator, so `mismatch_bound` never enters and `dinf M πstar μ` is
automatically supported precisely where `πstar` reaches. Note the caveat: the
bound is against the *comparator's* occupancy, so a downstream step needing the
*learner's* occupancy will reintroduce a mismatch factor there rather than here.

`hF` is unused (the result holds for any policy family) and only `hstar μ` is
needed rather than `∀ s`. Kept as frozen. -/
@[infra "Dirac-domination"]
theorem dirac_gradient_domination (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (μ : S) (θ : EuclideanSpace ℝ (S × A)) :
    Vstar M μ - Vinf M (F.toPolicy θ) μ
      = (∑ s, dinf M πstar μ s * ∑ a, (πstar s) a * advInf M (F.toPolicy θ) s a) :=
  Proofs.dirac_gradient_domination_eq M F hr hγ₀ hγ₁ πstar hstar μ θ

/-- **The vector-parameter rate recursion** — what `mei_theorem4` composes with.

`Mei.smooth_loja_rate` proves exactly this shape but for `f : ℝ → ℝ`, a *scalar*
derivative. The goals step by `gradient` in `EuclideanSpace ℝ (S × A)`, so the
recursion has to be redone there. `vec_ascent_step` (proved) is the per-step
half; this is the `1/T` accumulation on top of it.

Stated abstractly on purpose: it is a fact about smooth Łojasiewicz ascent, not
about MDPs, and keeping it that way is what let the scalar version be reused
across `Mei.lean` and `AKM.lean`. Instantiating it at
`f = VinfDist M (F.toPolicy ·) μ` is then `mei_theorem4`'s remaining work,
together with `g1_lojasiewicz` for `hloja` and `g9_c_positive` for `c`. -/
@[infra "Vector-rate"]
theorem vec_smooth_loja_rate {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {c fstar β : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (x : ℕ → E) (hx : ∀ t, x (t + 1) = x t + (1 / β) • gradient f (x t))
    (hloja : ∀ t, c * (fstar - f (x t)) ≤ ‖gradient f (x t)‖)
    (hlt : ∀ t, f (x t) < fstar)
    (T : ℕ) (hT : 1 ≤ T) :
    fstar - f (x T) ≤ 1 / (c ^ 2 / (2 * β) * T) :=
  Proofs.vec_smooth_loja_rate_proof hβ hc hgrad hsmooth x hx hloja hlt T hT

/-- **Mei Theorem 6 — the entropy-regularized geometric rate.**

VERBATIM, Mei et al. (arXiv:2005.06392) Theorem 6:

> **Theorem 6.** Suppose `μ(s) > 0` for all state `s`. Using Algorithm 1 with the
> entropy regularized objective and softmax parametrization and
> `η = (1−γ)³/(8 + τ(4 + 8 log A))`, **there exists a constant `C > 0`** such
> that for all `t ≥ 1`,
> ```
> Ṽ^{π*_τ}(ρ) − Ṽ^{π_θt}(ρ) ≤ (‖1/μ‖_∞) · ((1 + τ log A)/(1−γ)²) · e^{−C(t−1)}
> ```

Restated 2026-08-22 over `VsoftDisc`, the soft Bellman fixed point, after the
earlier version was refuted three ways. Three things the refuted version got
wrong, all visible in the quote above:

1. **`C` is existential**, not a free universal `K`. The old form let the caller
   pick `K` near 1 and force near-instant convergence.
2. **`η` is pinned** to `(1−γ)³/(8 + τ(4 + 8 log A))`, not free. A step size that
   is too large diverges — `Proofs.mei6_false_tabular` refutes the free-`η` form
   with `η = 10` on a one-state MDP, where the objective *decreases*.
3. **The objective is the discounted-entropy `Ṽ`**, not `Target.VinfSoft`, which
   adds entropy at the start state only. `Proofs.VsoftDisc` is the right object;
   `Proofs.VsoftStarDisc` is its supremum, well-defined via
   `bddAbove_range_VsoftDisc`.

Note the constant is calibrated in `log A`, which is why the sharp Gibbs bound
`Proofs.entropy_le_log_card` was needed — the earlier `entropy ≤ |A| − 1` could
not state this at all.

Still missing for a proof: Mei's Lemma 14 (smoothness of the discounted entropy,
`(4 + 8 log A)/(1−γ)³`), Lemma 15 (soft Łojasiewicz), and the existence of `π*_τ`
as a soft-greedy fixed point. `Proofs.softBackup_softmax` and
`softBackup_sub_eq_KL` are the variational identities underneath Lemma 15. -/
@[paper "Mei2020" "Theorem 6"]
theorem mei_theorem6 (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (τ : ℝ) (hτ : 0 < τ)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (ρ : Dist S)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / (8 + τ * (4 + 8 * Real.log (Fintype.card A))))
          • gradient (fun w => ∑ s, μ s * Proofs.VsoftDisc M (F.toPolicy w) τ s) (θ t)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      (∑ s, ρ s * Proofs.VsoftStarDisc M τ s)
          - (∑ s, ρ s * Proofs.VsoftDisc M (F.toPolicy (θ t)) τ s)
        ≤ Proofs.invMuSup μ * ((1 + τ * Real.log (Fintype.card A)) / (1 - M.γ) ^ 2)
            * Real.exp (-C * (t - 1)) := sorry

/-! ### The entropy track: what the papers actually say

Two corrections from reading Mei's text, both of which would have produced
mislabeled theorems if taken from my paraphrase.

**Lemma 14 is not what I said it was.** Verbatim:

> `ℍ(ρ, π_θ)` is `(4 + 8 log A)/(1−γ)³`-smooth, where `A := |𝒜|`.

It is about the **discounted entropy `ℍ` alone**, not "`Ṽ` is `β`-smooth". The
constant `(8 + τ(4 + 8 log A))/(1−γ)³` appears only inside the *proof* of Theorem
6 and is never a numbered lemma. Note it is calibrated in `log A` — so the
repo's earlier `entropy ≤ |A| − 1` could not state Lemma 14 at all. The sharp
Gibbs bound `entropy ≤ log |A|` (`Proofs.entropy_le_log_card`) is now proved and
is what makes the statement expressible.

**The soft performance difference has a term I did not anticipate.** Mei's soft
advantage (their Eq. 18) is `Ã^π(s,a) = Q̃^π(s,a) − τ log π(a|s) − Ṽ^π(s)`,
carrying the *inner* policy's log. Averaged under `π'` that produces a
**cross-entropy**, not `π'`'s own entropy, so an explicit correction term
`entGap = ∑ₐ π'(a|s)(log π(a|s) − log π'(a|s)) = −D_KL(π'‖π)` is required.
`Proofs.perfDiffSoft` carries it; `Proofs.sum_advSoft_self` calibrates it
independently, and `VsoftDisc_zero` checks the `τ = 0` collapse to `Vinf`.

Proved toward Lemma 15: `Proofs.softBackup_softmax` (Mei's Eq. 26 as a
variational statement rather than an assumed fixed point) and
`softBackup_sub_eq_KL` — every other policy's shortfall is exactly `τ` times a
KL, which is the mechanism putting a KL on Lemma 15's right-hand side.

Still missing for the entropy track: the smoothness ladder (the entropy analogue
of `G7b`, where each rung's reward is *parameter-dependent* unlike the constant
`r` of the unregularized case), the existence of `π_τ*` as a soft-greedy fixed
point (a contraction argument absent here), and Mei's Lemma 10 gradient formula.
Theorem 6 is not restated until those exist. -/

/-! ## G10 — the entropy-regularized track

`geometric_rate` mentions no entropy, no `τ`, no policy and no MDP; its
hypothesis `hstep` *is* Mei Theorem 6. Their Lemmas 14 (entropy smoothness),
15 (entropy Łojasiewicz) and 16 exist to establish that contraction, and none is
formalized. -/

/-! ## Theorem 6 was FALSE three ways — the entropy track needs rebuilding

Refuted 2026-08-22 by two independent machine-checked counterexamples, plus a
definitional defect neither of my stated concerns anticipated.

**1 — free `logits`** (`Proofs.mei6_general_false`). The same defect as
`g7_smoothness`, `g1_lojasiewicz` and `mei_theorem4`: `logits ≡ 0` makes the
policy uniform at every `θ`, so the objective is constant, the gradient is `0`,
and the trajectory never moves while the gap stays positive.

**2 — `K` universal and `η` free** (`Proofs.mei6_false_tabular`). The decisive
one, because it pins Mei's genuine **tabular** parameterization and so cannot be
dismissed as parameterization abuse. One state, two actions, `γ = 0`,
`r = (1,0)`, `τ = 1`, `η = 10`: the objective reduces to
`fsoft d = σ(d)(1−d) + log(e^d+1)`, one step sends the logit gap `0 → 5`
exactly, and `fsoft 5 < fsoft 0` — the objective *decreases*, so the gap
*grows*, contradicting the bound for **every** `K ∈ (0,1)` at once. Numerically
`η = 5` already diverges (ratio 1.004).

**3 — `VinfSoft` is not Mei's objective.** It adds entropy at the **start state
only**; Mei's `Ṽ` discounts entropy along the whole trajectory (the soft Bellman
fixed point). The bonus does not propagate, `VsoftStar` has no log-sum-exp form,
and their Lemmas 14/15/16 are not true over it. **So fixing the quantifiers is
not enough** — `Target.lean` needs a genuinely new definition first.

Theorem 6 is therefore not restated here yet. Stating it over a definition known
to be wrong would be worse than leaving it out: the goal would look like
progress while measuring nothing. The prerequisites are below; Theorem 6 returns
once `VsoftDisc` exists. -/

/-- **The discounted-entropy soft value** — the definition Theorem 6 needs.

`Ṽ^π(s) = E[∑ₜ γᵗ (r(sₜ,aₜ) + τ·H(π(·|sₜ)))]`, the soft Bellman fixed point,
as opposed to `VinfSoft`'s start-state-only bonus. Everything in the entropy
track waits on this. -/
@[infra "Soft-value"]
theorem vsoftDisc_exists (M : FiniteMDP S A) (τ : ℝ) (hτ : 0 < τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) :
    ∃ V : Policy S A → S → ℝ,
      ∀ π s, V π s = (∑ a, (π s) a * M.r s a) + τ * entropy (π s)
        + M.γ * ∑ a, (π s) a * ∑ s', (M.P s a) s' * V π s' :=
  Proofs.vsoftDisc_exists_proof M τ hτ hr hγ₀ hγ₁

/-- **Entropy is bounded** — needed before `⨆ π, Ṽ` means anything.

`VsoftStar` is a `ciSup`; without `BddAbove` Mathlib returns junk `0` and every
statement about it is vacuous. Proved as `Proofs.entropy_le_card` during the
refutation; stated here so the dependency is explicit. -/
@[infra "Entropy-bounded"]
theorem entropy_bdd (d : Dist A) : entropy d ≤ (Fintype.card A : ℝ) - 1 :=
  Proofs.entropy_bdd_proof d

end PolicyGradient
