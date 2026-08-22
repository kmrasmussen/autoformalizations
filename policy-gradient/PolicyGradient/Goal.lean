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

Under a non-degeneracy condition (some policy is strictly suboptimal, i.e. the
MDP is not one where every policy is optimal), a softmax policy — which puts
positive mass on every action — is strictly suboptimal.
This is what licenses the `0 < δ t` the `1/t` recursion needs. -/
@[paper "Mei2020" "Lemma 9 (strictness)"]
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
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (astar : S → A) (hastar : ∀ s, Qstar M s (astar s) = Vstar M s) :
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

`‖∇V‖ ≤ 2/(1-γ)²`, the vector-parameter analogue of `abs_dV_le_softmax`. Note
`hF` now pins the **tabular** parameterization: the logits *are* the parameter
coordinates. -/
@[paper "AKM2021" "Lemma E.4 (gradient)"]
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
one-line edit — see `vec_c2_family` below. -/
@[paper "AKM2021" "Lemma E.4"]
theorem g7b_smoothness (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s₀ : S) :
    ‖fderiv ℝ (fun t => fderiv ℝ (fun u => Vinf M (F.toPolicy u) s₀) t) θ‖
      ≤ 8 / (1 - M.γ) ^ 3 := sorry

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

Corrected: tabular `hF`, `mismatchCoeff` in place of a free real, values against
a start distribution, and `hr` restored.

`hastar` added 2026-08-22 after the same unconstrained-`astar` defect was
refuted in `g9_c_positive` (`Proofs.g9_is_false`). An arbitrary `astar` need not
select optimal actions, and the Łojasiewicz coefficient is meaningless — the
inequality unfounded — if it does not. -/
@[paper "Mei2020" "Lemma 8"]
theorem g1_lojasiewicz (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (astar : S → A) (hastar : ∀ s, Qstar M s (astar s) = Vstar M s)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    (⨅ s : S, (F.toPolicy θ s) (astar s))
        / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖ := sorry

/-- **G2 — AKM Lemma 4.1, gradient domination.**

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
          * (⨆ s : S, ⨆ a : A, |advInf M (F.toPolicy θ) s a|) :=
  Proofs.g2_gradient_domination_proof M F hF hr hγ₀ hγ₁ μ hμ πstar hstar θ

/-! ## G8 / Mei Theorem 4 — the headline rate

All current rate results use finite-horizon `V`; both papers are
infinite-horizon. This goal is stated for `Vinf`, so discharging it closes G8
for the rate track as well. -/

/-- **Mei Theorem 4 — the `O(1/T)` rate for softmax policy gradient.**

The statement the repo is actually for. Note what it mentions and the current
`smooth_loja_rate` does not: an MDP, a softmax family, `Vinf`, and `V*`.

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
here. -/
@[paper "Mei2020" "Theorem 4"]
theorem mei_theorem4 (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 1 ≤ T →
      Vstar M μ - Vinf M (F.toPolicy (θ T)) μ
        ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T) := sorry

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

/-! ## G10 — the entropy-regularized track

`geometric_rate` mentions no entropy, no `τ`, no policy and no MDP; its
hypothesis `hstep` *is* Mei Theorem 6. Their Lemmas 14 (entropy smoothness),
15 (entropy Łojasiewicz) and 16 exist to establish that contraction, and none is
formalized. -/

/-- **Mei Theorem 6 — the entropy-regularized geometric rate.**

Unlike Theorem 4 this constant is explicit, because the analogue of their
Lemma 9 (their Lemma 16) follows from monotone convergence rather than an
external citation. -/
@[paper "Mei2020" "Theorem 6"]
theorem mei_theorem6 (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (τ : ℝ) (hτ : 0 < τ) (μ : S) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfSoft M (F.toPolicy w) τ μ) (θ t))
    (K : ℝ) (hK₀ : 0 < K) (hK₁ : K < 1) (t : ℕ) :
    VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ t)) τ μ
      ≤ (VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ 0)) τ μ) * (1 - K) ^ t := sorry

end PolicyGradient
