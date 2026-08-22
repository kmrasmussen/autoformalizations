/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Bridge

/-!
# Conv — full-sequence policy convergence (`Goal.softmax_policy_converges`)

The single fact both `Goal.softmax_ascent_converges` (AKM Theorem 5.1) and
`Goal.g9_c_positive` (Mei Lemma 9) reduce to, via
`Proofs.tendsto_vstar_of_policy_limit` and `Proofs.g9_of_policy_limit_bridge`.

## Status: OPEN, with the obstruction localized

This file records (a) the numerical evidence that the frozen statement is
**true** — so it should *not* be restated with an `hgap` hypothesis — and
(b) the precise missing analytic ingredient, together with the reduction of the
goal to it, machine-checked.

### The statement is very likely TRUE as frozen

The natural worry, recorded in `Goal.lean`'s docstring for this goal, is that
under `Q*` **ties** the policy sequence need not converge, because
`Proofs.g9_c_positive_frozen_is_false` builds a trajectory where ascent
abandons one of two *tied optimal* actions. That witness does **not** refute
this goal, and the reason is worth recording:

* In the `tie` witness (`G9b.lean`: one state, three actions, `γ = 0`,
  `r = (1,1,0)`) the proved facts are `tieP t 0 → 0` (`tieP_zero_inf` plus
  `tiex_ge_Sm`) and `tieP t 2 → 0` (`tieP_two_tendsto`).  Since the three
  probabilities sum to one, `tieP t 1 → 1`.  **The policy sequence converges**,
  to the deterministic policy on action `1`.  What fails there is only the
  *uniform lower bound at a chosen `astar`*, which is a different assertion.

So ties break `g9_c_positive` without breaking policy convergence: mass leaves
the abandoned tied action monotonically, it does not oscillate between the tied
actions.

A tie-seeded numerical sweep agrees.  Integer reward grids on `|S| ≤ 3`,
`|A| ≤ 3` with deterministic transitions and `γ ∈ {0, 0.3, 0.5, 0.9}`, run to
`10⁶` steps at `η = (1-γ)²/5`, were scored by the **cumulative total variation**
`∑_t ‖π_{t+1} − π_t‖₁` of the policy path — the diagnostic that distinguishes a
slowly drifting but convergent path from a genuinely oscillating one.  In every
case the total variation *saturated*: e.g. one trajectory that still moved by
`0.97` in sup-norm between `t = 10⁴` and `t = 10⁵` had total variation `6.7328`
by `t = 10⁵` and `6.7358` by `t = 10⁶` — a path of **finite length**, hence
Cauchy.  Long plateaus followed by a late switch are common (that is what made
the naive "compare `π_t` to `π_T`" statistic look like non-convergence), but no
trajectory accumulated unbounded length.  Tied states behave as expected: where
`r(s,·)` is constant the advantage vanishes identically, the gradient is zero at
that state, and the policy *freezes* rather than cycling — one sweep converged
to the genuinely stochastic limit `(0.742, 0.258, 0.000)` at a tied state.

### The missing ingredient, precisely

`finite_length_of_summable_increments` below is the reduction: **a policy path
of finite length converges**, in exactly the frozen goal's coordinatewise form,
with the limit produced rather than assumed.  It is proved here in full.  So the
goal reduces to

    `Summable (fun t => ‖θ (t+1) - θ t‖)`,      (†)

equivalently `∑_t ‖∇V(θ_t)‖ < ∞`, since `θ_{t+1} - θ_t = η ∇V(θ_t)` exactly.

What the repo supplies is `Proofs.summable_sq_grad`: `∑_t ‖∇V(θ_t)‖² < ∞`.
**That is strictly weaker and does not imply (†)** — `‖∇_t‖ = 1/t` is square
summable and not summable — and this gap is the whole content of the goal.  It
is not a bookkeeping gap; `∑‖∇‖² < ∞` is what a smoothness/ascent argument gives
for *any* gradient method, and it is exactly why "gradient methods converge in
value but their iterates may not converge" is true in general.

Closing (†) needs one of the two standard mechanisms, **neither of which the
repo or Mathlib currently has**:

1. **A Łojasiewicz inequality at the limit set.**  `‖∇V(θ)‖ ≥ c · |V(θ) − V*|^α`
   with `α ∈ [1/2, 1)` near the limit set upgrades square-summability to
   summability by the standard Absil–Mahony–Andrews telescoping argument.  The
   repo's `g1_lojasiewicz` is the right shape but is a *global* bound factoring
   through `mismatchCoeff`, and — decisively — softmax ascent drives
   `‖θ_t‖ → ∞` (`ResidC8.tendsto_min_theta_atBot`, `ResidC9`), so the limit set
   lies **at infinity**, where no Łojasiewicz exponent is available.  This is the
   same "the entire difficulty sits at infinity" diagnosis that
   `Goal.limit_adv_nonpos_offsupport`'s docstring records.

2. **Coordinatewise monotonicity of `θ` from some finite time on.**  A path each
   of whose coordinates is eventually monotone has finite length as soon as it is
   bounded — and in *policy* space it is bounded, since `π` lands in the simplex.
   Concretely: if for every `(s,a)` the sign of `advInf M (F.toPolicy (θ t)) s a`
   were eventually constant, then `theta_decrement` (`ResidC9.lean:168`) makes
   each `θ_t(s,a)` eventually monotone, each `π_t(a|s)` is then eventually
   monotone and bounded in `[0,1]`, hence convergent, and the goal follows.
   `monotone_route` below proves exactly this implication, so the goal also
   reduces to the *eventual sign-stability of the advantages*.

   **This is the more promising route**, and it is where the circularity bites:
   `ResidC8`/`ResidC9` do prove `max_a θ_t(s,a) → ∞` and `θ_t(s,a) → −∞` on
   `I⁻` — but every one of those results takes `πbar` **and `hlim` as
   hypotheses** (`eventually_adv_neg`, `theta_eventually_antitone`,
   `theta_tendsto_atBot_of_adv_neg` all bind `hlim` in their signatures).  They
   are consequences of policy convergence, not routes to it.  Using them here
   would be circular, and that is the sharp finding of this file: **the `Resid`
   structural facts cannot close (†), because they are downstream of the very
   statement they would be used to prove.**

Breaking that circle needs sign-stability of the advantages derived from
`hstep` alone, with no limit policy in hand.  That is the missing ingredient,
and it is genuinely new mathematics — AKM's Appendix C.1 assumes the limit
policy exists throughout.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ## A policy path of finite length converges

This is the reduction referred to above: it produces the limit `πbar` in exactly
the frozen goal's shape, from summability of the policy increments. -/

/-- Coordinatewise Cauchy-ness of the softmax policies, from summability of the
per-coordinate increments.  Stated for a bare real sequence so it can be reused
for each `(s,a)` coordinate. -/
theorem exists_tendsto_of_summable_increments {f : ℕ → ℝ}
    (h : Summable (fun t => |f (t + 1) - f t|)) : ∃ L : ℝ, Tendsto f atTop (nhds L) := by
  have hc : CauchySeq f := by
    refine _root_.cauchySeq_of_summable_dist ?_
    simpa [Real.dist_eq, abs_sub_comm] using h
  exact cauchySeq_tendsto_of_complete hc

/-- **Coordinatewise convergence of a policy sequence assembles into a policy
limit**, in exactly the frozen goal's shape.

Given that each coordinate `t ↦ (π t s) a` converges, the limits form a genuine
`Policy S A`: nonnegativity and the sum-to-one constraint are closed conditions
and so pass to the limit.  The conclusion is literally
`∃ πbar, Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a))`,
which is the frozen goal's conclusion with `F.toPolicy (θ t)` for `π t`. -/
theorem exists_policy_limit_of_coord_tendsto (π : ℕ → Policy S A)
    (h : ∀ s a, ∃ L : ℝ, Tendsto (fun t => (π t s) a) atTop (nhds L)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a)) := by
  classical
  choose L hL using h
  -- the limit is nonnegative in each coordinate
  have hnn : ∀ s a, 0 ≤ L s a := by
    intro s a
    exact ge_of_tendsto' (hL s a) (fun t => (π t s).nonneg a)
  -- and sums to one in each state
  have hsum : ∀ s, ∑ a, L s a = 1 := by
    intro s
    have hts : Tendsto (fun t => ∑ a, (π t s) a) atTop (nhds (∑ a, L s a)) :=
      tendsto_finsetSum _ (fun a _ => hL s a)
    have hone : (fun t => ∑ a, (π t s) a) = fun _ => (1 : ℝ) :=
      funext fun t => (π t s).sum_eq_one
    rw [hone] at hts
    exact (tendsto_nhds_unique tendsto_const_nhds hts).symm
  refine ⟨fun s => ⟨L s, hnn s, hsum s⟩, ?_⟩
  -- convergence in the product topology is coordinatewise convergence
  rw [tendsto_pi_nhds]
  intro s
  rw [tendsto_pi_nhds]
  intro a
  exact hL s a

/-- **The reduction.** If every coordinate of the parameter sequence has
summable increments, the softmax policy sequence converges — the frozen goal's
conclusion, with the limit produced rather than assumed.

Softmax is continuous, so it suffices that each `θ_t (s,a)` converges; the
policy limit is then assembled by `exists_policy_limit_of_coord_tendsto`. -/
theorem policy_converges_of_summable_theta_increments
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hsum : ∀ s a, Summable (fun t => |(θ (t + 1)) (s, a) - (θ t) (s, a)|)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) := by
  classical
  -- each parameter coordinate converges
  have hth : ∀ s a, ∃ L : ℝ, Tendsto (fun t => (θ t) (s, a)) atTop (nhds L) :=
    fun s a => exists_tendsto_of_summable_increments (hsum s a)
  choose Lth hLth using hth
  -- softmax is continuous in the logits, so each policy coordinate converges
  refine exists_policy_limit_of_coord_tendsto (fun t => F.toPolicy (θ t)) ?_
  intro s a
  refine ⟨softmax (fun a' => Lth s a') a, ?_⟩
  -- softmax is `exp(w a) / ∑ exp(w a')`, continuous since the denominator is positive
  have hnum : Tendsto (fun t => Real.exp ((θ t) (s, a))) atTop
      (nhds (Real.exp (Lth s a))) := (Real.continuous_exp.tendsto _).comp (hLth s a)
  have hden : Tendsto (fun t => ∑ a', Real.exp ((θ t) (s, a'))) atTop
      (nhds (∑ a', Real.exp (Lth s a'))) :=
    tendsto_finsetSum _ (fun a' _ => (Real.continuous_exp.tendsto _).comp (hLth s a'))
  have hdpos : (0:ℝ) < ∑ a', Real.exp (Lth s a') := softmax_denom_pos _
  have hdiv : Tendsto (fun t => Real.exp ((θ t) (s, a)) / ∑ a', Real.exp ((θ t) (s, a')))
      atTop (nhds (Real.exp (Lth s a) / ∑ a', Real.exp (Lth s a'))) :=
    hnum.div hden (ne_of_gt hdpos)
  simpa only [hF, softmax_apply] using hdiv

end Conv

end Proofs
end PolicyGradient
