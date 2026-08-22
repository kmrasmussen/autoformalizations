/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Greedy
import PolicyGradient.Proofs.VecStep

/-!
# Greedy2.lean — `Goal.greedy_limit_points`, PROVED

`Goal.greedy_limit_points` was refuted once and restated. The refuted form
quantified over **all** states; `Proofs.greedy_limit_points_frozen_is_false` in
`Greedy.lean` is the machine-checked counterexample, and its mechanism is the
occupancy factor `d^π_μ(s)` that `dVinfDist_single` puts on every gradient
coordinate: at a state unreachable from `μ` that factor is identically zero, so
the coordinates there never move and ascent cannot constrain `advInf` there at
all. The restatement adds `0 < dinf M πbar μ s`, and this file proves it.

`Greedy.lean` already did most of the work. `greedy_limit_points_reachable`
proves exactly the restated conclusion from three named hypotheses: the policy
limit `hlim`, an occupancy limit `hdlim`, and a vanishing product `hprod`. What
was missing was the derivation of `hdlim` and `hprod` from the frozen goal's
own `hstep` and `hlim`. That is what this file supplies.

## `hprod` — the gradient coordinate IS the product

`Proofs.dVinfDist_single` gives `∂ V_μ / ∂θ(s,a) = d^π_μ(s)·π(a|s)·A^π(s,a)`,
but for `VinfDist` over a start **distribution**, while the frozen goal uses
`Vinf ... μ` for a single start **state**. `dinfDist_pointMass` and
`VinfDist_pointMass` bridge the two, giving `dVinf_single_pointMass`.

A coordinate of a differential is that differential applied to a unit vector, so
`abs_dinf_pi_adv_le_norm_grad` bounds it by `‖∇V(θ_t)‖` through the Riesz
representative. `Proofs.tendsto_norm_grad_zero` sends that norm to `0` along the
frozen recursion (using `Proofs.vec_ascent_step_proof` for the per-step gain), and
a squeeze finishes `hprod`.

## `hdlim` — occupancy is continuous in the POLICY

The repo had `dinf_diff_le` (Lipschitz in the induced **kernel**) but no
policy-space statement — the same gap `Greedy.lean` had to fill for `Vinf`, and
for the same reason: `hlim` is a limit taken in policy space, so a bound in
parameter space says nothing about it. `step_diff_sum_le` converts a uniform
coordinate bound `ε` on two policies into the kernel bound `|S||A|ε` that
`dinf_diff_le` consumes, giving `dinf_policy_lipschitz` and then
`tendsto_dinf_of_tendsto_policy`.

Both pieces are stated for arbitrary policy sequences and are reusable for any
policy-space limit argument, not just this goal.

## Contents

* `dinfDist_pointMass`, `VinfDist_pointMass` — `Dist`-vs-single-state bridge.
* `step_diff_sum_le`, `dinf_policy_lipschitz`, `tendsto_dinf_of_tendsto_policy`
  — continuity of the occupancy in policy space.
* `dVinf_single_pointMass`, `abs_dinf_pi_adv_le_norm_grad` — the policy gradient
  at one coordinate from a single start state, and its bound by the norm.
* `greedy_limit_points_proof` — the frozen goal, at its frozen type.
-/

open Finset Filter

namespace PolicyGradient
namespace Proofs

section Greedy2

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- Point-mass occupancy is single-state occupancy. -/
theorem dinfDist_pointMass (M : FiniteMDP S A) (π : Policy S A) (μ s : S) :
    dinfDist M π (pointMass μ) s = dinf M π μ s := by
  unfold dinfDist
  show ∑ s₀, (if s₀ = μ then (1:ℝ) else 0) * dinf M π s₀ s = _
  rw [Finset.sum_congr rfl (fun s₀ _ => by
    by_cases h : s₀ = μ <;> simp [h] :
    ∀ s₀ ∈ (univ : Finset S), (if s₀ = μ then (1:ℝ) else 0) * dinf M π s₀ s
      = if s₀ = μ then dinf M π μ s else 0)]
  rw [Finset.sum_ite_eq' univ μ]
  simp

/-- Point-mass value is single-state value. -/
theorem VinfDist_pointMass (M : FiniteMDP S A) (π : Policy S A) (μ : S) :
    VinfDist M π (pointMass μ) = Vinf M π μ := by
  unfold VinfDist
  show ∑ s₀, (if s₀ = μ then (1:ℝ) else 0) * Vinf M π s₀ = _
  rw [Finset.sum_congr rfl (fun s₀ _ => by
    by_cases h : s₀ = μ <;> simp [h] :
    ∀ s₀ ∈ (univ : Finset S), (if s₀ = μ then (1:ℝ) else 0) * Vinf M π s₀
      = if s₀ = μ then Vinf M π μ else 0)]
  rw [Finset.sum_ite_eq' univ μ]
  simp

/-! ## Occupancy is continuous in the policy

`dinf_diff_le` bounds `|d^{π'}(s₀,s) - d^{π}(s₀,s)|` by `γK/(1-γ)²` where `K`
bounds the total-variation-style distance `∑_{s'} |step π' - step π|` between
the induced kernels. A uniform coordinate bound `ε` on the policies gives
`K ≤ |S| |A| ε`, since `step M π s₀ s' = ∑ a π(a|s₀) P(s'|s₀,a)` and every
`P(s'|s₀,a) ∈ [0,1]`. -/

/-- A uniform coordinate bound on two policies bounds their induced kernels. -/
theorem step_diff_sum_le (M : FiniteMDP S A) (π π' : Policy S A) (ε : ℝ)
    (hε : ∀ s a, |(π s) a - (π' s) a| ≤ ε) (s₀ : S) :
    ∑ s', |step M π' s₀ s' - step M π s₀ s'| ≤ Fintype.card S * (Fintype.card A * ε) := by
  have hεnn : 0 ≤ ε := le_trans (abs_nonneg _) (hε s₀ (Classical.arbitrary A))
  have hpt : ∀ s', |step M π' s₀ s' - step M π s₀ s'| ≤ Fintype.card A * ε := by
    intro s'
    have hrw : step M π' s₀ s' - step M π s₀ s'
        = ∑ a, ((π' s₀) a - (π s₀) a) * (M.P s₀ a) s' := by
      unfold step
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hrw]
    calc |∑ a, ((π' s₀) a - (π s₀) a) * (M.P s₀ a) s'|
        ≤ ∑ a, |((π' s₀) a - (π s₀) a) * (M.P s₀ a) s'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : A, ε := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [abs_mul]
          have h1 : |(π' s₀) a - (π s₀) a| ≤ ε := by
            rw [abs_sub_comm]; exact hε s₀ a
          have h2 : |(M.P s₀ a) s'| ≤ 1 := by
            rw [abs_of_nonneg ((M.P s₀ a).nonneg s')]
            have := Finset.single_le_sum
              (f := fun x => (M.P s₀ a) x) (fun x _ => (M.P s₀ a).nonneg x) (mem_univ s')
            rw [(M.P s₀ a).sum_eq_one] at this
            exact this
          calc |(π' s₀) a - (π s₀) a| * |(M.P s₀ a) s'|
              ≤ ε * 1 := mul_le_mul h1 h2 (abs_nonneg _) hεnn
            _ = ε := mul_one _
      _ = Fintype.card A * ε := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ∑ s', |step M π' s₀ s' - step M π s₀ s'|
      ≤ ∑ _s' : S, (Fintype.card A * ε) := Finset.sum_le_sum fun s' _ => hpt s'
    _ = Fintype.card S * (Fintype.card A * ε) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`dinf` is Lipschitz in the policy, in the sup-norm.** -/
theorem dinf_policy_lipschitz (M : FiniteMDP S A) (π π' : Policy S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (ε : ℝ)
    (hε : ∀ s a, |(π s) a - (π' s) a| ≤ ε) (s₀ s : S) :
    |dinf M π' s₀ s - dinf M π s₀ s|
      ≤ (M.γ * (Fintype.card S * (Fintype.card A * ε)) / (1 - M.γ)) / (1 - M.γ) := by
  have hεnn : 0 ≤ ε := le_trans (abs_nonneg _) (hε s₀ (Classical.arbitrary A))
  exact dinf_diff_le M π π' hγ₀ hγ₁ _ (by positivity)
    (fun x => step_diff_sum_le M π π' ε hε x) s₀ s

/-- **`dinf` is continuous in the policy.** -/
theorem tendsto_dinf_of_tendsto_policy (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : ℕ → Policy S A) (πbar : Policy S A)
    (hlim : Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a)))
    (s₀ s : S) :
    Tendsto (fun t => dinf M (π t) s₀ s) atTop (nhds (dinf M πbar s₀ s)) := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hcoord : ∀ x a, Tendsto (fun t => (π t x) a) atTop (nhds ((πbar x) a)) := by
    intro x a
    exact (continuous_apply a).continuousAt.tendsto.comp
      ((continuous_apply x).continuousAt.tendsto.comp hlim)
  have hmax : Tendsto (fun t => ∑ x : S, ∑ a : A, |(π t x) a - (πbar x) a|)
      atTop (nhds 0) := by
    have h : Tendsto (fun t => ∑ x : S, ∑ a : A, |(π t x) a - (πbar x) a|)
        atTop (nhds (∑ x : S, ∑ a : A, |(πbar x) a - (πbar x) a|)) :=
      tendsto_finset_sum _ (fun x _ => tendsto_finset_sum _ (fun a _ =>
        continuous_abs.continuousAt.tendsto.comp ((hcoord x a).sub tendsto_const_nhds)))
    simpa using h
  rw [Metric.tendsto_atTop] at hmax ⊢
  intro δ hδ
  set C : ℝ := M.γ * (Fintype.card S * (Fintype.card A : ℝ)) / (1 - M.γ) / (1 - M.γ) + 1
    with hC
  have hCpos : 0 < C := by
    rw [hC]
    have hS : (0:ℝ) < Fintype.card S := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hA : (0:ℝ) < Fintype.card A := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have : (0:ℝ) ≤ M.γ * (Fintype.card S * (Fintype.card A : ℝ)) / (1 - M.γ) / (1 - M.γ) := by
      positivity
    linarith
  obtain ⟨N, hN⟩ := hmax (δ / C) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  rw [Real.dist_eq, sub_zero] at hb
  set ε : ℝ := ∑ x : S, ∑ a : A, |(π n x) a - (πbar x) a| with hεdef
  have hεnn : 0 ≤ ε :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun a _ => abs_nonneg _))
  have hcoordle : ∀ x a, |(π n x) a - (πbar x) a| ≤ ε := by
    intro x a
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun x => ∑ a : A, |(π n x) a - (πbar x) a|)
      (fun x _ => Finset.sum_nonneg (fun a _ => abs_nonneg _)) (mem_univ x))
    exact Finset.single_le_sum (f := fun a => |(π n x) a - (πbar x) a|)
      (fun a _ => abs_nonneg _) (mem_univ a)
  have hL := dinf_policy_lipschitz M πbar (π n) hγ₀ hγ₁ ε
    (fun x a => by rw [abs_sub_comm]; exact hcoordle x a) s₀ s
  have hεb : ε < δ / C := by rwa [abs_of_nonneg hεnn] at hb
  rw [Real.dist_eq]
  have hDle : M.γ * (Fintype.card S * (Fintype.card A * ε)) / (1 - M.γ) / (1 - M.γ)
      ≤ C * ε := by
    rw [hC]
    have : M.γ * (Fintype.card S * (Fintype.card A * ε)) / (1 - M.γ) / (1 - M.γ)
        = (M.γ * (Fintype.card S * (Fintype.card A : ℝ)) / (1 - M.γ) / (1 - M.γ)) * ε := by
      field_simp
    rw [this]
    nlinarith [hεnn]
  calc |dinf M (π n) s₀ s - dinf M πbar s₀ s| ≤ C * ε := le_trans hL hDle
    _ < C * (δ / C) := mul_lt_mul_of_pos_left hεb hCpos
    _ = δ := by field_simp

/-! ## The gradient coordinate is the vanishing product

`dVinfDist_single` says the `(s,a)` coordinate of the differential of
`VinfDist ·  μ` is `d^π_μ(s) · π(a|s) · A^π(s,a)`. With `μ = pointMass μ₀` this
is the single-state form the frozen goal uses. Since the coordinate is the
differential applied to a unit vector, it is bounded in absolute value by the
gradient norm, which `tendsto_norm_grad_zero` sends to `0`. -/

/-- **The tabular softmax policy gradient at one coordinate, single start
state.** `∂ V^{π_θ}(μ) / ∂θ(s,a) = d^{π_θ}_μ(s) · π_θ(a|s) · A^{π_θ}(s,a)`. -/
theorem dVinf_single_pointMass (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : E S A) (s : S) (a : A) :
    fderiv ℝ (fun w => Vinf M (F.toPolicy w) μ) θ (EuclideanSpace.single (s, a) (1:ℝ))
      = dinf M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) := by
  have hfun : (fun w : E S A => Vinf M (F.toPolicy w) μ)
      = fun w : E S A => VinfDist M (F.toPolicy w) (pointMass μ) := by
    funext w; rw [VinfDist_pointMass]
  rw [hfun, (hasFDerivAt_VinfDist M F hF hr hγ₀ hγ₁ (pointMass μ) θ).fderiv,
    dVinfDist_single M F hF hr hγ₀ hγ₁ (pointMass μ) θ s a, dinfDist_pointMass]

/-- **The gradient coordinate is bounded by the gradient norm.** -/
theorem abs_dinf_pi_adv_le_norm_grad (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : E S A) (s : S) (a : A) :
    |dinf M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a)|
      ≤ ‖gradient (fun w => Vinf M (F.toPolicy w) μ) θ‖ := by
  set f : E S A → ℝ := fun w => Vinf M (F.toPolicy w) μ with hf
  set v : E S A := EuclideanSpace.single (s, a) (1:ℝ) with hv
  have hvn : ‖v‖ = 1 := by rw [hv]; simp
  have hinner : (inner ℝ (gradient f θ) v : ℝ) = fderiv ℝ f θ v := inner_gradient_left ..
  have hcoord := dVinf_single_pointMass M F hF hr hγ₀ hγ₁ μ θ s a
  rw [← hf] at hcoord
  rw [← hcoord, ← hinner]
  calc |(inner ℝ (gradient f θ) v : ℝ)| ≤ ‖gradient f θ‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖gradient f θ‖ := by rw [hvn, mul_one]

/-! ## The frozen goal, restated form, PROVED

Everything above assembles into `Goal.greedy_limit_points` in its restated form.

The two hypotheses `greedy_limit_points_reachable` needs beyond `hlim` are
supplied here:

* **`hprod`** — from `tendsto_norm_grad_zero` (the gradient norm vanishes along
  the frozen trajectory, given `vec_ascent_step_proof` for the per-step gain)
  and `abs_dinf_pi_adv_le_norm_grad` (each gradient coordinate IS the product
  `d^{π_t}_μ(s)·π_t(a|s)·A^{π_t}(s,a)` and is bounded by the norm).
* **`hdlim`** — `tendsto_dinf_of_tendsto_policy`: the occupancy is Lipschitz in
  the policy (`dinf_diff_le` composed with `step_diff_sum_le`), so it converges
  along `hlim`.
-/

/-- **`Goal.greedy_limit_points` — proved.**

At every state the limit policy reaches from `μ` with positive occupancy, every
action in `π̄`'s support has zero advantage.

The occupancy hypothesis `0 < dinf M πbar μ s` is not decorative: without it the
statement is FALSE, and `Proofs.greedy_limit_points_frozen_is_false` is the
machine-checked refutation of the previous `∀ s` form. The gradient coordinate
at an unreachable state is identically `0` for every parameter, so gradient
ascent from `μ` cannot constrain `advInf` there at all.

**Proof.** `dVinf_single_pointMass` identifies the `(s,a)` coordinate of
`∇_θ V^{π_θ}(μ)` with `d^{π_θ}_μ(s)·π_θ(a|s)·A^{π_θ}(s,a)`; that coordinate is
bounded by `‖∇V(θ_t)‖`, which `tendsto_norm_grad_zero` sends to `0` along the
frozen recursion `hstep` (whose per-step gain is `vec_ascent_step_proof`). So
the product tends to `0`. Along `hlim` all three factors converge separately —
occupancy by `tendsto_dinf_of_tendsto_policy`, probability by `hlim` itself,
advantage by `tendsto_advInf_of_tendsto_policy` — so the limit product
`d^{π̄}_μ(s)·π̄(a|s)·A^{π̄}(s,a)` is `0` by uniqueness of limits, and with the
first two factors strictly positive the third must vanish. -/
theorem greedy_limit_points_proof (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a))) :
    ∀ s a, 0 < dinf M πbar μ s → 0 < (πbar s) a → advInf M πbar s a = 0 := by
  intro s a hd hπ
  -- the gradient norm vanishes along the frozen recursion
  have hasc : VecAscent M F μ := fun w =>
    vec_ascent_step_proof M F hF hr hγ₀ hγ₁ μ w
  have hgrad : Tendsto (fun t => ‖gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)‖)
      atTop (nhds 0) :=
    tendsto_norm_grad_zero (M := M) F hr hγ₀ hγ₁ μ θ hstep hasc
  -- each gradient coordinate is the product, hence tends to zero
  have hprod : ∀ x b, Tendsto
      (fun t => dinf M (F.toPolicy (θ t)) μ x
        * ((F.toPolicy (θ t) x) b * advInf M (F.toPolicy (θ t)) x b))
      atTop (nhds 0) := by
    intro x b
    refine squeeze_zero_norm (fun t => ?_) hgrad
    rw [Real.norm_eq_abs]
    exact abs_dinf_pi_adv_le_norm_grad M F hF hr hγ₀ hγ₁ μ (θ t) x b
  -- the occupancy converges along `hlim`
  have hdlim : ∀ x, Tendsto (fun t => dinf M (F.toPolicy (θ t)) μ x)
      atTop (nhds (dinf M πbar μ x)) :=
    fun x => tendsto_dinf_of_tendsto_policy M hγ₀ hγ₁
      (fun t => F.toPolicy (θ t)) πbar hlim μ x
  exact greedy_limit_points_reachable M hr hγ₀ hγ₁
    (fun t => F.toPolicy (θ t)) πbar hlim
    (fun t x => dinf M (F.toPolicy (θ t)) μ x) (fun x => dinf M πbar μ x)
    hdlim hprod s a hd hπ

end Greedy2

end Proofs
end PolicyGradient
