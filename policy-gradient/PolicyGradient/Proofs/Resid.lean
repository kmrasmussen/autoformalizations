/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.AKM51b
import PolicyGradient.Proofs.Greedy2
import PolicyGradient.Proofs.DgLip

/-!
# Resid — the residual of AKM Theorem 5.1

Transcription of Akyürek–Kakade–Mahajan (arXiv:1908.00261) **Appendix C.1**, the
proof of their Theorem 5.1 (global convergence of gradient ascent under the
tabular softmax parameterization).

## What the frozen goal needs, and where `hμ` enters

`Goal.limit_adv_nonpos_offsupport` asks for `A^{π̄}(s,a) ≤ 0` at every *off-support*
action of the limit policy. `Goal.lean` records the obstruction precisely: the
gradient limit constrains `A^{π̄}(s,a)` only where `π̄(a|s) > 0`, because
`∂V/∂θ(s,a) = d^π_μ(s)·π(a|s)·A^π(s,a)` and the middle factor vanishes for the
wrong reason. Closing it needs a *rate comparison* between the decay of
`π_t(a|s)` and the advantage — a per-coordinate asymptotic estimate on `θ_t`.

That is exactly what AKM supply, and the strict positivity `hμ : ∀ s, 0 < μ s`
is what makes it possible (their Remark 5.1 leaves convergence open without it).
`hμ` is used here in `state_gain`, via `mu_le_dinfDist`, to make the per-state
gain `μ(s)·(η μ(s)/5)·‖∇F_s‖²` *uniformly positive*; without it that weight is
`0` and the whole chain is vacuous.

## Constants — the two places the goal's hypotheses differ from AKM's

1. **Rewards.** AKM assume `r ∈ [0,1]`, so `|A| ≤ 1/(1-γ)`. The frozen goal
   assumes only `|r| ≤ 1`, so the honest bound is `|A| ≤ 2/(1-γ)`
   (`abs_advInf_le`) — a factor `2` against the step-size budget.
2. **Smoothness constant.** AKM's Lemma E.2 gives `β = 5‖c‖_∞` for the auxiliary
   `F_s`; the repo's `dg_lipschitz` gave only `6‖c‖_∞`.

Both are absorbed by `Proofs.dg_lipschitz4` (`Proofs/DgLip.lean`), which proves
`4‖c‖_∞` — better than AKM's own `5` — by measuring the coefficient vector in
`ℓ²` rather than `ℓ¹`. With `B = 2/(1-γ)` and `L = 4B = 8/(1-γ)`, the effective
step at a state is `c = η·d^π_μ(s) ≤ ((1-γ)²/5)·(1/(1-γ))`, so

  `c · L ≤ 8/5 < 2`,

and `ascent_of_step_le` (which needs only `c·L ≤ 2`, the ascent condition, not
the sharper `c ≤ 1/L`) applies. The margin is genuine but not large: this is why
the exact constant `(1-γ)²/5` in the frozen statement is load-bearing.

## The chain, following AKM's appendix

* `sum_pi_next_adv_nonneg`, `Vinf_step_monotone` — **Lemma C.1**, per-state
  monotone improvement `V^{(t+1)}(s) ≥ V^{(t)}(s)`.
* `exists_Vinf_limit`, `VinfDist_monotone_traj` — **Lemma C.2**, the limits exist.
* `eventually_adv_pos` — **Lemma C.3**, the advantage keeps its sign eventually.
* `state_gain`, `VinfDist_gain`, `tendsto_norm_gradF_zero`, `tendsto_pi_adv_zero`
  — **Lemma C.4**, `π^{(t)}(a|s)·A^{(t)}(s,a) → 0` for every `(s,a)`. This is
  where `hμ` is indispensable.
* `theta_increasing_of_adv_pos`, `theta_eventually_monotone` — **Lemma C.5**.
* `sum_grad_coords_zero`, `sum_theta_const` — **Lemma C.6**, the conservation law
  `∑_a θ^{(t)}(s,a) = const`.
* `tendsto_max_theta_atTop` — **Lemma C.7**, `max_a θ^{(t)}(s,a) → ∞`.
* `stable_step`, `stable_forward` — **Lemma C.10** (`lemma:stable`).

`Proofs/ResidC8.lean` has **Lemma C.8** (`min_a θ^{(t)}(s,a) → -∞`),
`Proofs/ResidC9.lean` has **Lemma C.9** (`θ^{(t)}(s,a) → -∞` for `a ∈ I^s_-`),
and `Proofs/ResidAsm.lean` assembles them.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Resid

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

local notation "E" => EuclideanSpace ℝ (S × A)

/-- The `(s,a)` gradient coordinate of `VinfDist · μ` is
`d^{π_θ}_μ(s) · π_θ(a|s) · A^{π_θ}(s,a)`, bounded by the gradient norm. -/
theorem abs_dinfDist_pi_adv_le_norm_grad (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    |dinfDist M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a)|
      ≤ ‖gradient (fun w => VinfDist M (F.toPolicy w) μ) θ‖ := by
  set f : EuclideanSpace ℝ (S × A) → ℝ := fun w => VinfDist M (F.toPolicy w) μ with hf
  set v : EuclideanSpace ℝ (S × A) := EuclideanSpace.single (s, a) (1:ℝ) with hv
  have hvn : ‖v‖ = 1 := by rw [hv]; simp
  have hinner : (inner ℝ (gradient f θ) v : ℝ) = fderiv ℝ f θ v := inner_gradient_left ..
  have hcoord : fderiv ℝ f θ v
      = dinfDist M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) := by
    rw [hf, (hasFDerivAt_VinfDist M F hF hr hγ₀ hγ₁ μ θ).fderiv,
      dVinfDist_single M F hF hr hγ₀ hγ₁ μ θ s a]
  rw [← hcoord, ← hinner]
  calc |(inner ℝ (gradient f θ) v : ℝ)| ≤ ‖gradient f θ‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖gradient f θ‖ := by rw [hvn, mul_one]

/-! ## AKM Lemma C.1/C.4 for a start **distribution**

`Ginf` is the derivative map of `Vinf M · s₀`; averaging it against `μ` gives the
derivative map of `VinfDist M · μ`, with the same `8/(1-γ)³` Lipschitz constant
(a convex combination of `8/(1-γ)³`-Lipschitz maps). `sharp_descent` then gives
the per-step gain, and square-summability gives `∇ → 0`. -/

/-- The derivative map of `VinfDist M · μ`: the `μ`-average of `Ginf`. -/
noncomputable def GinfDist (M : FiniteMDP S A) (θ : EuclideanSpace ℝ (S × A))
    (μ : Dist S) : EuclideanSpace ℝ (S × A) →L[ℝ] ℝ :=
  ∑ s₀ : S, μ s₀ • Ginf M θ s₀

theorem hasFDeriv_VinfDist_Ginf (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : EuclideanSpace ℝ (S × A)) :
    HasFDerivAt (fun t => VinfDist M (F.toPolicy t) μ) (GinfDist M θ μ) θ := by
  have key : (fun t : EuclideanSpace ℝ (S × A) => VinfDist M (F.toPolicy t) μ)
      = fun t : EuclideanSpace ℝ (S × A) => ∑ s₀ : S, μ s₀ * Vinf M (F.toPolicy t) s₀ := by
    funext t; rfl
  rw [key, GinfDist]
  have : HasFDerivAt (fun t : EuclideanSpace ℝ (S × A) =>
      ∑ s₀ : S, μ s₀ * Vinf M (F.toPolicy t) s₀)
      (∑ s₀ : S, μ s₀ • Ginf M θ s₀) θ := by
    have hfun : (fun t : EuclideanSpace ℝ (S × A) =>
        ∑ s₀ : S, μ s₀ * Vinf M (F.toPolicy t) s₀)
        = ∑ s₀ : S, (fun t : EuclideanSpace ℝ (S × A) => μ s₀ * Vinf M (F.toPolicy t) s₀) := by
      funext t; simp
    rw [hfun]
    exact HasFDerivAt.sum fun s₀ _ =>
      ((hasFDeriv_Vinf M F hF hr hγ₀ hγ₁ θ s₀).const_mul (μ s₀))
  exact this

theorem GinfDist_lipschitz (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ₁ θ₂ : EuclideanSpace ℝ (S × A)) :
    ‖GinfDist M θ₁ μ - GinfDist M θ₂ μ‖ ≤ 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hsub : GinfDist M θ₁ μ - GinfDist M θ₂ μ
      = ∑ s₀ : S, μ s₀ • (Ginf M θ₁ s₀ - Ginf M θ₂ s₀) := by
    rw [GinfDist, GinfDist, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s₀ _ => by rw [smul_sub]
  rw [hsub]
  calc ‖∑ s₀ : S, μ s₀ • (Ginf M θ₁ s₀ - Ginf M θ₂ s₀)‖
      ≤ ∑ s₀ : S, ‖μ s₀ • (Ginf M θ₁ s₀ - Ginf M θ₂ s₀)‖ := norm_sum_le _ _
    _ ≤ ∑ s₀ : S, μ s₀ * (8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖) := by
        refine Finset.sum_le_sum fun s₀ _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg s₀)]
        exact mul_le_mul_of_nonneg_left
          (Ginf_lipschitz M hr hγ₀ hγ₁ θ₁ θ₂ s₀) (μ.nonneg s₀)
    _ = 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
        rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]

/-! ## AKM Lemma C.1 — per-state monotone improvement

AKM's key auxiliary function is `F_s(θ_s) = ∑_a π_θ(a|s) c(s,a)` with `c` frozen
at `A^{(t)}(s,·)`. Its gradient at `θ^{(t)}` is `π^{(t)}(a|s) A^{(t)}(s,a)`
(because `∑_a π^{(t)}(a|s) A^{(t)}(s,a) = 0`), which is exactly the ascent
direction up to the positive scalar `d^{π^{(t)}}_μ(s)`. Smoothness of `F_s` with
a step below `1/β` then gives `F_s(θ^{(t+1)}) ≥ F_s(θ^{(t)})`, i.e.
`∑_a π^{(t+1)}(a|s) A^{(t)}(s,a) ≥ 0`, and the performance-difference lemma turns
that into `V^{(t+1)}(s) ≥ V^{(t)}(s)` at every state. -/

/-- `g s q` is the AKM auxiliary function `F_s`, and `dg` is its derivative. -/
theorem g_eq_sum_pi (s : S) (q : A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : EuclideanSpace ℝ (S × A)) :
    g (S := S) (A := A) s q θ = ∑ a, (F.toPolicy θ s) a * q a := by
  unfold g
  exact Finset.sum_congr rfl fun a _ => by rw [hF]

/-- At `θ`, with `q = A^{π_θ}(s,·)`, the derivative `dg` acts on a coordinate as
`π_θ(a|s) · A^{π_θ}(s,a)` — AKM equation (C.3). -/
theorem dg_adv_single (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    dg (S := S) (A := A) s (fun a' => advInf M (F.toPolicy θ) s a') θ
        (EuclideanSpace.single (s, a) (1:ℝ))
      = (F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a := by
  rw [dg_single]
  have hzero : ∑ a', (softmax fun a'' => θ (s, a'')) a' * advInf M (F.toPolicy θ) s a' = 0 := by
    have := sum_pi_advInf_self M hr hγ₀ hγ₁ (F.toPolicy θ) s
    rw [← this]
    exact Finset.sum_congr rfl fun a' _ => by rw [hF]
  rw [hzero, sub_zero, hF]
  simp

/-- **AKM Lemma C.1, abstract core.** If `f` has `L`-Lipschitz derivative map `G`
and we move from `x` by `c • v` where `v` is the Riesz representative of `G x`
(here supplied as the hypothesis `hGv`), with `0 ≤ c ≤ 1/L`, then `f` increases.

This is `sharp_descent` specialized: the gain is `c‖G x‖² - (L/2)c²‖G x‖²
= c(1 - cL/2)‖G x‖² ≥ 0` whenever `0 ≤ c ≤ 2/L`. -/
theorem ascent_of_step_le {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {f : E' → ℝ} {G : E' → E' →L[ℝ] ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x, HasFDerivAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (x v : E') (c : ℝ) (hc₀ : 0 ≤ c) (hcL : c * L ≤ 2)
    (hGv : G x v = ‖v‖ ^ 2) :
    f x ≤ f (x + c • v) := by
  have key := sharp_descent hL hd hlip x (c • v)
  have h1 : G x (c • v) = c * ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.map_smul, hGv]; simp [smul_eq_mul]
  have h2 : ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h1, h2] at key
  have hgain : 0 ≤ c * ‖v‖ ^ 2 - L / 2 * (c ^ 2 * ‖v‖ ^ 2) := by
    have : c * ‖v‖ ^ 2 - L / 2 * (c ^ 2 * ‖v‖ ^ 2)
        = (c * ‖v‖ ^ 2) * (1 - c * L / 2) := by ring
    rw [this]
    have hnn : 0 ≤ c * ‖v‖ ^ 2 := mul_nonneg hc₀ (sq_nonneg _)
    nlinarith [hnn, hcL]
  linarith [key, hgain]

/-! ### The ascent direction, restricted to one state's block

`GinfDist M θ μ` is `∑_s dinfDist(s) • dg s (Q^π(s,·)) θ` (this is `dVinfDist`,
identified with `GinfDist` by uniqueness of the derivative). Since `dg s · θ` is
supported on state `s`'s coordinate block, and `dg` is invariant under shifting
`q` by a constant (`dg_sub_const`), the `s`-block of the ascent direction is
`dinfDist(s) • dg s (A^π(s,·)) θ`. -/

theorem GinfDist_eq_dVinfDist (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : EuclideanSpace ℝ (S × A)) :
    GinfDist M θ μ = dVinfDist M (F.toPolicy θ) μ θ :=
  (hasFDeriv_VinfDist_Ginf M F hF hr hγ₀ hγ₁ μ θ).unique
    (hasFDerivAt_VinfDist M F hF hr hγ₀ hγ₁ μ θ)

/-- The gradient of `VinfDist` is the Riesz representative of `dVinfDist`. -/
theorem gradient_VinfDist_apply (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    (gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a)
      = dinfDist M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) := by
  set f : EuclideanSpace ℝ (S × A) → ℝ := fun w => VinfDist M (F.toPolicy w) μ with hf
  set v : EuclideanSpace ℝ (S × A) := EuclideanSpace.single (s, a) (1:ℝ) with hv
  have hinner : (inner ℝ (gradient f θ) v : ℝ) = fderiv ℝ f θ v := inner_gradient_left ..
  have hcoord : fderiv ℝ f θ v
      = dinfDist M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) := by
    rw [hf, (hasFDerivAt_VinfDist M F hF hr hγ₀ hγ₁ μ θ).fderiv,
      dVinfDist_single M F hF hr hγ₀ hγ₁ μ θ s a]
  rw [← hcoord, ← hinner, hv]
  rw [EuclideanSpace.inner_single_right]
  simp

/-! ### AKM Lemma C.1: `∑_a π^{(t+1)}(a|s) A^{(t)}(s,a) ≥ 0`

The `θ`-step is `θ' = θ + η • ∇VinfDist`. Restricted to state `s`'s block the
increment is `η · d^{π_θ}_μ(s) · (π_θ(a|s) A^{π_θ}(s,a))_a`, which is
`η · d^{π_θ}_μ(s)` times the gradient of `F_s = g s (A^{π_θ}(s,·))`. Because
`g s q` depends only on the `s`-block, the other blocks of the step are
irrelevant to `F_s`, and `ascent_of_step_le` applies with
`c = η · d^{π_θ}_μ(s)` and `L = C/(1-γ)`. -/

/-- The `s`-block of `η • ∇VinfDist` equals `(η · d(s)) •` the Riesz vector of
`dg s (A(s,·)) θ` — expressed coordinatewise. -/
theorem grad_block_eq (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    (gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a)
      = dinfDist M (F.toPolicy θ) μ s
          * ((gradient (g (S := S) (A := A) s
                (fun a' => advInf M (F.toPolicy θ) s a')) θ) (s, a)) := by
  rw [gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ θ s a]
  congr 1
  set q : A → ℝ := fun a' => advInf M (F.toPolicy θ) s a' with hq
  set v : EuclideanSpace ℝ (S × A) := EuclideanSpace.single (s, a) (1:ℝ) with hv
  have hinner : (inner ℝ (gradient (g (S := S) (A := A) s q) θ) v : ℝ)
      = fderiv ℝ (g (S := S) (A := A) s q) θ v := inner_gradient_left ..
  have hfd : fderiv ℝ (g (S := S) (A := A) s q) θ = dg (S := S) (A := A) s q θ :=
    (hasFDeriv_g (S := S) (A := A) s q θ).fderiv
  have hcoord : dg (S := S) (A := A) s q θ v
      = (F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a :=
    dg_adv_single M F hF hr hγ₀ hγ₁ θ s a
  rw [hfd, hcoord] at hinner
  rw [← hinner, hv, EuclideanSpace.inner_single_right]
  simp

/-! ### AKM Lemma C.1: `∑_a π^{(t+1)}(a|s) A^{(t)}(s,a) ≥ 0`

`F_s := g s (A^{π_θ}(s,·))` has derivative map `dg s (A^{π_θ}(s,·))`, which is
`4B`-Lipschitz with `B = 2/(1-γ)` (`dg_lipschitz4`, `abs_advInf_le`), i.e.
`L = 8/(1-γ)`. The `θ`-step's `s`-block is `η·d^{π_θ}_μ(s)` times the Riesz
vector of that derivative (`grad_block_eq`), and

`η · d^{π_θ}_μ(s) · L ≤ ((1-γ)²/5) · (1/(1-γ)) · (8/(1-γ)) = 8/5 ≤ 2`,

so `ascent_of_step_le` applies. This is where `η ≤ (1-γ)²/5` is used, and the
margin is genuine: `8/5 < 2`. -/

/-- The Riesz vector of `dg s q θ` is supported on state `s`'s block: it agrees
with `∇(g s q)` there and vanishes elsewhere, so adding a multiple of it to `θ`
changes no other state's block. -/
theorem gradient_g_off_block (s x : S) (q : A → ℝ) (θ : EuclideanSpace ℝ (S × A))
    (a : A) (hx : x ≠ s) :
    (gradient (g (S := S) (A := A) s q) θ) (x, a) = 0 := by
  set v : EuclideanSpace ℝ (S × A) := EuclideanSpace.single (x, a) (1:ℝ) with hv
  have hinner : (inner ℝ (gradient (g (S := S) (A := A) s q) θ) v : ℝ)
      = fderiv ℝ (g (S := S) (A := A) s q) θ v := inner_gradient_left ..
  have hfd : fderiv ℝ (g (S := S) (A := A) s q) θ = dg (S := S) (A := A) s q θ :=
    (hasFDeriv_g (S := S) (A := A) s q θ).fderiv
  have hz : dg (S := S) (A := A) s q θ v = 0 := by
    rw [hv, dg_single]; exact if_neg (Ne.symm hx)
  rw [hfd, hz] at hinner
  rw [← hinner, hv, EuclideanSpace.inner_single_right]
  simp

/-- `g s q` depends only on state `s`'s coordinate block. -/
theorem g_congr_block (s : S) (q : A → ℝ) (θ₁ θ₂ : EuclideanSpace ℝ (S × A))
    (h : ∀ a, θ₁ (s, a) = θ₂ (s, a)) :
    g (S := S) (A := A) s q θ₁ = g (S := S) (A := A) s q θ₂ := by
  unfold g
  have : (fun a' => θ₁ (s, a')) = fun a' => θ₂ (s, a') := funext h
  rw [this]

/-- **AKM Lemma C.1 (the `F_s` half).**
`∑_a π^{(t+1)}(a|s) A^{(t)}(s,a) ≥ ∑_a π^{(t)}(a|s) A^{(t)}(s,a) = 0`. -/
theorem sum_pi_next_adv_nonneg (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) :
    0 ≤ ∑ a, (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) s) a
          * advInf M (F.toPolicy θ) s a := by
  have hpos : 0 < 1 - M.γ := by linarith
  set q : A → ℝ := fun a' => advInf M (F.toPolicy θ) s a' with hq
  set B : ℝ := 2 / (1 - M.γ) with hB
  have hqB : ∀ a, |q a| ≤ B := fun a => abs_advInf_le M (F.toPolicy θ) hr hγ₀ hγ₁ s a
  set L : ℝ := 4 * B with hL
  have hLnn : 0 ≤ L := by rw [hL, hB]; positivity
  -- the derivative map of `F_s = g s q` is `L`-Lipschitz
  have hd : ∀ x, HasFDerivAt (g (S := S) (A := A) s q) (dg (S := S) (A := A) s q x) x :=
    fun x => hasFDeriv_g (S := S) (A := A) s q x
  have hlip : ∀ x y, ‖dg (S := S) (A := A) s q x - dg (S := S) (A := A) s q y‖
      ≤ L * ‖x - y‖ := fun x y => dg_lipschitz4 s q B hqB x y
  -- the step scalar
  set c : ℝ := η * dinfDist M (F.toPolicy θ) μ s with hc
  have hdnn : 0 ≤ dinfDist M (F.toPolicy θ) μ s := dinfDist_nonneg M hγ₀ _ _ _
  have hc₀ : 0 ≤ c := mul_nonneg (le_of_lt hη₀) hdnn
  -- `d ≤ 1/(1-γ)`
  have hdle : dinfDist M (F.toPolicy θ) μ s ≤ 1 / (1 - M.γ) := by
    unfold dinfDist
    calc ∑ s₀, μ s₀ * dinf M (F.toPolicy θ) s₀ s
        ≤ ∑ s₀, μ s₀ * (1 / (1 - M.γ)) :=
          Finset.sum_le_sum fun s₀ _ =>
            mul_le_mul_of_nonneg_left (dinf_le_one_div M hγ₀ hγ₁ _ _ _) (μ.nonneg s₀)
      _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]
  -- `c * L ≤ 8/5 ≤ 2`
  have hcL : c * L ≤ 2 := by
    have h1 : c ≤ (1 - M.γ) ^ 2 / 5 * (1 / (1 - M.γ)) := by
      rw [hc]
      exact mul_le_mul hη hdle hdnn (by positivity)
    have h2 : (1 - M.γ) ^ 2 / 5 * (1 / (1 - M.γ)) = (1 - M.γ) / 5 := by
      field_simp
    rw [h2] at h1
    have hLeq : L = 8 / (1 - M.γ) := by rw [hL, hB]; field_simp; ring
    rw [hLeq]
    calc c * (8 / (1 - M.γ)) ≤ ((1 - M.γ) / 5) * (8 / (1 - M.γ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 8 / 5 := by field_simp
      _ ≤ 2 := by norm_num
  -- the Riesz vector of the `F_s` derivative
  set v : EuclideanSpace ℝ (S × A) := gradient (g (S := S) (A := A) s q) θ with hv
  have hGv : dg (S := S) (A := A) s q θ v = ‖v‖ ^ 2 := by
    have h := inner_gradient_left (𝕜 := ℝ) (f := g (S := S) (A := A) s q) (x := θ) (y := v)
    rw [(hasFDeriv_g (S := S) (A := A) s q θ).fderiv] at h
    rw [← h, hv, real_inner_self_eq_norm_sq]
  -- ascent on `F_s`
  have hasc := ascent_of_step_le hLnn hd hlip θ v c hc₀ hcL hGv
  -- the actual step agrees with `θ + c • v` on block `s`
  have hblock : ∀ a,
      (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a)
        = (θ + c • v) (s, a) := by
    intro a
    have hg := grad_block_eq M F hF hr hγ₀ hγ₁ μ θ s a
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hg, hv, hc]
    ring
  have hgeq : g (S := S) (A := A) s q
        (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ)
      = g (S := S) (A := A) s q (θ + c • v) := g_congr_block s q _ _ hblock
  -- translate `F_s(θ) ≤ F_s(step)` into the sum form
  have hzero : g (S := S) (A := A) s q θ = 0 := by
    rw [g_eq_sum_pi s q F hF θ]
    exact sum_pi_advInf_self M hr hγ₀ hγ₁ (F.toPolicy θ) s
  have hfin : g (S := S) (A := A) s q
      (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ)
      = ∑ a, (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) s) a
          * advInf M (F.toPolicy θ) s a := g_eq_sum_pi s q F hF _
  rw [← hfin, hgeq]
  linarith [hasc, hzero]

/-- **AKM Lemma C.1.** `V^{(t+1)}(s) ≥ V^{(t)}(s)` at **every** state.

The performance-difference lemma writes the gap as
`∑_{s'} d^{π^{(t+1)}}(s,s') ∑_a π^{(t+1)}(a|s') A^{(t)}(s',a)`, and every inner
sum is `≥ 0` by `sum_pi_next_adv_nonneg`, with the occupancy weights `≥ 0`. -/
theorem Vinf_step_monotone (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : EuclideanSpace ℝ (S × A)) (s₀ : S) :
    Vinf M (F.toPolicy θ) s₀
      ≤ Vinf M (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ)) s₀ := by
  set θ' : EuclideanSpace ℝ (S × A) :=
    θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ with hθ'
  have hpd := perfDiffInf M (F.toPolicy θ) (F.toPolicy θ') hr hγ₀ hγ₁ s₀
  have hnn : 0 ≤ pdInf M (F.toPolicy θ) (F.toPolicy θ') s₀ := by
    unfold pdInf
    refine Finset.sum_nonneg fun s _ => ?_
    refine mul_nonneg (dinf_nonneg M hγ₀ _ _ _) ?_
    unfold advGapInf
    exact sum_pi_next_adv_nonneg M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ s
  linarith [hpd, hnn]

/-! ## AKM Lemma C.2 and the limiting sets

Along the trajectory `θ`, `hlim` gives `π^{(t)} → π̄` in policy space, so by
continuity of `advInf` (`tendsto_advInf_of_tendsto_policy`) we get
`A^{(t)}(s,a) → A^{π̄}(s,a)`. Hence AKM's `A^{(∞)}` **is** `advInf M π̄`, and
their sets are

* `I^s_+ = {a | A^{π̄}(s,a) > 0}`, `I^s_0 = {a | A^{π̄}(s,a) = 0}`,
  `I^s_- = {a | A^{π̄}(s,a) < 0}`.

The goal `∀ s a, π̄(a|s) = 0 → A^{π̄}(s,a) ≤ 0` says exactly: **no action in
`I^s_+` is off-support.** AKM prove the stronger `I^s_+ = ∅`. -/

/-- The trajectory's advantages converge to `π̄`'s. -/
theorem tendsto_adv_traj (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) :
    Filter.Tendsto (fun t => advInf M (F.toPolicy (θ t)) s a) Filter.atTop
      (nhds (advInf M πbar s a)) :=
  tendsto_advInf_of_tendsto_policy M hr hγ₀ hγ₁ (fun t => F.toPolicy (θ t)) πbar hlim s a

/-- **AKM Lemma C.2.** The value at each state converges (monotone + bounded). -/
theorem exists_Vinf_limit (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s₀ : S) :
    Monotone (fun t => Vinf M (F.toPolicy (θ t)) s₀) := by
  refine monotone_nat_of_le_succ fun t => ?_
  have h := Vinf_step_monotone M F hF hr hγ₀ hγ₁ μ η hη₀ hη (θ t) s₀
  rw [← hstep t] at h
  exact h

/-! ## AKM Lemma C.4: the gradient vanishes, hence `π^{(t)}(a|s) → 0` off `I^s_0`

`VinfDist` has an `8/(1-γ)³`-Lipschitz derivative map (`GinfDist_lipschitz`), so
a step of size `η ≤ (1-γ)²/5` gains at least `η(1 - ηL/2)‖∇‖²`. Here
`ηL/2 ≤ ((1-γ)²/5)(4/(1-γ)³) = 4/(5(1-γ))`, which **exceeds 1** for `γ > 1/5` —
so the naive gain is not positive, and the value-ascent route on `VinfDist`
with this `L` does not by itself give square-summable gradients.

Instead we use the per-state monotonicity already proved: `VinfDist` is monotone
along the trajectory (average of monotone `Vinf`) and bounded, hence convergent.
That gives convergence of the objective but **not** `∇ → 0` without a gain
inequality. -/

/-- `VinfDist` is monotone along the trajectory. -/
theorem VinfDist_monotone_traj (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t)) :
    Monotone (fun t => VinfDist M (F.toPolicy (θ t)) μ) := by
  refine monotone_nat_of_le_succ fun t => ?_
  unfold VinfDist
  refine Finset.sum_le_sum fun s₀ _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (μ.nonneg s₀)
  exact exists_Vinf_limit M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep s₀ (Nat.le_succ t)

/-! ### A *quantified* per-state gain

`ascent_of_step_le` discarded the gain. Keeping it gives, at each state `s`,

`F_s(θ^{(t+1)}) ≥ c(1 - cL/2)‖∇F_s(θ^{(t)})‖²`  with `c = η d^{(t)}_μ(s)`,

and `cL ≤ 8/5` makes `1 - cL/2 ≥ 1/5`. Since `‖∇F_s(θ)‖² = ∑_a (π(a|s)A(s,a))²`,
this lower-bounds the per-state advantage-weighted mass. Combined with the
performance-difference lemma and `μ(s) > 0`, the telescoped sum of these gains is
finite, forcing `π^{(t)}(a|s) A^{(t)}(s,a) → 0` for every `s, a`. -/

/-- `ascent_of_step_le` with the gain retained. -/
theorem ascent_gain {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    {f : E' → ℝ} {G : E' → E' →L[ℝ] ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x, HasFDerivAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (x v : E') (c : ℝ)
    (hGv : G x v = ‖v‖ ^ 2) :
    f x + c * (1 - c * L / 2) * ‖v‖ ^ 2 ≤ f (x + c • v) := by
  have key := sharp_descent hL hd hlip x (c • v)
  have h1 : G x (c • v) = c * ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.map_smul, hGv]; simp [smul_eq_mul]
  have h2 : ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h1, h2] at key
  have harith : c * ‖v‖ ^ 2 - L / 2 * (c ^ 2 * ‖v‖ ^ 2)
      = c * (1 - c * L / 2) * ‖v‖ ^ 2 := by ring
  linarith [key, harith.symm.le, harith.le]

/-- The squared norm of the `F_s` gradient is `∑_a (π(a|s) A(s,a))²`. -/
theorem norm_sq_gradient_g (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) :
    ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) ^ 2
      ≤ ‖gradient (g (S := S) (A := A) s
            (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2 := by
  set q : A → ℝ := fun a' => advInf M (F.toPolicy θ) s a' with hq
  set w : EuclideanSpace ℝ (S × A) := gradient (g (S := S) (A := A) s q) θ with hw
  have hcoord : w (s, a) = (F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a := by
    have hinner : (inner ℝ w (EuclideanSpace.single (s, a) (1:ℝ)) : ℝ)
        = fderiv ℝ (g (S := S) (A := A) s q) θ (EuclideanSpace.single (s, a) (1:ℝ)) :=
      inner_gradient_left ..
    rw [(hasFDeriv_g (S := S) (A := A) s q θ).fderiv,
      dg_adv_single M F hF hr hγ₀ hγ₁ θ s a] at hinner
    rw [← hinner, EuclideanSpace.inner_single_right]
    simp
  rw [← hcoord]
  have := EuclideanSpace.norm_eq w
  have hle : w (s, a) ^ 2 ≤ ∑ p : S × A, w p ^ 2 := by
    refine Finset.single_le_sum (f := fun p : S × A => w p ^ 2)
      (fun p _ => sq_nonneg _) (Finset.mem_univ (s, a))
  have hnorm : ‖w‖ ^ 2 = ∑ p : S × A, w p ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt
      (Finset.sum_nonneg fun p _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun p _ => by rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  exact hle

/-! ### From the per-state gain to `π^{(t)}(a|s) A^{(t)}(s,a) → 0`

At state `s`, `sum_pi_next_adv_nonneg`'s proof produced a *gain*: with
`c_t = η d^{(t)}_μ(s)` and `L = 8/(1-γ)`,

`∑_a π^{(t+1)}(a|s) A^{(t)}(s,a) ≥ c_t (1 - c_t L/2) ‖∇F_s(θ^{(t)})‖² ≥ 0`,

and `c_t L ≤ 8/5` gives `1 - c_t L/2 ≥ 1/5`. Now `hμ` enters: `d^{(t)}_μ(s) ≥ μ(s) > 0`
(`mu_le_dinfDist`), so `c_t ≥ η μ(s) > 0` and the gain is at least
`(η μ(s)/5)‖∇F_s(θ^{(t)})‖²`.

Feeding this through the performance-difference lemma at start distribution `μ`,
`V^{(t+1)}(μ) - V^{(t)}(μ) ≥ (1-γ)μ(s) · (η μ(s)/5) ‖∇F_s(θ^{(t)})‖²`
(the occupancy weight `d^{π^{(t+1)}}_μ(s) ≥ μ(s)`), and `V(μ)` is bounded, so
the gains are summable and `‖∇F_s(θ^{(t)})‖ → 0`. -/

/-- **The per-state gain, with `hμ` making it uniformly positive.** -/
theorem state_gain (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) :
    η * μ s / 5
        * ‖gradient (g (S := S) (A := A) s
              (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2
      ≤ ∑ a, (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) s) a
          * advInf M (F.toPolicy θ) s a := by
  have hpos : 0 < 1 - M.γ := by linarith
  set q : A → ℝ := fun a' => advInf M (F.toPolicy θ) s a' with hq
  set B : ℝ := 2 / (1 - M.γ) with hB
  have hqB : ∀ a, |q a| ≤ B := fun a => abs_advInf_le M (F.toPolicy θ) hr hγ₀ hγ₁ s a
  set L : ℝ := 4 * B with hL
  have hLeq : L = 8 / (1 - M.γ) := by rw [hL, hB]; field_simp; ring
  have hLnn : 0 ≤ L := by rw [hLeq]; positivity
  have hd : ∀ x, HasFDerivAt (g (S := S) (A := A) s q) (dg (S := S) (A := A) s q x) x :=
    fun x => hasFDeriv_g (S := S) (A := A) s q x
  have hlip : ∀ x y, ‖dg (S := S) (A := A) s q x - dg (S := S) (A := A) s q y‖
      ≤ L * ‖x - y‖ := fun x y => dg_lipschitz4 s q B hqB x y
  set c : ℝ := η * dinfDist M (F.toPolicy θ) μ s with hc
  have hdnn : 0 ≤ dinfDist M (F.toPolicy θ) μ s := dinfDist_nonneg M hγ₀ _ _ _
  have hc₀ : 0 ≤ c := mul_nonneg (le_of_lt hη₀) hdnn
  have hdle : dinfDist M (F.toPolicy θ) μ s ≤ 1 / (1 - M.γ) := by
    unfold dinfDist
    calc ∑ s₀, μ s₀ * dinf M (F.toPolicy θ) s₀ s
        ≤ ∑ s₀, μ s₀ * (1 / (1 - M.γ)) :=
          Finset.sum_le_sum fun s₀ _ =>
            mul_le_mul_of_nonneg_left (dinf_le_one_div M hγ₀ hγ₁ _ _ _) (μ.nonneg s₀)
      _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]
  have hcL : c * L ≤ 8 / 5 := by
    have h1 : c ≤ (1 - M.γ) ^ 2 / 5 * (1 / (1 - M.γ)) := by
      rw [hc]; exact mul_le_mul hη hdle hdnn (by positivity)
    have h2 : (1 - M.γ) ^ 2 / 5 * (1 / (1 - M.γ)) = (1 - M.γ) / 5 := by field_simp
    rw [h2] at h1
    rw [hLeq]
    calc c * (8 / (1 - M.γ)) ≤ ((1 - M.γ) / 5) * (8 / (1 - M.γ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 8 / 5 := by field_simp
  -- `hμ` gives the lower bound on `c`
  have hcμ : η * μ s ≤ c := by
    rw [hc]
    exact mul_le_mul_of_nonneg_left (mu_le_dinfDist M hγ₀ hγ₁ _ μ s) (le_of_lt hη₀)
  set v : EuclideanSpace ℝ (S × A) := gradient (g (S := S) (A := A) s q) θ with hv
  have hGv : dg (S := S) (A := A) s q θ v = ‖v‖ ^ 2 := by
    have h := inner_gradient_left (𝕜 := ℝ) (f := g (S := S) (A := A) s q) (x := θ) (y := v)
    rw [(hasFDeriv_g (S := S) (A := A) s q θ).fderiv] at h
    rw [← h, hv, real_inner_self_eq_norm_sq]
  have hgain := ascent_gain hLnn hd hlip θ v c hGv
  -- the actual step agrees with `θ + c • v` on block `s`
  have hblock : ∀ a,
      (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a)
        = (θ + c • v) (s, a) := by
    intro a
    have hg := grad_block_eq M F hF hr hγ₀ hγ₁ μ θ s a
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [hg, hv, hc]; ring
  have hgeq : g (S := S) (A := A) s q
        (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ)
      = g (S := S) (A := A) s q (θ + c • v) := g_congr_block s q _ _ hblock
  have hzero : g (S := S) (A := A) s q θ = 0 := by
    rw [g_eq_sum_pi s q F hF θ]
    exact sum_pi_advInf_self M hr hγ₀ hγ₁ (F.toPolicy θ) s
  have hfin : g (S := S) (A := A) s q
      (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ)
      = ∑ a, (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) s) a
          * advInf M (F.toPolicy θ) s a := g_eq_sum_pi s q F hF _
  rw [← hfin, hgeq]
  -- `c (1 - cL/2) ≥ (η μ s) · (1/5)`
  have hfac : η * μ s / 5 ≤ c * (1 - c * L / 2) := by
    have hone : (1:ℝ) / 5 ≤ 1 - c * L / 2 := by linarith [hcL]
    have hημ : 0 ≤ η * μ s := mul_nonneg (le_of_lt hη₀) (le_of_lt (hμ s))
    calc η * μ s / 5 = (η * μ s) * (1/5) := by ring
      _ ≤ c * (1 - c * L / 2) := by
          refine mul_le_mul hcμ hone (by norm_num) hc₀
  have hvsq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  nlinarith [hgain, hzero, hfac, hvsq]

/-- **The objective's per-step gain, in terms of one state's `F_s` gradient.**

Performance difference at start distribution `μ` gives
`V^{(t+1)}(μ) - V^{(t)}(μ) = ∑_{s'} d^{π^{(t+1)}}_μ(s') ∑_a π^{(t+1)}(a|s') A^{(t)}(s',a)`.
Every summand is `≥ 0` (`sum_pi_next_adv_nonneg`), so dropping all but `s'=s` and
using `d^{π^{(t+1)}}_μ(s) ≥ μ(s)` (`mu_le_dinfDist`) with `state_gain` gives the
claim. -/
theorem VinfDist_gain (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) :
    VinfDist M (F.toPolicy θ) μ
        + μ s * (η * μ s / 5)
          * ‖gradient (g (S := S) (A := A) s
                (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2
      ≤ VinfDist M (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ)) μ := by
  set θ' : EuclideanSpace ℝ (S × A) :=
    θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ with hθ'
  -- performance difference, averaged over `μ`
  have hpd : VinfDist M (F.toPolicy θ') μ - VinfDist M (F.toPolicy θ) μ
      = ∑ s₀, μ s₀ * pdInf M (F.toPolicy θ) (F.toPolicy θ') s₀ := by
    unfold VinfDist
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s₀ _ => ?_
    rw [← mul_sub, perfDiffInf M (F.toPolicy θ) (F.toPolicy θ') hr hγ₀ hγ₁ s₀]
  -- reorganize as `∑_{s'} dinfDist(s') * advGapInf(s')`
  have hswap : ∑ s₀, μ s₀ * pdInf M (F.toPolicy θ) (F.toPolicy θ') s₀
      = ∑ s', dinfDist M (F.toPolicy θ') μ s'
          * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s' := by
    unfold pdInf dinfDist
    have hL : ∀ s₀ : S, μ s₀ * ∑ s', dinf M (F.toPolicy θ') s₀ s'
          * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s'
        = ∑ s', μ s₀ * dinf M (F.toPolicy θ') s₀ s'
          * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s' := by
      intro s₀; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s' _ => by ring
    rw [Finset.sum_congr rfl (fun s₀ _ => hL s₀), Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [Finset.sum_mul]
  -- each term is nonneg; keep only `s'= s`
  have hterm : ∀ s', 0 ≤ dinfDist M (F.toPolicy θ') μ s'
      * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s' := by
    intro s'
    refine mul_nonneg (dinfDist_nonneg M hγ₀ _ _ _) ?_
    unfold advGapInf
    exact sum_pi_next_adv_nonneg M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ s'
  have hsingle : dinfDist M (F.toPolicy θ') μ s
        * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s
      ≤ ∑ s', dinfDist M (F.toPolicy θ') μ s'
          * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s' :=
    Finset.single_le_sum (fun s' _ => hterm s') (Finset.mem_univ s)
  -- lower-bound that single term
  have hgs : η * μ s / 5
      * ‖gradient (g (S := S) (A := A) s
            (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2
      ≤ advGapInf M (F.toPolicy θ) (F.toPolicy θ') s :=
    state_gain M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ s
  have hdμ : μ s ≤ dinfDist M (F.toPolicy θ') μ s := mu_le_dinfDist M hγ₀ hγ₁ _ μ s
  have hgnn : 0 ≤ η * μ s / 5
      * ‖gradient (g (S := S) (A := A) s
            (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2 := by
    have : 0 ≤ η * μ s / 5 := by
      have := (hμ s); positivity
    exact mul_nonneg this (sq_nonneg _)
  have hlow : μ s * (η * μ s / 5)
      * ‖gradient (g (S := S) (A := A) s
            (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2
      ≤ dinfDist M (F.toPolicy θ') μ s
        * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s := by
    have h1 : μ s * (η * μ s / 5
        * ‖gradient (g (S := S) (A := A) s
              (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2)
        ≤ dinfDist M (F.toPolicy θ') μ s
          * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s :=
      mul_le_mul hdμ hgs hgnn (dinfDist_nonneg M hγ₀ _ _ _)
    calc μ s * (η * μ s / 5)
          * ‖gradient (g (S := S) (A := A) s
                (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2
        = μ s * (η * μ s / 5
            * ‖gradient (g (S := S) (A := A) s
                  (fun a' => advInf M (F.toPolicy θ) s a')) θ‖ ^ 2) := by ring
      _ ≤ _ := h1
  linarith [hpd, hswap, hsingle, hlow]

/-- **AKM Lemma C.4 (gradient half).** `‖∇F_s(θ^{(t)})‖ → 0` at every state.

The gains of `VinfDist_gain` telescope against the bound `V(μ) ≤ 1/(1-γ)`, so
`∑_t ‖∇F_s(θ^{(t)})‖²` converges. This is where `hμ` is indispensable: without
`μ(s) > 0` the weight `μ s * (η μ s/5)` vanishes and the bound is vacuous. -/
theorem tendsto_norm_gradF_zero (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) :
    Filter.Tendsto (fun t => ‖gradient (g (S := S) (A := A) s
        (fun a' => advInf M (F.toPolicy (θ t)) s a')) (θ t)‖) Filter.atTop (nhds 0) := by
  set κ : ℝ := μ s * (η * μ s / 5) with hκ
  have hκpos : 0 < κ := by
    have := hμ s; rw [hκ]; positivity
  refine tendsto_zero_of_summable_sq (g := fun t => ‖gradient (g (S := S) (A := A) s
      (fun a' => advInf M (F.toPolicy (θ t)) s a')) (θ t)‖) ?_
  refine summable_sq_of_ascent (v := fun t => VinfDist M (F.toPolicy (θ t)) μ)
    (B := 1 / (1 - M.γ)) hκpos ?_ ?_
  · intro t
    have h := VinfDist_gain M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη (θ t) s
    rw [← hstep t] at h
    exact h
  · intro t
    unfold VinfDist
    calc ∑ s₀, μ s₀ * Vinf M (F.toPolicy (θ t)) s₀
        ≤ ∑ s₀, μ s₀ * (1 / (1 - M.γ)) :=
          Finset.sum_le_sum fun s₀ _ =>
            mul_le_mul_of_nonneg_left (Vinf_le_one_div M hr hγ₀ hγ₁ _ _) (μ.nonneg s₀)
      _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]

/-- **AKM Lemma C.4.** `π^{(t)}(a|s) · A^{(t)}(s,a) → 0` for every `s, a`. -/
theorem tendsto_pi_adv_zero (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a : A) :
    Filter.Tendsto (fun t => (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)
      Filter.atTop (nhds 0) := by
  have hbase := tendsto_norm_gradF_zero M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep s
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun t => abs_nonneg _) (fun t => ?_) hbase
  simp only [Function.comp_apply]
  have hsq := norm_sq_gradient_g M F hF hr hγ₀ hγ₁ (θ t) s a
  have h1 : |(F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a|
      = Real.sqrt (((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1]
  have h2 : Real.sqrt (‖gradient (g (S := S) (A := A) s
      (fun a' => advInf M (F.toPolicy (θ t)) s a')) (θ t)‖ ^ 2)
      = ‖gradient (g (S := S) (A := A) s
          (fun a' => advInf M (F.toPolicy (θ t)) s a')) (θ t)‖ :=
    Real.sqrt_sq (norm_nonneg _)
  rw [← h2]
  exact Real.sqrt_le_sqrt hsq

/-! ## Towards the contradiction: AKM Lemmas C.3, C.5, C.6

Fix a state `s` and suppose some `a₊` has `A^{π̄}(s,a₊) > 0` (this is
`I^s_+ ≠ ∅`). By continuity `A^{(t)}(s,a₊) → A^{π̄}(s,a₊) > 0`, so eventually
`A^{(t)}(s,a₊) > Δ/4` for a fixed `Δ > 0` (AKM Lemma C.3). Since
`d^{(t)}_μ(s) ≥ μ(s) > 0`, `tendsto_pi_adv_zero` then forces
`π^{(t)}(a₊|s) → 0`.

The `θ`-coordinate for such an action is *strictly increasing* eventually
(AKM Lemma C.5), because its gradient coordinate
`d^{(t)}_μ(s) π^{(t)}(a₊|s) A^{(t)}(s,a₊)` is strictly positive. -/

/-- **AKM Lemma C.3, positive case.** Eventually `A^{(t)}(s,a) ≥ A^{π̄}(s,a)/2`
whenever `A^{π̄}(s,a) > 0`. -/
theorem eventually_adv_pos (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) (hpos : 0 < advInf M πbar s a) :
    ∀ᶠ t in Filter.atTop, advInf M πbar s a / 2 ≤ advInf M (F.toPolicy (θ t)) s a := by
  have hA := tendsto_adv_traj M F hr hγ₀ hγ₁ θ πbar hlim s a
  have hhalf : advInf M πbar s a / 2 < advInf M πbar s a := by linarith
  exact (hA.eventually (eventually_gt_nhds hhalf)).mono fun t ht => le_of_lt ht

/-- **AKM Lemma C.4 consequence.** If `A^{π̄}(s,a) > 0` then `π^{(t)}(a|s) → 0`. -/
theorem tendsto_pi_zero_of_adv_pos (M : FiniteMDP S A)
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
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) (hpos : 0 < advInf M πbar s a) :
    (πbar s) a = 0 := by
  -- `π^{(t)}(a|s) → π̄(a|s)` and `π^{(t)}(a|s) A^{(t)}(s,a) → 0`
  have hprod := tendsto_pi_adv_zero M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep s a
  have hpi : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds ((πbar s) a)) := by
    have h1 := (tendsto_pi_nhds.mp hlim) s
    exact (tendsto_pi_nhds.mp h1) a
  have hA := tendsto_adv_traj M F hr hγ₀ hγ₁ θ πbar hlim s a
  -- the product converges to `π̄(a|s) · A^{π̄}(s,a)`, which must be `0`
  have hlimprod : Filter.Tendsto
      (fun t => (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)
      Filter.atTop (nhds ((πbar s) a * advInf M πbar s a)) := hpi.mul hA
  have heq : (πbar s) a * advInf M πbar s a = 0 :=
    tendsto_nhds_unique hlimprod hprod
  rcases mul_eq_zero.mp heq with h | h
  · exact h
  · exact absurd h (ne_of_gt hpos)

/-- **AKM Lemma C.5, positive case.** Once `A^{(t)}(s,a) > 0`, the coordinate
`θ^{(t)}(s,a)` is strictly increasing: its gradient coordinate is
`d^{(t)}_μ(s) · π^{(t)}(a|s) · A^{(t)}(s,a) > 0`, all three factors positive
(`d ≥ μ(s) > 0` by `hμ`, `π > 0` by softmax positivity). -/
theorem theta_increasing_of_adv_pos (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (η : ℝ) (hη₀ : 0 < η)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A)
    (hadv : 0 < advInf M (F.toPolicy θ) s a) :
    θ (s, a)
      < (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a) := by
  have hgrad := gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ θ s a
  have hdpos : 0 < dinfDist M (F.toPolicy θ) μ s :=
    lt_of_lt_of_le (hμ s) (mu_le_dinfDist M hγ₀ hγ₁ _ μ s)
  have hpipos : 0 < (F.toPolicy θ s) a := by
    rw [hF]; exact softmax_pos _ a
  have hprod : 0 < dinfDist M (F.toPolicy θ) μ s
      * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) :=
    mul_pos hdpos (mul_pos hpipos hadv)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hgrad]
  nlinarith [hprod, hη₀]

/-! ### The softmax ratio — AKM's rate comparison

`π_θ(a|s)/π_θ(b|s) = exp(θ(s,a) - θ(s,b))`. This is the identity that converts
statements about `θ`-coordinates into statements about probabilities, and is how
AKM compare the *decay rate* of `π^{(t)}(a₊|s)` with that of other actions. -/

theorem softmax_ratio (w : A → ℝ) (a b : A) :
    (softmax w) a = Real.exp (w a - w b) * (softmax w) b := by
  rw [softmax_apply, softmax_apply, Real.exp_sub]
  have hden : (0:ℝ) < ∑ a', Real.exp (w a') := softmax_denom_pos w
  field_simp

/-- If `θ(s,a) ≥ θ(s,b)` then `π_θ(a|s) ≥ π_θ(b|s)`. -/
theorem softmax_mono (w : A → ℝ) (a b : A) (h : w b ≤ w a) :
    (softmax w) b ≤ (softmax w) a := by
  rw [softmax_apply, softmax_apply]
  have hden : (0:ℝ) < ∑ a', Real.exp (w a') := softmax_denom_pos w
  gcongr

/-! ### AKM Lemma C.6: the gradient coordinates at a state sum to zero

`∑_a ∂V/∂θ(s,a) = d^{π}_μ(s) ∑_a π(a|s) A^π(s,a) = 0` by `sum_pi_advInf_self`.
Hence `∑_a θ^{(t)}(s,a)` is **constant** along the trajectory — AKM's
conservation law, which forces `min_a θ^{(t)}(s,a) → -∞` once
`max_a θ^{(t)}(s,a) → ∞`. -/

theorem sum_grad_coords_zero (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : EuclideanSpace ℝ (S × A)) (s : S) :
    ∑ a, (gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a) = 0 := by
  have hco : ∀ a, (gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a)
      = dinfDist M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) :=
    fun a => gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ θ s a
  rw [Finset.sum_congr rfl (fun a _ => hco a), ← Finset.mul_sum,
    sum_pi_advInf_self M hr hγ₀ hγ₁ (F.toPolicy θ) s, mul_zero]

/-- **AKM's conservation law.** `∑_a θ^{(t)}(s,a)` never changes. -/
theorem sum_theta_const (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (t : ℕ) :
    ∑ a, (θ (t + 1)) (s, a) = ∑ a, (θ t) (s, a) := by
  rw [hstep t]
  have hexp : ∀ a, (θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t)) (s, a)
      = (θ t) (s, a) + η * (gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t)) (s, a) := by
    intro a; simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_grad_coords_zero M F hF hr hγ₀ hγ₁ μ (θ t) s, mul_zero, add_zero]

/-! ### AKM Lemma C.7: some coordinate diverges to `+∞`

If `π^{(t)}(a₊|s) → 0` while `θ^{(t)}(s,a₊)` is nondecreasing, then since
`π^{(t)}(a₊|s) = exp(θ_{a₊})/∑_a exp(θ_a)` with a nondecreasing numerator, the
denominator diverges, so `max_a θ^{(t)}(s,a) → ∞`. Combined with the
conservation law `∑_a θ^{(t)}(s,a) = c`, this forces
`min_a θ^{(t)}(s,a) → -∞`. -/

/-- `π_θ(a|s) ≥ exp(θ(s,a) - M) / |A|` where `M = max_a θ(s,a)`: the softmax of
a coordinate is controlled below by its gap to the maximum. -/
theorem softmax_ge_of_le_max (w : A → ℝ) (a : A) (Mx : ℝ) (hM : ∀ b, w b ≤ Mx) :
    Real.exp (w a - Mx) / (Fintype.card A) ≤ (softmax w) a := by
  rw [softmax_apply]
  have hden : (0:ℝ) < ∑ a', Real.exp (w a') := softmax_denom_pos w
  have hub : ∑ a', Real.exp (w a') ≤ (Fintype.card A) * Real.exp Mx := by
    calc ∑ a', Real.exp (w a') ≤ ∑ _a' : A, Real.exp Mx :=
          Finset.sum_le_sum fun a' _ => Real.exp_le_exp.mpr (hM a')
      _ = (Fintype.card A) * Real.exp Mx := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0:ℝ) < (Fintype.card A) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  rw [Real.exp_sub, div_div]
  refine div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hden ?_
  calc ∑ a', Real.exp (w a') ≤ (Fintype.card A) * Real.exp Mx := hub
    _ = Real.exp Mx * (Fintype.card A) := by ring

/-! ### The limit policy's advantages sum to zero against `π̄`

`∑_a π̄(a|s) A^{π̄}(s,a) = 0` (`sum_pi_advInf_self`). So if every on-support
action had `A^{π̄} = 0`, the off-support ones are unconstrained by this identity
alone — which is exactly why AKM need the `θ`-dynamics. -/

/-- On the support of `π̄`, the limiting advantage is **≤ 0**.

`π̄(a|s) > 0` means `π^{(t)}(a|s)` is eventually bounded below, so
`π^{(t)}(a|s) A^{(t)}(s,a) → 0` forces `A^{(t)}(s,a) → 0`, i.e. `A^{π̄}(s,a) = 0`.
This is the "on-support" half; it holds with equality. -/
theorem advInf_eq_zero_on_support (M : FiniteMDP S A)
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
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) (hsupp : 0 < (πbar s) a) :
    advInf M πbar s a = 0 := by
  have hprod := tendsto_pi_adv_zero M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep s a
  have hpi : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds ((πbar s) a)) := by
    have h1 := (tendsto_pi_nhds.mp hlim) s
    exact (tendsto_pi_nhds.mp h1) a
  have hA := tendsto_adv_traj M F hr hγ₀ hγ₁ θ πbar hlim s a
  have hlimprod : Filter.Tendsto
      (fun t => (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)
      Filter.atTop (nhds ((πbar s) a * advInf M πbar s a)) := hpi.mul hA
  have heq : (πbar s) a * advInf M πbar s a = 0 :=
    tendsto_nhds_unique hlimprod hprod
  rcases mul_eq_zero.mp heq with h | h
  · exact absurd h (ne_of_gt hsupp)
  · exact h

/-! ### Bounding the `a₊` coordinate below (AKM Lemma C.9, first claim)

`θ^{(t)}(s,a₊)` is nondecreasing from the time `A^{(t)}(s,a₊) > 0` onwards
(`theta_increasing_of_adv_pos`), hence bounded below by its value there. This is
the easy half of AKM's Lemma C.9 and is unconditional given `eventually_adv_pos`. -/

theorem theta_eventually_monotone (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a : A) (T : ℕ)
    (hT : ∀ t, T ≤ t → 0 < advInf M (F.toPolicy (θ t)) s a) :
    ∀ t, T ≤ t → (θ T) (s, a) ≤ (θ t) (s, a) := by
  intro t ht
  induction t with
  | zero =>
      have : T = 0 := Nat.le_zero.mp ht
      rw [this]
  | succ n ih =>
      rcases Nat.lt_or_ge T (n + 1) with hlt | hge
      · have hTn : T ≤ n := Nat.lt_succ_iff.mp hlt
        have hstep' := theta_increasing_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀
          (θ n) s a (hT n hTn)
        rw [← hstep n] at hstep'
        exact le_trans (ih hTn) (le_of_lt hstep')
      · have : T = n + 1 := le_antisymm ht hge
        rw [this]

/-! ### AKM Lemma C.7: `max_a θ^{(t)}(s,a) → ∞`

`softmax_ge_of_le_max` gives `π_θ(a₊|s) ≥ exp(θ(s,a₊) - Mx)/|A|` with
`Mx = max_a θ(s,a)`. If `θ(s,a₊) ≥ c` and `π^{(t)}(a₊|s) → 0`, then
`exp(c - Mx_t)/|A| → 0`, so `Mx_t → ∞`. -/

theorem tendsto_max_theta_atTop (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (s : S) (ap : A) (c : ℝ)
    (hlow : ∀ t, c ≤ (θ t) (s, ap))
    (hzero : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) ap) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => (Finset.univ : Finset A).sup' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atTop := by
  classical
  set Mx : ℕ → ℝ := fun t => (Finset.univ : Finset A).sup' Finset.univ_nonempty
    (fun b => (θ t) (s, b)) with hMx
  have hcard : (0:ℝ) < (Fintype.card A) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  -- `exp (c - Mx t) / |A| ≤ π^{(t)}(ap|s)`
  have hbound : ∀ t, Real.exp (c - Mx t) / (Fintype.card A)
      ≤ (F.toPolicy (θ t) s) ap := by
    intro t
    have hle : ∀ b, (θ t) (s, b) ≤ Mx t := fun b =>
      Finset.le_sup' (fun b => (θ t) (s, b)) (Finset.mem_univ b)
    have h := softmax_ge_of_le_max (fun a' => (θ t) (s, a')) ap (Mx t) hle
    rw [hF]
    refine le_trans ?_ h
    have hmono : Real.exp (c - Mx t) ≤ Real.exp ((θ t) (s, ap) - Mx t) :=
      Real.exp_le_exp.mpr (by linarith [hlow t])
    gcongr
  -- hence `exp (c - Mx t) → 0`
  have hexp : Filter.Tendsto (fun t => Real.exp (c - Mx t)) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun t => Real.exp (c - Mx t) / (Fintype.card A))
        Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun t => by positivity) hbound ?_
      simpa using hzero
    have := hsq.const_mul ((Fintype.card A : ℝ))
    simpa [mul_div_cancel₀, ne_of_gt hcard] using this
  -- `exp (c - Mx t) → 0` forces `c - Mx t → -∞`, i.e. `Mx t → ∞`
  have hneg : Filter.Tendsto (fun t => c - Mx t) Filter.atTop Filter.atBot := by
    by_contra hcon
    rw [Real.tendsto_exp_comp_nhds_zero] at hexp
    exact hcon hexp
  refine Filter.tendsto_atTop.mpr fun b => ?_
  have := Filter.tendsto_atBot.mp hneg (c - b)
  exact this.mono fun t ht => by linarith

/-! ### AKM Lemma C.10 (`lemma:stable`): the ordering `π(a|s) ≤ π(ap|s)` persists

If at time `t` we have `π^{(t)}(a|s) ≤ π^{(t)}(ap|s)` and moreover
`A^{(t)}(s,a) ≤ A^{(t)}(s,ap)`, then the gradient coordinate at `a` is at most
that at `ap`, hence `θ^{(t+1)}(s,a) - θ^{(t)}(s,a) ≤ θ^{(t+1)}(s,ap) - θ^{(t)}(s,ap)`.
Since softmax is monotone in the coordinate difference, the ordering of
probabilities is preserved. -/

/-- The `θ`-difference `θ(s,a) - θ(s,b)` determines the probability ordering. -/
theorem pi_le_iff_theta_le (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a b : A) :
    (F.toPolicy θ s) a ≤ (F.toPolicy θ s) b ↔ (θ) (s, a) ≤ (θ) (s, b) := by
  rw [hF, hF, softmax_apply, softmax_apply]
  have hden : (0:ℝ) < ∑ a', Real.exp ((θ) (s, a')) :=
    softmax_denom_pos (fun a' => (θ) (s, a'))
  rw [div_le_div_iff_of_pos_right hden, Real.exp_le_exp]

/-- **AKM Lemma C.10, one step.** -/
theorem stable_step (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a ap : A)
    (hpi : (F.toPolicy θ s) a ≤ (F.toPolicy θ s) ap)
    (hadv : advInf M (F.toPolicy θ) s a ≤ advInf M (F.toPolicy θ) s ap)
    (hadvp : 0 ≤ advInf M (F.toPolicy θ) s ap) :
    (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) s) a
      ≤ (F.toPolicy (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) s) ap := by
  rw [pi_le_iff_theta_le F hF]
  have hθ : (θ) (s, a) ≤ (θ) (s, ap) := (pi_le_iff_theta_le F hF θ s a ap).mp hpi
  have hga := gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ θ s a
  have hgp := gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ θ s ap
  have hdnn : 0 ≤ dinfDist M (F.toPolicy θ) μ s := dinfDist_nonneg M hγ₀ _ _ _
  have hpinn : 0 ≤ (F.toPolicy θ s) a := (F.toPolicy θ s).nonneg a
  -- `π(a|s) A(s,a) ≤ π(ap|s) A(s,ap)`
  have hkey : (F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a
      ≤ (F.toPolicy θ s) ap * advInf M (F.toPolicy θ) s ap := by
    rcases le_or_gt (advInf M (F.toPolicy θ) s a) 0 with hneg | hpos
    · -- LHS ≤ 0 ≤ RHS
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos hpinn hneg)
        (mul_nonneg ((F.toPolicy θ s).nonneg ap) hadvp)
    · exact mul_le_mul hpi hadv (le_of_lt hpos) ((F.toPolicy θ s).nonneg ap)
  have hgle : (gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a)
      ≤ (gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, ap) := by
    rw [hga, hgp]
    exact mul_le_mul_of_nonneg_left hkey hdnn
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  nlinarith [hθ, hgle, hη₀]

/-! ### The limit identity `∑_a π̄(a|s) A^{π̄}(s,a) = 0` and what it does *not* give

At the limit policy, `sum_pi_advInf_self` gives `∑_a π̄(a|s) A^{π̄}(s,a) = 0`, and
`advInf_eq_zero_on_support` makes every on-support term individually zero. So the
identity is satisfied **regardless** of the off-support advantages: it carries no
information about them. This is precisely the obstruction recorded in `Goal.lean`,
and it is why AKM's argument must descend to the `θ`-dynamics (Lemmas C.5–C.11)
rather than work at the limit policy. -/

theorem limit_identity_vacuous (M : FiniteMDP S A)
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
      (nhds (fun s a => (πbar s) a)))
    (s : S) :
    ∀ a, (πbar s) a * advInf M πbar s a = 0 := by
  intro a
  rcases eq_or_lt_of_le ((πbar s).nonneg a) with h | h
  · rw [← h]; ring
  · rw [advInf_eq_zero_on_support M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim s a h,
      mul_zero]

/-! ### AKM Lemma C.10, iterated

Once the ordering `π(a|s) ≤ π(ap|s)` holds at some time `T` and the advantage
ordering `A(s,a) ≤ A(s,ap)` holds from `T` on, the probability ordering persists
for all later times. -/

theorem stable_forward (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a ap : A) (T : ℕ)
    (hadv : ∀ t, T ≤ t → advInf M (F.toPolicy (θ t)) s a
      ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hadvp : ∀ t, T ≤ t → 0 ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hT : (F.toPolicy (θ T) s) a ≤ (F.toPolicy (θ T) s) ap) :
    ∀ t, T ≤ t → (F.toPolicy (θ t) s) a ≤ (F.toPolicy (θ t) s) ap := by
  intro t ht
  induction t with
  | zero =>
      have : T = 0 := Nat.le_zero.mp ht
      rw [this] at hT; exact hT
  | succ n ih =>
      rcases Nat.lt_or_ge T (n + 1) with hlt | hge
      · have hTn : T ≤ n := Nat.lt_succ_iff.mp hlt
        have h := stable_step M F hF hr hγ₀ hγ₁ μ η hη₀ (θ n) s a ap
          (ih hTn) (hadv n hTn) (hadvp n hTn)
        rw [← hstep n] at h
        exact h
      · have : T = n + 1 := le_antisymm ht hge
        rw [this] at hT; exact hT

/-! ### The support of `π̄` is where the mass goes

`∑_a π̄(a|s) = 1`, so `π̄` has at least one action with positive probability, and
`∑_{a : π̄(a|s) > 0} π^{(t)}(a|s) → 1`. Every action with `A^{π̄}(s,a) ≠ 0` is
off-support (`tendsto_pi_zero_of_adv_pos` for the positive case), so the mass
concentrates on `I^s_0 ∩ supp π̄`. -/

/-- `π̄` has an action of positive probability at every state. -/
theorem exists_support (πbar : Policy S A) (s : S) : ∃ a, 0 < (πbar s) a := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ a, (πbar s) a = 0 := fun a =>
    le_antisymm (hcon a) ((πbar s).nonneg a)
  have := (πbar s).sum_eq_one
  rw [Finset.sum_congr rfl (fun a _ => hzero a)] at this
  simp at this

/-- **Every on-support action lies in `I^s_0`.** Restated for the endgame:
at the limit, on-support advantages vanish, so if the goal fails at `(s, ap)`
then `ap` is off-support with `A^{π̄}(s,ap) > 0` — AKM's `I^s_+ ≠ ∅`. -/
theorem support_in_I0 (M : FiniteMDP S A)
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
      (nhds (fun s a => (πbar s) a)))
    (s : S) :
    ∃ a0, 0 < (πbar s) a0 ∧ advInf M πbar s a0 = 0 := by
  obtain ⟨a0, ha0⟩ := exists_support πbar s
  exact ⟨a0, ha0, advInf_eq_zero_on_support M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
    πbar hlim s a0 ha0⟩

/-! ### The endgame comparison

Suppose the goal fails at `(s, ap)`: `π̄(ap|s) = 0` but `A^{π̄}(s,ap) > 0`. Take
`a0` on-support (so `A^{π̄}(s,a0) = 0` and `π̄(a0|s) > 0`). Then eventually

* `A^{(t)}(s,ap) ≥ A^{π̄}(s,ap)/2 > 0` (continuity), so `θ^{(t)}(s,ap)` increases
  (`theta_increasing_of_adv_pos`) and is bounded below;
* `π^{(t)}(a0|s) → π̄(a0|s) > 0`, while `π^{(t)}(ap|s) → 0`.

So `π^{(t)}(ap|s) < π^{(t)}(a0|s)` eventually, i.e. `θ^{(t)}(s,ap) < θ^{(t)}(s,a0)`
(`pi_le_iff_theta_le`), and `θ^{(t)}(s,a0)` is therefore **bounded below** too. -/

theorem theta_a0_bounded_below (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (s : S) (ap a0 : A) (c : ℝ) (T : ℕ)
    (hlow : ∀ t, T ≤ t → c ≤ (θ t) (s, ap))
    (hord : ∀ t, T ≤ t → (F.toPolicy (θ t) s) ap ≤ (F.toPolicy (θ t) s) a0) :
    ∀ t, T ≤ t → c ≤ (θ t) (s, a0) := by
  intro t ht
  have h1 : (θ t) (s, ap) ≤ (θ t) (s, a0) :=
    (pi_le_iff_theta_le F hF (θ t) s ap a0).mp (hord t ht)
  exact le_trans (hlow t ht) h1

/-! ### No action with positive limiting advantage can have `θ → -∞`

If `A^{π̄}(s,b) > 0` then eventually `A^{(t)}(s,b) > 0`, so `θ^{(t)}(s,b)` is
nondecreasing from that point (`theta_increasing_of_adv_pos`) and hence bounded
below. In particular it cannot tend to `-∞`. -/

theorem not_theta_atBot_of_adv_pos (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (b : A) (hpos : 0 < advInf M πbar s b) :
    ∃ c : ℝ, ∃ T : ℕ, ∀ t, T ≤ t → c ≤ (θ t) (s, b) := by
  -- eventually the advantage along the trajectory is positive
  have hev := eventually_adv_pos M F hr hγ₀ hγ₁ θ πbar hlim s b hpos
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  refine ⟨(θ T) (s, b), T, ?_⟩
  refine theta_eventually_monotone M F hF hr hγ₀ hγ₁ μ hμ η hη₀ θ hstep s b T ?_
  intro t ht
  exact lt_of_lt_of_le (by linarith [hpos] : (0:ℝ) < advInf M πbar s b / 2) (hT t ht)

/-! ### `θ^{(t)}(s,b) → -∞` forces `b` off-support

If `θ^{(t)}(s,b) → -∞` while some coordinate is bounded below, the softmax ratio
`π^{(t)}(b|s)/π^{(t)}(a|s) = exp(θ_b - θ_a) → 0`, so `π^{(t)}(b|s) → 0` and
`π̄(b|s) = 0`. -/

theorem pi_tendsto_zero_of_theta_atBot (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (s : S) (b : A) (c : ℝ) (a0 : A) (T : ℕ)
    (hlow : ∀ t, T ≤ t → c ≤ (θ t) (s, a0))
    (hbot : Filter.Tendsto (fun t => (θ t) (s, b)) Filter.atTop Filter.atBot) :
    Filter.Tendsto (fun t => (F.toPolicy (θ t) s) b) Filter.atTop (nhds 0) := by
  -- `π(b|s) ≤ exp(θ_b - c)` because the denominator is at least `exp(θ_{a0}) ≥ exp c`
  have hbound : ∀ t, T ≤ t → (F.toPolicy (θ t) s) b ≤ Real.exp ((θ t) (s, b) - c) := by
    intro t ht
    rw [hF, softmax_apply]
    have hden : Real.exp c ≤ ∑ a', Real.exp ((θ t) (s, a')) := by
      calc Real.exp c ≤ Real.exp ((θ t) (s, a0)) := Real.exp_le_exp.mpr (hlow t ht)
        _ ≤ ∑ a', Real.exp ((θ t) (s, a')) :=
            Finset.single_le_sum (f := fun a' : A => Real.exp ((θ t) (s, a')))
              (fun a' _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ a0)
    rw [Real.exp_sub]
    exact div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) (Real.exp_pos c) hden
  -- `exp(θ_b - c) → 0`
  have hexp : Filter.Tendsto (fun t => Real.exp ((θ t) (s, b) - c)) Filter.atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Filter.tendsto_atBot_add_const_right _ (-c) hbot |>.congr (fun t => by ring)
  refine squeeze_zero' ?_ ?_ hexp
  · exact Filter.Eventually.of_forall fun t => (F.toPolicy (θ t) s).nonneg b
  · exact Filter.eventually_atTop.mpr ⟨T, hbound⟩

/-! ## Assembly: the goal reduces to AKM's Lemma C.9

Suppose the goal fails at `(s, ap)`: `π̄(ap|s) = 0` and `A^{π̄}(s,ap) > 0`. The
lemmas above give, with `T` large and `c = θ^{(T)}(s,ap)`:

* `c ≤ θ^{(t)}(s,ap)` for `t ≥ T`  (`not_theta_atBot_of_adv_pos`);
* `π^{(t)}(ap|s) → 0`  (`tendsto_pi_zero_of_adv_pos` gives `π̄(ap|s)=0`, and
  `hlim` transports it);
* hence `max_a θ^{(t)}(s,a) → ∞`  (`tendsto_max_theta_atTop`);
* hence `min_a θ^{(t)}(s,a) → -∞`  (`tendsto_min_theta_atBot` + `sum_theta_const`).

So some action's coordinate is driven to `-∞` infinitely often. `Resid`'s
`not_theta_atBot_of_adv_pos` rules out `A^{π̄} > 0` for such an action, and
`pi_tendsto_zero_of_theta_atBot` shows it is off-support. What remains is
AKM's Lemma C.9 — that an action with `A^{π̄}(s,·) < 0` has `θ → -∞`, and the
`B^s_0` bookkeeping that turns "some coordinate diverges" into the final
contradiction. -/

/-- The trajectory's probabilities converge coordinatewise. -/
theorem tendsto_pi_coord (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) :
    Filter.Tendsto (fun t => (F.toPolicy (θ t) s) a) Filter.atTop (nhds ((πbar s) a)) := by
  have h1 := (tendsto_pi_nhds.mp hlim) s
  exact (tendsto_pi_nhds.mp h1) a


end Resid

end Proofs
end PolicyGradient
