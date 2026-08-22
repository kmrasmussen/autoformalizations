/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.AKM51b
import PolicyGradient.Proofs.Greedy2
import PolicyGradient.Proofs.DgLip

/-!
# Resid — the residual of AKM Theorem 5.1

Transcription of Akyürek–Kakade–Mahajan (arXiv:1908.00261) Appendix C.1.
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

end Resid

end Proofs
end PolicyGradient
