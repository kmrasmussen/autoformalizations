/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.VecRate
import PolicyGradient.Proofs.G7b
import PolicyGradient.Proofs.G1
import PolicyGradient.Proofs.G2

/-!
# Mei4C — the composition proof for Mei et al. Theorem 4

Work in progress: infrastructure first.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Mei4C

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- The objective of Mei's Theorem 4: expected value under the start
distribution `μ`, as a function of the tabular softmax logits. -/
noncomputable def Jmu (M : FiniteMDP S A) (F : VecPolicy S A (E S A)) (μ : Dist S)
    (θ : E S A) : ℝ :=
  VinfDist M (F.toPolicy θ) μ

/-- The Fréchet derivative of `Jmu`, as the `μ`-average of the per-state
derivatives `Ginf`. -/
noncomputable def GJ (M : FiniteMDP S A) (μ : Dist S) (θ : E S A) : E S A →L[ℝ] ℝ :=
  ∑ s : S, μ s • Ginf M θ s

/-- `Jmu` is Fréchet differentiable with derivative `GJ`. -/
theorem hasFDerivAt_Jmu (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : E S A) :
    HasFDerivAt (fun t : E S A => Jmu M F μ t) (GJ M μ θ) θ := by
  have key : (fun t : E S A => Jmu M F μ t)
      = fun t : E S A => ∑ s₀ : S, μ s₀ * Vinf M (F.toPolicy t) s₀ := rfl
  rw [key]
  have hsum : HasFDerivAt (fun t : E S A => ∑ s₀ : S, μ s₀ * Vinf M (F.toPolicy t) s₀)
      (∑ s₀ : S, μ s₀ • Ginf M θ s₀) θ := by
    have hfun : (fun t : E S A => ∑ s₀ : S, μ s₀ * Vinf M (F.toPolicy t) s₀)
        = ∑ s₀ : S, (fun t : E S A => μ s₀ * Vinf M (F.toPolicy t) s₀) := by
      funext t; simp [Finset.sum_apply]
    rw [hfun]
    refine HasFDerivAt.sum (fun s₀ _ => ?_)
    have h := (hasFDeriv_Vinf M F hF hr hγ₀ hγ₁ θ s₀).const_mul (μ s₀)
    refine h.congr_fderiv ?_
    ext v
    simp
  exact hsum

/-- **The `μ`-averaged gradient map is `8/(1-γ)³`-Lipschitz.**

`Ginf_lipschitz` gives this per state; averaging over the probability
distribution `μ` (whose weights are nonnegative and sum to one) preserves the
constant. -/
theorem GJ_lipschitz (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ₁ θ₂ : E S A) :
    ‖GJ M μ θ₁ - GJ M μ θ₂‖ ≤ 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
  classical
  have hpos : 0 < 1 - M.γ := by linarith
  have hdiff : GJ M μ θ₁ - GJ M μ θ₂
      = ∑ s : S, μ s • (Ginf M θ₁ s - Ginf M θ₂ s) := by
    rw [GJ, GJ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => (smul_sub (μ s) (Ginf M θ₁ s) (Ginf M θ₂ s)).symm
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ s : S, ‖μ s • (Ginf M θ₁ s - Ginf M θ₂ s)‖
      ≤ μ s * (8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖) := by
    intro s
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg s)]
    exact mul_le_mul_of_nonneg_left (Ginf_lipschitz M hr hγ₀ hγ₁ θ₁ θ₂ s) (μ.nonneg s)
  calc ∑ s : S, ‖μ s • (Ginf M θ₁ s - Ginf M θ₂ s)‖
      ≤ ∑ s : S, μ s * (8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖) :=
        Finset.sum_le_sum (fun s _ => hterm s)
    _ = 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
        rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]

/-! ### The gradient / Fréchet-derivative bridge

`g1_lojasiewicz` states its conclusion with `‖fderiv ℝ f θ‖`; the rate spine
`vec_smooth_loja_rate_proof` wants `‖gradient f θ‖`.  In a (complete) real inner
product space the two are equal, via the Riesz isometry
`InnerProductSpace.toDual`. -/

/-- `Jmu` has a gradient at every point, namely the Riesz representative of
`GJ`. -/
theorem hasGradientAt_Jmu (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : E S A) :
    HasGradientAt (fun t : E S A => Jmu M F μ t)
      ((InnerProductSpace.toDual ℝ (E S A)).symm (GJ M μ θ)) θ :=
  (hasFDerivAt_Jmu M F hF hr hγ₀ hγ₁ μ θ).hasGradientAt

/-- The gradient of `Jmu` is the Riesz representative of `GJ`. -/
theorem gradient_Jmu (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : E S A) :
    gradient (fun t : E S A => Jmu M F μ t) θ
      = (InnerProductSpace.toDual ℝ (E S A)).symm (GJ M μ θ) :=
  (hasGradientAt_Jmu M F hF hr hγ₀ hγ₁ μ θ).gradient

/-- **`‖gradient‖ = ‖fderiv‖`** for `Jmu`.  This is the explicit bridge between
`g1_lojasiewicz`'s conclusion and the rate spine's Łojasiewicz hypothesis. -/
theorem norm_gradient_Jmu (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ : E S A) :
    ‖gradient (fun t : E S A => Jmu M F μ t) θ‖
      = ‖fderiv ℝ (fun t : E S A => VinfDist M (F.toPolicy t) μ) θ‖ := by
  have hfd : fderiv ℝ (fun t : E S A => VinfDist M (F.toPolicy t) μ) θ = GJ M μ θ :=
    (hasFDerivAt_Jmu M F hF hr hγ₀ hγ₁ μ θ).fderiv
  rw [hfd, gradient_Jmu M F hF hr hγ₀ hγ₁ μ θ, LinearIsometryEquiv.norm_map]

/-- **The gradient map of `Jmu` is `8/(1-γ)³`-Lipschitz.**  This is exactly the
`hsmooth` input `vec_smooth_loja_rate_proof` asks for. -/
theorem gradient_Jmu_lipschitz (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (θ₁ θ₂ : E S A) :
    ‖gradient (fun t : E S A => Jmu M F μ t) θ₁
        - gradient (fun t : E S A => Jmu M F μ t) θ₂‖
      ≤ 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
  rw [gradient_Jmu M F hF hr hγ₀ hγ₁ μ θ₁, gradient_Jmu M F hF hr hγ₀ hγ₁ μ θ₂,
    ← map_sub, LinearIsometryEquiv.norm_map]
  exact GJ_lipschitz M hr hγ₀ hγ₁ μ θ₁ θ₂

/-! ## The composition

`vec_smooth_loja_rate_proof` instantiated at `f = Jmu`, `β = 8/(1-γ)³`.  Note
`(1-γ)³/8 = 1/β`, so `mei_theorem4`'s `hstep` is *exactly* the spine's ascent
recursion — that part lines up on the nose.
-/

/-- **The rate at `μ`, in its natural constants.**

The spine `vec_smooth_loja_rate_proof` instantiated at `f = Jmu M F μ`,
`β = 8/(1-γ)³`, and the Łojasiewicz coefficient
`C = c / (√|S| · mismatchCoeff M πstar μ)` that `g1_lojasiewicz` produces.

`hloja` is `g1_lojasiewicz`'s conclusion along the trajectory, already bridged
from `‖fderiv‖` to `‖gradient‖`; `hlt` is strict suboptimality (`g3`). -/
theorem mei4_mu_rate (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A)
    (θ : ℕ → E S A)
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (c : ℝ) (hc : 0 < c)
    -- `g1_lojasiewicz` along the trajectory, with `c` in place of `⨅ s, π(a*(s)|s)`
    -- (legitimate by `hcbound`, and monotone in the right direction).
    (hloja : ∀ t, c / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy (θ t)) μ)
      ≤ ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) (θ t)‖)
    -- strict suboptimality (`g3_strict_suboptimality`)
    (hlt : ∀ t, VinfDist M (F.toPolicy (θ t)) μ < VstarDist M μ)
    (T : ℕ) (hT : 1 ≤ T) :
    VstarDist M μ - VinfDist M (F.toPolicy (θ T)) μ
      ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 3 * T)
          * mismatchCoeff M πstar μ ^ 2 := by
  classical
  have hpos : 0 < 1 - M.γ := by linarith
  set β : ℝ := 8 / (1 - M.γ) ^ 3 with hβdef
  have hβ : 0 < β := by rw [hβdef]; positivity
  set m : ℝ := mismatchCoeff M πstar μ with hmdef
  have hm : 0 < m := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hScard : (0:ℝ) < (Fintype.card S : ℝ) := by
    have := Fintype.card_pos_iff.mpr ‹Nonempty S›
    exact_mod_cast this
  have hSq : 0 < Real.sqrt (Fintype.card S) := Real.sqrt_pos.mpr hScard
  set C : ℝ := c / (Real.sqrt (Fintype.card S) * m) with hCdef
  have hC : 0 < C := by rw [hCdef]; positivity
  -- the objective, as the spine sees it
  set f : E S A → ℝ := fun w => VinfDist M (F.toPolicy w) μ with hfdef
  have hfJ : f = fun w : E S A => Jmu M F μ w := rfl
  have hgrad : ∀ x : E S A, HasGradientAt f (gradient f x) x := by
    intro x
    rw [hfJ]
    have := hasGradientAt_Jmu M F hF hr hγ₀ hγ₁ μ x
    rw [gradient_Jmu M F hF hr hγ₀ hγ₁ μ x]
    exact this
  have hsmooth : ∀ x y : E S A, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖ := by
    intro x y
    rw [hfJ, hβdef]
    exact gradient_Jmu_lipschitz M F hF hr hγ₀ hγ₁ μ x y
  -- `(1-γ)³/8 = 1/β`
  have hinvβ : (1 - M.γ) ^ 3 / 8 = 1 / β := by
    rw [hβdef]; field_simp
  have hstep' : ∀ t, θ (t + 1) = θ t + (1 / β) • gradient f (θ t) := by
    intro t; rw [hstep t, hinvβ]
  -- the Łojasiewicz hypothesis in `‖gradient‖` form
  have hloja' : ∀ t, C * (VstarDist M μ - f (θ t)) ≤ ‖gradient f (θ t)‖ := by
    intro t
    have hn : ‖gradient f (θ t)‖
        = ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) (θ t)‖ := by
      rw [hfJ]; exact norm_gradient_Jmu M F hF hr hγ₀ hγ₁ μ (θ t)
    rw [hn]
    exact hloja t
  have hkey := vec_smooth_loja_rate_proof (f := f) (c := C)
    (fstar := VstarDist M μ) (β := β) hβ hC hgrad hsmooth θ hstep' hloja' hlt T hT
  -- reconcile `1/(C²/(2β)·T)` with the stated constant
  have hTpos : (0:ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have harith : 1 / (C ^ 2 / (2 * β) * T)
      = 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 3 * T) * m ^ 2 := by
    have hsq : Real.sqrt (Fintype.card S) ^ 2 = (Fintype.card S : ℝ) :=
      Real.sq_sqrt hScard.le
    rw [hCdef, hβdef]
    field_simp
    nlinarith [hsq, hSq, hm, hpos, hTpos, sq_nonneg c,
      sq_nonneg (Real.sqrt (Fintype.card S))]
  rw [← harith]
  exact hkey

end Mei4C

end Proofs
end PolicyGradient
