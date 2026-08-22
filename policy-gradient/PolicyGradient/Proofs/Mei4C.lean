/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.VecRate
import PolicyGradient.Proofs.G7b
import PolicyGradient.Proofs.G1
import PolicyGradient.Proofs.G2

/-!
# Mei4C — the composition proof for `Goal.mei_theorem4` (Mei et al., Theorem 4)

The rate spine `vec_smooth_loja_rate_proof` instantiated at the actual objective
`f = fun w => VinfDist M (F.toPolicy w) μ`, with `β = 8/(1-γ)³` from
`Ginf_lipschitz`.  Everything here is proved; the composition is reduced to
exactly the two open inputs (`g1_lojasiewicz`, `g9_c_positive`) plus one
inequality between constants that **the frozen statement gets wrong**.

## What lines up

* **The step size lines up on the nose.**  `mei_theorem4`'s `hstep` uses
  `(1-γ)³/8`, and with `β = 8/(1-γ)³` that is literally `1/β`, the spine's
  ascent step.  `hinvβ` in `mei4_mu_rate` is that one-line `field_simp`.
* **The smoothness input lines up.**  `Ginf_lipschitz` is per start *state*;
  `GJ_lipschitz` here averages it over `μ`, and because `μ` is a probability
  distribution the constant `8/(1-γ)³` is unchanged.
* **`‖fderiv‖` vs `‖gradient‖`.**  `g1_lojasiewicz` concludes in `‖fderiv‖`, the
  spine wants `‖gradient‖`.  `norm_gradient_Jmu` is the explicit bridge, via the
  Riesz isometry `InnerProductSpace.toDual`.
* **`⨅ s, π(a*(s)|s)` vs `c`.**  `loja_of_g1` weakens the former to the latter
  using `mei_theorem4`'s own `hcbound`.

## What does NOT line up: the constants

With Łojasiewicz coefficient `C = c/(√|S| · m)`, `m := mismatchCoeff M πstar μ`,
the spine's `1/(C²/(2β)·T)` is

    V*(μ) - V^{π_T}(μ)  ≤  2β/(C²T)  =  16 |S| m² / (c² (1-γ)³ T)        (`mei4_mu_rate`)

and transferring `μ → ρ` costs a factor `‖1/μ‖_∞` (`VstarDist_sub_le_invMu`):

    V*(ρ) - V^{π_T}(ρ)  ≤  ‖1/μ‖_∞ · 16 |S| m² / (c² (1-γ)³ T)          (`mei4_rho_rate`)

`Goal.mei_theorem4` asks instead for

    V*(ρ) - V^{π_T}(ρ)  ≤  16 |S| m  / (c² (1-γ)⁶ T)

so the two differ by the factor `‖1/μ‖_∞ · m · (1-γ)³`, and the frozen bound
follows only when that factor is `≤ 1` — the hypothesis `hconst` of
`mei_theorem4_of_loja`.

**`hconst` is false in general.**  Take `γ = 0`, `|S| = 2`, `μ` uniform.  Then
`dinfDist = μ`, so `m = 1`; `‖1/μ‖_∞ = 2`; `(1-γ)³ = 1`; the left side is `2`
and the right side is `1`.

**And the frozen statement, not the composition, is what is off.**  Mei's own
Theorem 4, as transcribed in this repo's `MEI_NOTES.md`, reads

    V*(ρ) - V^{π_t}(ρ)  ≤  16|S|/(c²(1-γ)⁶ t) · ‖d^{π*}_μ/μ‖²_∞ · ‖1/μ‖_∞

— **`m` SQUARED, and a `‖1/μ‖_∞` factor**, neither of which appears in
`Goal.mei_theorem4`.  So the frozen statement is *strictly stronger than the
paper's* by exactly the factor `m · ‖1/μ‖_∞` (both `≥ 1`), and the composition
route reproduces the paper's shape, not the frozen one.  `mei4_rho_rate` is in
fact **stronger** than the paper's own theorem: it has `(1-γ)³` where the paper
has `(1-γ)⁶`, and `(1-γ)³ ≤ 1`.

The repair to `Goal.mei_theorem4` is to square the `mismatchCoeff` and multiply
by `invMuSup μ`; `mei4_rho_rate` then discharges it outright (given the two open
inputs and `hlt`), with `(1-γ)³` to spare.

## Remaining hypotheses of `mei_theorem4_of_loja`

Beyond the frozen statement's own hypotheses:

* `hloja` — `g1_lojasiewicz`'s conclusion at every `θ t`.  **OPEN.**
* `hlt`   — `VinfDist M (F.toPolicy (θ t)) μ < VstarDist M μ` for every `t`
  (`Goal.g3_strict_suboptimality`; its proved form needs a non-degeneracy
  hypothesis the frozen `mei_theorem4` does not carry, so it stays a
  hypothesis here).
* `hconst` — the constant gap above.  **Not provable; a defect in the frozen
  statement.**

`c` and `hcbound` come from `g9_c_positive` and are already frozen-statement
hypotheses, so that open input costs nothing extra.
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

/-! ### The `ρ → μ` change of measure

`mei_theorem4` measures suboptimality at `ρ` but takes the gradient (and hence
gets the rate) at `μ`.  Transferring costs a factor `‖1/μ‖_∞`: since
`ρ s ≤ 1 ≤ (1/⨅ μ) · μ s`, and the pointwise suboptimality is nonnegative,

    V*(ρ) - V^π(ρ)  ≤  ‖1/μ‖_∞ · (V*(μ) - V^π(μ)).

This factor is *not present in the frozen statement* — see the module docstring.
-/

/-- `‖1/μ‖_∞`, the reciprocal of the smallest start probability. -/
noncomputable def invMuSup (μ : Dist S) : ℝ := (⨅ s : S, μ s)⁻¹

omit [DecidableEq S] in
/-- Under Assumption 2 the smallest start probability is attained and positive. -/
theorem iInf_mu_pos (μ : Dist S) (hμ : ∀ s, 0 < μ s) : 0 < ⨅ s : S, μ s := by
  classical
  obtain ⟨s₀, -, hmin⟩ := Finset.exists_min_image (univ : Finset S)
    (fun s => μ s) ⟨Classical.arbitrary S, mem_univ _⟩
  have heq : (⨅ s : S, μ s) = μ s₀ := by
    refine le_antisymm (ciInf_le ⟨0, ?_⟩ s₀) (le_ciInf fun s => hmin s (mem_univ s))
    rintro y ⟨s, rfl⟩
    exact μ.nonneg _
  rw [heq]
  exact hμ s₀

omit [DecidableEq S] in
theorem invMuSup_pos (μ : Dist S) (hμ : ∀ s, 0 < μ s) : 0 < invMuSup μ :=
  inv_pos.mpr (iInf_mu_pos μ hμ)

omit [DecidableEq S] in
/-- `1 ≤ ‖1/μ‖_∞ · μ s` for every `s`: the defining property of `‖1/μ‖_∞`. -/
theorem one_le_invMuSup_mul (μ : Dist S) (hμ : ∀ s, 0 < μ s) (s : S) :
    1 ≤ invMuSup μ * μ s := by
  have h0 : 0 < ⨅ s : S, μ s := iInf_mu_pos μ hμ
  have hle : (⨅ s : S, μ s) ≤ μ s := ciInf_le ⟨0, by rintro y ⟨x, rfl⟩; exact μ.nonneg _⟩ s
  rw [invMuSup, inv_mul_eq_div, le_div_iff₀ h0, one_mul]
  exact hle

/-- **The `ρ → μ` transfer.**  Nonnegative pointwise suboptimality is inflated by
at most `‖1/μ‖_∞` when the start measure is changed from `μ` to any `ρ`. -/
theorem VstarDist_sub_le_invMu (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (μ ρ : Dist S) (hμ : ∀ s, 0 < μ s) :
    VstarDist M ρ - VinfDist M π ρ
      ≤ invMuSup μ * (VstarDist M μ - VinfDist M π μ) := by
  classical
  have hΔ : ∀ s, 0 ≤ Vstar M s - Vinf M π s := fun s => by
    have := vstar_upper_proof M hr hγ₀ hγ₁ π s; linarith
  have hiv : 0 < invMuSup μ := invMuSup_pos μ hμ
  have hL : VstarDist M ρ - VinfDist M π ρ
      = ∑ s, ρ s * (Vstar M s - Vinf M π s) := by
    unfold VstarDist VinfDist
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hR : invMuSup μ * (VstarDist M μ - VinfDist M π μ)
      = ∑ s, (invMuSup μ * μ s) * (Vstar M s - Vinf M π s) := by
    unfold VstarDist VinfDist
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hL, hR]
  refine Finset.sum_le_sum fun s _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (hΔ s)
  refine le_trans ?_ (one_le_invMuSup_mul μ hμ s)
  have h1 : ρ s ≤ ∑ x, ρ x := Finset.single_le_sum (fun x _ => ρ.nonneg x) (mem_univ s)
  rw [ρ.sum_eq_one] at h1
  exact h1

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

/-! ### The rate at `ρ`, with the paper's constants

Composing `mei4_mu_rate` with `VstarDist_sub_le_invMu` gives the bound at `ρ`
that this repo's ingredients actually produce:

    V*(ρ) - V^{π_T}(ρ)  ≤  ‖1/μ‖_∞ · 16|S| · m² / (c² (1-γ)³ T)

with `m = mismatchCoeff M πstar μ`.  Compare Mei's own Theorem 4 as recorded in
`MEI_NOTES.md`:

    V*(ρ) - V^{π_t}(ρ)  ≤  16|S| / (c² (1-γ)⁶ t) · ‖d^{π*}_μ/μ‖²_∞ · ‖1/μ‖_∞

The two agree up to `(1-γ)³`, in the safe direction: `(1-γ)³ ≤ 1`, so the
paper's `1/(1-γ)⁶` is *larger* than the `1/(1-γ)³` produced here.  **Both carry
`m` SQUARED and both carry `‖1/μ‖_∞`.**  `Goal.mei_theorem4` as frozen has
neither: it has `m` to the first power and no `‖1/μ‖_∞`. -/

/-- **The `ρ` rate in the constants this repo's ingredients produce.**

Strictly stronger than the paper's own Theorem 4 (see above), and *not*
comparable to the frozen `Goal.mei_theorem4`, which is missing a factor
`m · ‖1/μ‖_∞ · (1-γ)³`. -/
theorem mei4_rho_rate (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (ρ : Dist S)
    (πstar : Policy S A)
    (θ : ℕ → E S A)
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (c : ℝ) (hc : 0 < c)
    (hloja : ∀ t, c / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy (θ t)) μ)
      ≤ ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) (θ t)‖)
    (hlt : ∀ t, VinfDist M (F.toPolicy (θ t)) μ < VstarDist M μ)
    (T : ℕ) (hT : 1 ≤ T) :
    VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ
      ≤ invMuSup μ * (16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 3 * T)
          * mismatchCoeff M πstar μ ^ 2) := by
  refine le_trans
    (VstarDist_sub_le_invMu M hr hγ₀ hγ₁ (F.toPolicy (θ T)) μ ρ hμ) ?_
  exact mul_le_mul_of_nonneg_left
    (mei4_mu_rate M F hF hr hγ₀ hγ₁ μ hμ πstar θ hstep c hc hloja hlt T hT)
    (invMuSup_pos μ hμ).le

/-! ### From `g1_lojasiewicz`'s literal conclusion to the spine's `hloja`

`g1_lojasiewicz` concludes with `⨅ s, π(a*(s)|s)` in the numerator;
`mei_theorem4` supplies `hcbound : ∀ t s, c ≤ π_t(a*(s)|s)`, hence
`c ≤ ⨅ s, π_t(a*(s)|s)`, and the coefficient is monotone in that numerator. -/

/-- Weakening `g1_lojasiewicz`'s `⨅ s, π(a*(s)|s)` to the Lemma-9 constant `c`. -/
theorem loja_of_g1 (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (πstar : Policy S A)
    (astar : S → A) (θ : E S A) (c : ℝ)
    (hcbound : ∀ s, c ≤ (F.toPolicy θ s) (astar s))
    (hsub : VinfDist M (F.toPolicy θ) μ ≤ VstarDist M μ)
    (hg1 : (⨅ s : S, (F.toPolicy θ s) (astar s))
        / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) θ‖) :
    c / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) θ‖ := by
  classical
  refine le_trans ?_ hg1
  have hm : 0 < mismatchCoeff M πstar μ := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hScard : (0:ℝ) < (Fintype.card S : ℝ) := by
    have := Fintype.card_pos_iff.mpr ‹Nonempty S›
    exact_mod_cast this
  have hSq : 0 < Real.sqrt (Fintype.card S) := Real.sqrt_pos.mpr hScard
  have hci : c ≤ ⨅ s : S, (F.toPolicy θ s) (astar s) := le_ciInf hcbound
  have hden : (0:ℝ) < Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ := by positivity
  refine mul_le_mul_of_nonneg_right ?_ (by linarith)
  rw [div_le_div_iff_of_pos_right hden]
  exact hci

/-! ## `Goal.mei_theorem4`, as far as the ingredients reach

The frozen statement is delivered with exactly three extra hypotheses beyond
what `Goal.mei_theorem4` itself carries:

* **`hloja`** — `g1_lojasiewicz`'s conclusion along the trajectory (OPEN);
* **`hlt`** — strict suboptimality at every iterate (`g3_strict_suboptimality`
  is the corresponding proved goal; it needs a non-degeneracy hypothesis this
  statement does not carry, so it is taken as a hypothesis here);
* **`hconst`** — the constant reconciliation.

`hconst` is a **real gap in the frozen statement**, not a proof artefact.  See
the module docstring: the ingredients produce `m² · ‖1/μ‖_∞ / (1-γ)³` where the
frozen statement asks for `m / (1-γ)⁶`, and Mei's own Theorem 4 produces
`m² · ‖1/μ‖_∞ / (1-γ)⁶`.  Both the extra `m` and the `‖1/μ‖_∞` are missing from
the frozen statement, and `hconst` is exactly what is needed to bridge them.
It is FALSE in general (γ = 0, |S| = 2, uniform `μ`: LHS `= 2`, RHS `= 1`). -/

set_option linter.unusedVariables false in
/-- **`Goal.mei_theorem4` reduced to the two open inputs plus the constant gap.**

Every hypothesis of the frozen statement is present, verbatim; the added ones
are `hloja` (open: `g1_lojasiewicz`), `hlt` (strict suboptimality) and `hconst`
(the constant reconciliation, which is *not* provable — see above). -/
theorem mei_theorem4_of_loja (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (ρ : Dist S)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (c : ℝ) (hc : 0 < c)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hcbound : ∀ t s, c ≤ (F.toPolicy (θ t) s) (astar s))
    -- OPEN INPUT: `Goal.g1_lojasiewicz` instantiated along the trajectory.
    (hloja : ∀ t, (⨅ s : S, (F.toPolicy (θ t) s) (astar s))
        / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy (θ t)) μ)
      ≤ ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) (θ t)‖)
    -- `Goal.g3_strict_suboptimality`: softmax is never exactly optimal.
    (hlt : ∀ t, VinfDist M (F.toPolicy (θ t)) μ < VstarDist M μ)
    -- THE CONSTANT GAP.  Not provable: see the section docstring.
    (hconst : invMuSup μ * mismatchCoeff M πstar μ * (1 - M.γ) ^ 3 ≤ 1) :
    ∀ T : ℕ, 1 ≤ T →
      VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ
        ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)
            * mismatchCoeff M πstar μ := by
  classical
  intro T hT
  have hpos : 0 < 1 - M.γ := by linarith
  set m : ℝ := mismatchCoeff M πstar μ with hmdef
  have hm : 0 < m := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hiv : 0 < invMuSup μ := invMuSup_pos μ hμ
  have hScard : (0:ℝ) < (Fintype.card S : ℝ) := by
    have := Fintype.card_pos_iff.mpr ‹Nonempty S›
    exact_mod_cast this
  have hTpos : (0:ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have hloja' : ∀ t, c / (Real.sqrt (Fintype.card S) * m)
      * (VstarDist M μ - VinfDist M (F.toPolicy (θ t)) μ)
      ≤ ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) (θ t)‖ := by
    intro t
    exact loja_of_g1 M F hγ₀ hγ₁ μ hμ πstar astar (θ t) c (hcbound t) (hlt t).le (hloja t)
  have hmain := mei4_rho_rate M F hF hr hγ₀ hγ₁ μ hμ ρ πstar θ hstep c hc hloja' hlt T hT
  refine le_trans hmain ?_
  -- `‖1/μ‖_∞ · 16|S| m² / (c²(1-γ)³T)  ≤  16|S| m / (c²(1-γ)⁶T)`, by `hconst`.
  have hg3 : (0:ℝ) < (1 - M.γ) ^ 3 := pow_pos hpos 3
  have hg6 : (1 - M.γ) ^ 6 = (1 - M.γ) ^ 3 * (1 - M.γ) ^ 3 := by ring
  have hLHS : invMuSup μ * (16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 3 * T) * m ^ 2)
      = (16 * Fintype.card S * m / (c ^ 2 * (1 - M.γ) ^ 6 * T))
        * (invMuSup μ * m * (1 - M.γ) ^ 3) := by
    rw [hg6]; field_simp
  have hRHS : 16 * (Fintype.card S : ℝ) / (c ^ 2 * (1 - M.γ) ^ 6 * T) * m
      = 16 * Fintype.card S * m / (c ^ 2 * (1 - M.γ) ^ 6 * T) := by
    field_simp
  rw [hLHS, hRHS]
  have hcoef : (0:ℝ) ≤ 16 * Fintype.card S * m / (c ^ 2 * (1 - M.γ) ^ 6 * T) := by
    have : (0:ℝ) < (1 - M.γ) ^ 6 := pow_pos hpos 6
    positivity
  calc 16 * (Fintype.card S : ℝ) * m / (c ^ 2 * (1 - M.γ) ^ 6 * T)
        * (invMuSup μ * m * (1 - M.γ) ^ 3)
      ≤ 16 * Fintype.card S * m / (c ^ 2 * (1 - M.γ) ^ 6 * T) * 1 :=
        mul_le_mul_of_nonneg_left hconst hcoef
    _ = 16 * Fintype.card S * m / (c ^ 2 * (1 - M.γ) ^ 6 * T) := mul_one _

end Mei4C

/-! ## `hconst` is FALSE — machine-checked

The constant gap of `mei_theorem4_of_loja` is not an artefact of a lossy route:
the inequality it asks for fails on the simplest possible instance.  Two states,
`γ = 0`, uniform `μ`.  With `γ = 0` the occupancy `dinf` collapses to its `t = 0`
term, so `dinfDist M π μ = μ` and `mismatchCoeff = 1`; `‖1/μ‖_∞ = 2`; and
`(1-γ)³ = 1`.  The left side is `2`, the right side `1`.

This is a statement about the *constants only* — it does not refute
`Goal.mei_theorem4` itself.  It shows that the frozen constants cannot be
reached from `vec_smooth_loja_rate` + `g1_lojasiewicz` + the `ρ → μ` transfer,
and (with `MEI_NOTES.md`'s transcription) that the frozen statement is stronger
than what Mei et al. actually prove. -/

section HconstFalse

/-- Two states, `γ = 0`, deterministic self-loops. -/
noncomputable def twoMDP : FiniteMDP Bool Bool where
  P := fun s _ => ⟨fun x => if x = s then 1 else 0, by intro; positivity, by simp⟩
  r := fun _ _ => 0
  γ := 0

/-- The uniform start distribution on two states. -/
noncomputable def unifMu : Dist Bool where
  prob := fun _ => 1 / 2
  nonneg := by intro; norm_num
  sum_eq_one := by norm_num [Fintype.sum_bool]

theorem unifMu_pos : ∀ s, 0 < unifMu s := by intro; norm_num [unifMu]

/-- With `γ = 0` the occupancy is the start distribution itself. -/
theorem dinfDist_twoMDP (π : Policy Bool Bool) (s : Bool) :
    dinfDist twoMDP π unifMu s = unifMu s := by
  classical
  have hd : ∀ s₀ : Bool, dinf twoMDP π s₀ s = if s = s₀ then 1 else 0 := by
    intro s₀
    unfold dinf
    rw [tsum_eq_single 0]
    · simp [twoMDP]
    · intro t ht
      have : (twoMDP.γ : ℝ) ^ t = 0 := by simp [twoMDP, zero_pow ht]
      rw [this, zero_mul]
  unfold dinfDist
  simp only [hd]
  rw [Finset.sum_eq_single s] <;> simp +contextual [eq_comm]

theorem mismatchCoeff_twoMDP (π : Policy Bool Bool) :
    mismatchCoeff twoMDP π unifMu = 1 := by
  classical
  have h : ∀ s : Bool, dinfDist twoMDP π unifMu s / unifMu s = 1 := by
    intro s
    rw [dinfDist_twoMDP π s, div_self (ne_of_gt (unifMu_pos s))]
  unfold mismatchCoeff
  simp [h]

theorem invMuSup_unifMu : invMuSup unifMu = 2 := by
  classical
  have h : (⨅ s : Bool, unifMu s) = 1 / 2 := by
    have : ∀ s : Bool, unifMu s = 1 / 2 := fun _ => rfl
    simp [this]
  rw [invMuSup, h]
  norm_num

/-- **`hconst` is false.**  On `twoMDP` with uniform `μ`, its left side is `2`. -/
theorem hconst_is_false (π : Policy Bool Bool) :
    ¬ (invMuSup unifMu * mismatchCoeff twoMDP π unifMu * (1 - twoMDP.γ) ^ 3 ≤ 1) := by
  rw [invMuSup_unifMu, mismatchCoeff_twoMDP π]
  norm_num [twoMDP]

end HconstFalse

end Proofs
end PolicyGradient
