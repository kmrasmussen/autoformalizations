/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G7b

/-!
# Vector-ascent-step — one gradient-ascent step on `Vinf`

The classical ascent lemma: for an `L`-smooth objective, a step of size `1/L`
along the gradient gains at least `‖∇f‖²/(2L)`.  Here `L = 8/(1-γ)³`, so the
step is `(1-γ)³/8` and the gain `(1-γ)³/16 · ‖∇‖²`.  The constants are exactly
consistent — there is **no slack**: the crude mean-value bound
`|f(y)-f(x)-f'(x)(y-x)| ≤ L‖y-x‖²` (constant `L`, not `L/2`) yields a gain of
exactly `0` here.  So the sharp `L/2` form is mandatory, and it is obtained by
fencing along the segment (`image_le_of_deriv_right_le_deriv_boundary`) rather
than by a Lipschitz estimate on the segment.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section VecStep

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **The sharp descent/ascent lemma, abstractly.**

If `f : E → ℝ` has derivative `G x` at every point and the derivative map is
`L`-Lipschitz, then along any direction `d`

`f (x + d) ≥ f x + G x d - (L/2) ‖d‖²`. -/
theorem sharp_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {G : E → E →L[ℝ] ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x, HasFDerivAt f (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x d : E) :
    f x + G x d - L / 2 * ‖d‖ ^ 2 ≤ f (x + d) := by
  -- The scalar restriction `φ t = - f (x + t • d)` on `[0,1]`.
  set φ : ℝ → ℝ := fun t => -f (x + t • d) with hφ
  set φ' : ℝ → ℝ := fun t => -(G (x + t • d) d) with hφ'
  -- `φ` has derivative `φ'`.
  have hpath : ∀ t : ℝ, HasDerivAt (fun u : ℝ => x + u • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hφderiv : ∀ t : ℝ, HasDerivAt φ (φ' t) t := by
    intro t
    have := (hd (x + t • d)).comp_hasDerivAt t (hpath t)
    exact this.neg
  -- Boundary: `B t = φ 0 - t * (G x d) + (L/2) * t^2 * ‖d‖^2`.
  set B : ℝ → ℝ := fun t => φ 0 - t * (G x d) + L / 2 * t ^ 2 * ‖d‖ ^ 2 with hB
  set B' : ℝ → ℝ := fun t => -(G x d) + L * t * ‖d‖ ^ 2 with hB'
  have hBderiv : ∀ t : ℝ, HasDerivAt B (B' t) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => φ 0 - u * (G x d)) (-(G x d)) t := by
      simpa using ((hasDerivAt_id t).mul_const (G x d)).const_sub (φ 0)
    have h2 : HasDerivAt (fun u : ℝ => L / 2 * u ^ 2 * ‖d‖ ^ 2)
        (L * t * ‖d‖ ^ 2) t := by
      have hp : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      have h3 := (hp.const_mul (L / 2)).mul_const (‖d‖ ^ 2)
      have heq : L / 2 * (2 * t) * ‖d‖ ^ 2 = L * t * ‖d‖ ^ 2 := by ring
      rw [heq] at h3
      exact h3
    exact h1.add h2
  -- The derivative comparison `φ' t ≤ B' t` on `[0,1)`.
  have hcmp : ∀ t ∈ Set.Ico (0:ℝ) 1, φ' t ≤ B' t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    -- `|(G (x + t•d) - G x) d| ≤ L * t * ‖d‖^2`
    have hnorm : ‖G (x + t • d) - G x‖ ≤ L * (t * ‖d‖) := by
      have := hlip (x + t • d) x
      have hsub : x + t • d - x = t • d := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at this
      exact this
    have happ : |(G (x + t • d) - G x) d| ≤ ‖G (x + t • d) - G x‖ * ‖d‖ := by
      simpa [Real.norm_eq_abs] using
        (G (x + t • d) - G x).le_opNorm d
    have hkey : (G x) d - (G (x + t • d)) d ≤ L * t * ‖d‖ ^ 2 := by
      have h1 : |(G x) d - (G (x + t • d)) d| ≤ L * (t * ‖d‖) * ‖d‖ := by
        have heq : (G (x + t • d) - G x) d
            = (G (x + t • d)) d - (G x) d := by simp
        have := happ
        rw [heq] at this
        have := this.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg d))
        rwa [abs_sub_comm] at this
      have := (abs_le.mp h1).2
      nlinarith [this]
    simp only [hφ', hB']
    linarith [hkey]
  -- Fence.
  have hfence : ∀ ⦃t⦄, t ∈ Set.Icc (0:ℝ) 1 → φ t ≤ B t := by
    refine image_le_of_deriv_right_le_deriv_boundary
      (fun t _ => (hφderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hφderiv t).hasDerivWithinAt) ?_
      (fun t _ => (hBderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hBderiv t).hasDerivWithinAt) hcmp
    simp [hB]
  have h1 := hfence (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
  simp only [hφ, hB] at h1
  simp only [one_smul, zero_smul, add_zero] at h1
  linarith [h1]

/-- **The vector ascent step (Goal `vec_ascent_step`).**

One gradient-ascent step of size `(1-γ)³/8` on `θ ↦ Vinf M (F.toPolicy θ) μ`
gains at least `(1-γ)³/16 · ‖∇‖²`.

`hasFDeriv_Vinf` supplies the derivative (`Ginf`), `Ginf_lipschitz` supplies the
`8/(1-γ)³`-Lipschitz bound on that derivative map, and `sharp_descent` turns the
pair into the inequality.  The constants leave no slack: with `L = 8/(1-γ)³` the
step is exactly `1/L` and the gain exactly `1/(2L)`. -/
theorem vec_ascent_step_proof (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : EuclideanSpace ℝ (S × A)) :
    Vinf M (F.toPolicy θ) μ
        + ((1 - M.γ) ^ 3 / 16) * ‖gradient (fun w => Vinf M (F.toPolicy w) μ) θ‖ ^ 2
      ≤ Vinf M (F.toPolicy
          (θ + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) θ)) μ := by
  have hpos : 0 < 1 - M.γ := by linarith
  set f : E S A → ℝ := fun w => Vinf M (F.toPolicy w) μ with hf
  set G : E S A → (E S A →L[ℝ] ℝ) := fun w => Ginf M w μ with hG
  set L : ℝ := 8 / (1 - M.γ) ^ 3 with hLdef
  have hLpos : 0 < L := by rw [hLdef]; positivity
  have hderiv : ∀ w : E S A, HasFDerivAt f (G w) w :=
    fun w => hasFDeriv_Vinf M F hF hr hγ₀ hγ₁ w μ
  have hlip : ∀ x y : E S A, ‖G x - G y‖ ≤ L * ‖x - y‖ :=
    fun x y => Ginf_lipschitz M hr hγ₀ hγ₁ x y μ
  -- `gradient f θ` is the Riesz representative of `G θ = fderiv ℝ f θ`.
  set g : E S A := gradient f θ with hg
  have hfd : fderiv ℝ f θ = G θ := (hderiv θ).fderiv
  -- `G θ g = ‖g‖²`
  have hGg : (G θ) g = ‖g‖ ^ 2 := by
    have h1 : (inner ℝ g g : ℝ) = fderiv ℝ f θ g := by
      rw [hg]; exact inner_gradient_left ..
    rw [hfd] at h1
    rw [← h1, real_inner_self_eq_norm_sq]
  -- Apply the sharp descent lemma with `d = (1/L) • g`.
  set d : E S A := ((1 - M.γ) ^ 3 / 8) • g with hd
  have hdesc := sharp_descent (f := f) (G := G) (L := L) hLpos.le hderiv hlip θ d
  -- `G θ d = ((1-γ)³/8) * ‖g‖²`
  have hGd : (G θ) d = ((1 - M.γ) ^ 3 / 8) * ‖g‖ ^ 2 := by
    rw [hd, map_smul, smul_eq_mul, hGg]
  -- `‖d‖² = ((1-γ)³/8)² * ‖g‖²`
  have hdn : ‖d‖ ^ 2 = ((1 - M.γ) ^ 3 / 8) ^ 2 * ‖g‖ ^ 2 := by
    rw [hd, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - M.γ) ^ 3 / 8)]
    ring
  rw [hGd, hdn] at hdesc
  -- Arithmetic: `s * ‖g‖² - (L/2) * s² * ‖g‖² = (1-γ)³/16 * ‖g‖²` for `s = 1/L`.
  have harith : ((1 - M.γ) ^ 3 / 8) * ‖g‖ ^ 2
      - L / 2 * (((1 - M.γ) ^ 3 / 8) ^ 2 * ‖g‖ ^ 2)
      = ((1 - M.γ) ^ 3 / 16) * ‖g‖ ^ 2 := by
    rw [hLdef]
    field_simp
    ring
  calc f θ + ((1 - M.γ) ^ 3 / 16) * ‖g‖ ^ 2
      = f θ + (((1 - M.γ) ^ 3 / 8) * ‖g‖ ^ 2
          - L / 2 * (((1 - M.γ) ^ 3 / 8) ^ 2 * ‖g‖ ^ 2)) := by rw [harith]
    _ ≤ f (θ + d) := by linarith [hdesc]

end VecStep

end Proofs
end PolicyGradient
