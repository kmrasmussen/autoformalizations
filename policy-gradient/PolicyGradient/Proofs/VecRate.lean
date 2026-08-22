/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.VecStep
import PolicyGradient.Rate

/-!
# Vector-parameter Łojasiewicz rate (`vec_smooth_loja_rate`)

The vector analogue of `PolicyGradient.smooth_loja_rate` (`Mei.lean`).  The
accumulation argument is identical to the scalar one; only the smoothness input
changes, from `SmoothAt f f' β` to a Lipschitz bound on `gradient f`.

* `vec_ascent_step_gain` — the per-step gain `‖∇f x‖²/(2β)`, obtained from the
  already-proved `sharp_descent` with `L = β` and `d = (1/β) • gradient f x`.
* `vec_quad_decrease_of_domination` — the vector analogue of
  `quad_decrease_of_domination`.
* `vec_smooth_loja_rate_proof` — the vector analogue of `domination_rate_abstract`
  / `smooth_loja_rate`, closed with the existing `quad_decrease_rate`.
-/

namespace PolicyGradient
namespace Proofs

section VecRate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The vector ascent step.**  For an objective whose gradient map is
`β`-Lipschitz, one gradient-ascent step of size `1/β` gains at least
`‖∇f x‖²/(2β)`.

This is `sharp_descent` (from `Proofs/VecStep.lean`) with `L = β`, transported
along the Riesz isometry `InnerProductSpace.toDual`. -/
theorem vec_ascent_step_gain {f : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖) (x : E) :
    f x + 1 / (2 * β) * ‖gradient f x‖ ^ 2
      ≤ f (x + (1 / β) • gradient f x) := by
  classical
  -- The Fréchet derivative map, as the Riesz dual of the gradient.
  set G : E → (E →L[ℝ] ℝ) := fun y => (InnerProductSpace.toDual ℝ E) (gradient f y) with hG
  have hd : ∀ y : E, HasFDerivAt f (G y) y := fun y => (hgrad y).hasFDerivAt
  have hlip : ∀ y z : E, ‖G y - G z‖ ≤ β * ‖y - z‖ := by
    intro y z
    have hmap : G y - G z = (InnerProductSpace.toDual ℝ E) (gradient f y - gradient f z) := by
      simp [hG, map_sub]
    rw [hmap, LinearIsometryEquiv.norm_map]
    exact hsmooth y z
  set g : E := gradient f x with hgdef
  set d : E := (1 / β) • g with hddef
  have hdesc := sharp_descent (f := f) (G := G) (L := β) hβ.le hd hlip x d
  -- `G x g = ‖g‖²`
  have hGg : (G x) g = ‖g‖ ^ 2 := by
    show ((InnerProductSpace.toDual ℝ E) g) g = ‖g‖ ^ 2
    rw [InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq]
  have hGd : (G x) d = (1 / β) * ‖g‖ ^ 2 := by
    rw [hddef, map_smul, smul_eq_mul, hGg]
  have hdn : ‖d‖ ^ 2 = (1 / β) ^ 2 * ‖g‖ ^ 2 := by
    rw [hddef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / β)]
    ring
  rw [hGd, hdn] at hdesc
  have harith : (1 / β) * ‖g‖ ^ 2 - β / 2 * ((1 / β) ^ 2 * ‖g‖ ^ 2)
      = 1 / (2 * β) * ‖g‖ ^ 2 := by
    field_simp
    ring
  linarith [hdesc, harith]

/-- **Gradient domination gives a quadratic decrease** (vector version). -/
theorem vec_quad_decrease_of_domination {f : E → ℝ} {c fstar β : ℝ}
    (hβ : 0 < β) (hc : 0 ≤ c)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖) (x : E)
    (hdom : c * (fstar - f x) ≤ ‖gradient f x‖) (hle : f x ≤ fstar) :
    fstar - f (x + (1 / β) • gradient f x)
      ≤ (fstar - f x) - c ^ 2 / (2 * β) * (fstar - f x) ^ 2 := by
  have hasc := vec_ascent_step_gain hβ hgrad hsmooth x
  have hsq : c ^ 2 * (fstar - f x) ^ 2 ≤ ‖gradient f x‖ ^ 2 := by
    have h1 : 0 ≤ fstar - f x := by linarith
    have h2 : 0 ≤ c * (fstar - f x) := mul_nonneg hc h1
    calc c ^ 2 * (fstar - f x) ^ 2 = (c * (fstar - f x)) ^ 2 := by ring
      _ ≤ ‖gradient f x‖ ^ 2 := by nlinarith [hdom, h2]
  have hkey : c ^ 2 / (2 * β) * (fstar - f x) ^ 2
      ≤ 1 / (2 * β) * ‖gradient f x‖ ^ 2 := by
    have hinv : (0:ℝ) < 1 / (2 * β) := by positivity
    have heq1 : c ^ 2 / (2 * β) * (fstar - f x) ^ 2
        = 1 / (2 * β) * (c ^ 2 * (fstar - f x) ^ 2) := by field_simp
    rw [heq1]
    exact mul_le_mul_of_nonneg_left hsq hinv.le
  linarith [hasc, hkey]

/-- **`vec_smooth_loja_rate`** — the vector-parameter `O(1/T)` rate.

The exact vector analogue of `PolicyGradient.smooth_loja_rate` / of
`domination_rate_abstract`: `β`-smoothness (as a Lipschitz gradient map) plus a
Łojasiewicz bound with coefficient `c`, along gradient ascent with stepsize
`1/β`, gives suboptimality at most `2β/(c²T)`. -/
theorem vec_smooth_loja_rate_proof {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {c fstar β : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hsmooth : ∀ x y, ‖gradient f x - gradient f y‖ ≤ β * ‖x - y‖)
    (x : ℕ → E) (hx : ∀ t, x (t + 1) = x t + (1 / β) • gradient f (x t))
    (hloja : ∀ t, c * (fstar - f (x t)) ≤ ‖gradient f (x t)‖)
    (hlt : ∀ t, f (x t) < fstar)
    (T : ℕ) (hT : 1 ≤ T) :
    fstar - f (x T) ≤ 1 / (c ^ 2 / (2 * β) * T) := by
  set δ : ℕ → ℝ := fun t => fstar - f (x t) with hδ
  have hpos : ∀ t, 0 < δ t := fun t => by simp only [hδ]; linarith [hlt t]
  have hstep : ∀ t, δ (t + 1) ≤ δ t - (c ^ 2 / (2 * β)) * (δ t) ^ 2 := by
    intro t
    simp only [hδ]
    rw [hx t]
    exact vec_quad_decrease_of_domination hβ hc.le hgrad hsmooth (x t) (hloja t)
      (hlt t).le
  have hK : 0 < c ^ 2 / (2 * β) := by positivity
  exact PolicyGradient.quad_decrease_rate hK δ hpos hstep T hT

end VecRate

end Proofs
end PolicyGradient
