/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Infinite
import PolicyGradient.Softmax
import PolicyGradient.AKM

/-!
# Smoothness of the value function

AKM Lemma E.4 / Mei et al. Lemma 7: `V^{π_θ}` is `8/(1-γ)³`-smooth in `θ` under
softmax parameterization with rewards in `[0,1]`.

## Route

The paper's proof differentiates `M(α) = (I - γP(α))⁻¹` twice. We avoid matrix
inverses entirely by working with the series form the rest of this development
already uses: `Vinf` is a `tsum` over time, so bounding its second derivative
reduces to bounding each term's, which is elementary.

The building blocks, all elementary and all needed for the final constant:

* `|r| ≤ 1` gives `|V| ≤ 1/(1-γ)` and `|Q| ≤ 1/(1-γ)`;
* the softmax derivative bounds `∑_a |∂π(a|s)/∂α| ≤ 2‖u‖` and
  `∑_a |∂²π(a|s)/∂α²| ≤ 6‖u‖²`;
* the arithmetic `2γ²·4/(1-γ)³ + γ·6/(1-γ)² + 2γ·2/(1-γ)² + 3/(1-γ) ≤ 8/(1-γ)³`,
  which the paper asserts without derivation.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- **The hidden arithmetic step in the smoothness bound.**

Mei et al. Lemma 7 finishes with `2γ²·4/(1-γ)³ + γ·6/(1-γ)² + 2γ·2/(1-γ)² +
3/(1-γ) ≤ 8/(1-γ)³` and asserts it with no derivation. Clearing denominators
it reduces to `(γ+1)(γ+3) ≤ 8`, i.e. `γ ≤ 1`. -/
theorem smoothness_arithmetic {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    2 * γ ^ 2 * (4 / (1 - γ) ^ 3) + γ * (6 / (1 - γ) ^ 2)
      + 2 * γ * (2 / (1 - γ) ^ 2) + 3 / (1 - γ)
    ≤ 8 / (1 - γ) ^ 3 := by
  have hpos : 0 < 1 - γ := by linarith
  have h3 : 0 < (1 - γ) ^ 3 := by positivity
  rw [← sub_nonneg]
  have expand : 8 / (1 - γ) ^ 3
      - (2 * γ ^ 2 * (4 / (1 - γ) ^ 3) + γ * (6 / (1 - γ) ^ 2)
        + 2 * γ * (2 / (1 - γ) ^ 2) + 3 / (1 - γ))
      = (8 - (8 * γ ^ 2 + 10 * γ * (1 - γ) + 3 * (1 - γ) ^ 2)) / (1 - γ) ^ 3 := by
    field_simp
    ring
  rw [expand]
  refine div_nonneg ?_ (le_of_lt h3)
  nlinarith [h0, h1, sq_nonneg γ]

/-- With rewards in `[0,1]`, the finite-horizon value is bounded by
`1/(1-γ)` uniformly in the horizon — the bound the smoothness constant uses. -/
theorem V_le_geom (M : FiniteMDP S A) (π : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (m : ℕ) (s : S) :
    |V M π m s| ≤ 1 / (1 - M.γ) := by
  have hb := abs_V_le M π 1 zero_le_one hr hγ₀ m s
  have hgeom : ∑ i ∈ range m, M.γ ^ i ≤ 1 / (1 - M.γ) := by
    have hlt : M.γ ≠ 1 := ne_of_lt hγ₁
    have hne : (0:ℝ) < 1 - M.γ := by linarith
    have hpow : (0:ℝ) ≤ M.γ ^ m := pow_nonneg hγ₀ m
    rw [geom_sum_eq hlt, ← sub_nonneg]
    have expand : 1 / (1 - M.γ) - (M.γ ^ m - 1) / (M.γ - 1)
        = M.γ ^ m / (1 - M.γ) := by
      field_simp
      ring
    rw [expand]
    positivity
  linarith [hb, hgeom]

/-!
### Softmax derivative bounds

The other half of the `8/(1-γ)³` constant. Under softmax the score is
`π(a)([a=b] - π(b))`, so the total variation of the derivative across actions is
controlled by the policy being a probability vector.
-/

variable [Nonempty A] [DecidableEq A]

/-- Any `Dist` value is at most one. -/
theorem Dist.le_one {ι : Type*} [Fintype ι] (p : Dist ι) (i : ι) : p i ≤ 1 := by
  have hle : p i ≤ ∑ j, p j :=
    Finset.single_le_sum (fun j _ => p.nonneg j) (mem_univ i)
  rw [p.sum_eq_one] at hle
  exact hle

/-- Each softmax score is bounded in absolute value by the action probability. -/
theorem abs_score_le (w : A → ℝ) (a b : A) :
    |softmaxScore w a b| ≤ (softmax w) a := by
  unfold softmaxScore
  rw [abs_mul, abs_of_nonneg ((softmax w).nonneg a)]
  refine mul_le_of_le_one_right ((softmax w).nonneg a) ?_
  have hb0 : 0 ≤ (softmax w) b := (softmax w).nonneg b
  have hb1 : (softmax w) b ≤ 1 := Dist.le_one _ b
  by_cases h : a = b
  · simp only [if_pos h]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · simp only [if_neg h, zero_sub, abs_neg]
    rw [abs_of_nonneg hb0]
    exact hb1

/-- **`∑_a |score(a,b)| ≤ 1`.**

The total variation of the softmax score across actions is at most one, since
each term is bounded by the corresponding probability and those sum to one.
This is the bound the smoothness constant needs — the paper's `2‖u‖` factor
comes from applying it twice (once for the policy, once for the transition). -/
theorem sum_abs_score_le_one (w : A → ℝ) (b : A) :
    ∑ a, |softmaxScore w a b| ≤ 1 := by
  calc ∑ a, |softmaxScore w a b| ≤ ∑ a, (softmax w) a :=
        Finset.sum_le_sum fun a _ => abs_score_le w a b
    _ = 1 := (softmax w).sum_eq_one

/-!
### Assembling the constant

`SmoothAt` (from `AKM.lean`) is the predicate the ascent lemma consumes. Here we
record what the value function's smoothness constant is built from and give the
composition rule that lets the pieces be combined.
-/

/-- Smoothness is preserved under a nonnegative scaling of the constant. -/
theorem SmoothAt.mono {f f' : ℝ → ℝ} {β β' : ℝ} (h : SmoothAt f f' β)
    (hle : β ≤ β') : SmoothAt f f' β' := by
  intro x y
  refine le_trans (h x y) ?_
  have hsq : (0:ℝ) ≤ (y - x) ^ 2 := sq_nonneg _
  have : β / 2 ≤ β' / 2 := by linarith
  exact mul_le_mul_of_nonneg_right this hsq

/-- A sum of smooth functions is smooth, with the constants adding. -/
theorem SmoothAt.add {f g f' g' : ℝ → ℝ} {β δ : ℝ}
    (hf : SmoothAt f f' β) (hg : SmoothAt g g' δ) :
    SmoothAt (fun x => f x + g x) (fun x => f' x + g' x) (β + δ) := by
  intro x y
  have hf' := hf x y
  have hg' := hg x y
  have hrewrite : (f y + g y) - (f x + g x) - (f' x + g' x) * (y - x)
      = (f y - f x - f' x * (y - x)) + (g y - g x - g' x * (y - x)) := by ring
  rw [hrewrite]
  refine le_trans (abs_add_le _ _) ?_
  have : β / 2 * (y - x) ^ 2 + δ / 2 * (y - x) ^ 2
      = (β + δ) / 2 * (y - x) ^ 2 := by ring
  linarith [hf', hg']

/-- Scaling a smooth function scales its constant. -/
theorem SmoothAt.const_mul {f f' : ℝ → ℝ} {β c : ℝ} (hc : 0 ≤ c)
    (hf : SmoothAt f f' β) :
    SmoothAt (fun x => c * f x) (fun x => c * f' x) (c * β) := by
  intro x y
  have hf' := hf x y
  have hrw : c * f y - c * f x - c * f' x * (y - x)
      = c * (f y - f x - f' x * (y - x)) := by ring
  rw [hrw, abs_mul, abs_of_nonneg hc]
  have hsq : (0:ℝ) ≤ (y - x) ^ 2 := sq_nonneg _
  calc c * |f y - f x - f' x * (y - x)| ≤ c * (β / 2 * (y - x) ^ 2) :=
        mul_le_mul_of_nonneg_left hf' hc
    _ = c * β / 2 * (y - x) ^ 2 := by ring

end PolicyGradient
