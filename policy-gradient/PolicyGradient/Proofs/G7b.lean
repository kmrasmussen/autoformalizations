/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target
import PolicyGradient.Proofs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# G7b — AKM Lemma E.4: the `8/(1-γ)³` smoothness bound

Route: no second derivative is ever constructed. Instead the **gradient map**
`θ ↦ fderiv ℝ (V ∘ π_θ) θ` is shown to be globally Lipschitz with constant
`8/(1-γ)³`, and `norm_fderiv_le_of_lip'` converts that into the bound on
`fderiv (fderiv V)` — for free where the second derivative fails to exist, since
Mathlib's `fderiv` is then `0`.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section G7b

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]


/-! ### The finite-horizon value as a function of the parameter -/

/-- The finite-horizon value of the tabular softmax policy at parameter `θ`. -/
noncomputable def W (M : FiniteMDP S A) : ℕ → E S A → S → ℝ
  | 0, _, _ => 0
  | n + 1, θ, s => ∑ a, p (S := S) (A := A) s a θ
      * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')

@[simp] theorem W_zero (M : FiniteMDP S A) (θ : E S A) (s : S) : W M 0 θ s = 0 := rfl

theorem W_succ (M : FiniteMDP S A) (n : ℕ) (θ : E S A) (s : S) :
    W M (n + 1) θ s = ∑ a, p (S := S) (A := A) s a θ
      * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s') := rfl

/-- `W` is the finite-horizon `V` of the induced policy. -/
theorem W_eq_V (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (n : ℕ) (θ : E S A) (s : S) : W M n θ s = V M (F.toPolicy θ) n s := by
  induction n generalizing s with
  | zero => simp [W, V]
  | succ n ih =>
    rw [W_succ, V]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hF θ s a]
    have : ∑ s', (M.P s a) s' * W M n θ s'
        = ∑ s', (M.P s a) s' * V M (F.toPolicy θ) n s' :=
      Finset.sum_congr rfl fun s' _ => by rw [ih s']
    rw [this]
    rfl


/-! ### The derivative of the finite-horizon value -/

/-- The `θ`-derivative of `W`, by the recursion obtained from differentiating
`W_succ`: a product rule with the softmax derivative `dp` on the outside and the
transported derivative of the tail on the inside. -/
noncomputable def DW (M : FiniteMDP S A) : ℕ → E S A → S → (E S A →L[ℝ] ℝ)
  | 0, _, _ => 0
  | n + 1, θ, s => ∑ a,
      ((M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s') • dp (S := S) (A := A) s a θ
        + (p (S := S) (A := A) s a θ * M.γ) • ∑ s', ((M.P s a) s' • DW M n θ s'))

@[simp] theorem DW_zero (M : FiniteMDP S A) (θ : E S A) (s : S) : DW M 0 θ s = 0 := rfl

theorem DW_succ (M : FiniteMDP S A) (n : ℕ) (θ : E S A) (s : S) :
    DW M (n + 1) θ s = ∑ a,
      ((M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s') • dp (S := S) (A := A) s a θ
        + (p (S := S) (A := A) s a θ * M.γ) • ∑ s', ((M.P s a) s' • DW M n θ s')) := rfl

/-- **`DW` is the derivative of `W`.** -/
theorem hasFDeriv_W (M : FiniteMDP S A) (n : ℕ) (θ : E S A) (s : S) :
    HasFDerivAt (fun t : E S A => W M n t s) (DW M n θ s) θ := by
  induction n generalizing s θ with
  | zero => simpa [W] using (hasFDerivAt_const (0 : ℝ) θ)
  | succ n ih =>
    have hfun : (fun t : E S A => W M (n + 1) t s)
        = fun t : E S A => ∑ a, p (S := S) (A := A) s a t
            * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n t s') := rfl
    rw [hfun, DW_succ]
    have key : (fun t : E S A => ∑ a, p (S := S) (A := A) s a t
            * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n t s'))
        = ∑ a : A, (fun t : E S A => p (S := S) (A := A) s a t
            * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n t s')) := by
      funext t; simp [Finset.sum_apply]
    rw [key]
    refine HasFDerivAt.sum (fun a _ => ?_)
    -- inner: the tail value
    have htail : HasFDerivAt
        (fun t : E S A => M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n t s')
        (M.γ • ∑ s' : S, ((M.P s a) s' • DW M n θ s')) θ := by
      have hsum : HasFDerivAt (fun t : E S A => ∑ s', (M.P s a) s' * W M n t s')
          (∑ s' : S, ((M.P s a) s' • DW M n θ s')) θ := by
        have k2 : (fun t : E S A => ∑ s', (M.P s a) s' * W M n t s')
            = ∑ s' : S, (fun t : E S A => (M.P s a) s' * W M n t s') := by
          funext t; simp [Finset.sum_apply]
        rw [k2]
        refine HasFDerivAt.sum (fun s' _ => ?_)
        have := (ih θ s').const_mul ((M.P s a) s')
        exact this
      exact (hsum.const_mul M.γ).const_add _
    have hprod := (hasFDeriv_p (S := S) (A := A) s a θ).mul htail
    refine hprod.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring


/-! ### Total-variation bounds on the softmax score -/

theorem p_nonneg (s : S) (a : A) (θ : E S A) : 0 ≤ p (S := S) (A := A) s a θ :=
  (softmax (fun a' => θ (s, a'))).nonneg a

theorem p_sum_eq_one (s : S) (θ : E S A) : ∑ a, p (S := S) (A := A) s a θ = 1 :=
  (softmax (fun a' => θ (s, a'))).sum_eq_one

theorem p_le_one (s : S) (a : A) (θ : E S A) : p (S := S) (A := A) s a θ ≤ 1 := by
  have h := Finset.single_le_sum
    (f := fun b => p (S := S) (A := A) s b θ)
    (fun b _ => p_nonneg (S := S) (A := A) s b θ) (mem_univ a)
  rw [p_sum_eq_one] at h
  exact h

/-- The `ℓ¹` mass of the score matrix at a state: `∑_a ∑_b |p_a(δ_ab - p_b)| ≤ 2`. -/
theorem score_l1_le_two (s : S) (θ : E S A) :
    ∑ a, ∑ b, |softmaxScore (fun a' => θ (s, a')) a b| ≤ 2 := by
  set P : A → ℝ := fun a => p (S := S) (A := A) s a θ with hP
  have hPn : ∀ a, 0 ≤ P a := fun a => p_nonneg (S := S) (A := A) s a θ
  have hP1 : ∑ a, P a = 1 := p_sum_eq_one (S := S) (A := A) s θ
  have hrow : ∀ a, ∑ b, |softmaxScore (fun a' => θ (s, a')) a b| ≤ 2 * P a := by
    intro a
    have hb : ∀ b, |softmaxScore (fun a' => θ (s, a')) a b|
        = P a * |(if a = b then (1:ℝ) else 0) - P b| := by
      intro b
      unfold softmaxScore
      show |P a * ((if a = b then (1:ℝ) else 0) - P b)| = _
      rw [abs_mul, abs_of_nonneg (hPn a)]
    calc ∑ b, |softmaxScore (fun a' => θ (s, a')) a b|
        = ∑ b, P a * |(if a = b then (1:ℝ) else 0) - P b| :=
          Finset.sum_congr rfl fun b _ => hb b
      _ = P a * ∑ b, |(if a = b then (1:ℝ) else 0) - P b| := by rw [Finset.mul_sum]
      _ ≤ P a * 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (hPn a)
          have hsplit : ∑ b, |(if a = b then (1:ℝ) else 0) - P b|
              = |1 - P a| + ∑ b ∈ univ.erase a, P b := by
            rw [← Finset.add_sum_erase _ _ (mem_univ a)]
            congr 1
            · simp
            refine Finset.sum_congr rfl fun b hb' => ?_
            rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hb')), zero_sub, abs_neg,
              abs_of_nonneg (hPn b)]
          rw [hsplit]
          have herase : ∑ b ∈ univ.erase a, P b = 1 - P a := by
            have := Finset.add_sum_erase univ P (mem_univ a)
            rw [hP1] at this; linarith
          rw [herase, abs_of_nonneg (by linarith [p_le_one (S := S) (A := A) s a θ] :
            (0:ℝ) ≤ 1 - P a)]
          have h1 : P a ≤ 1 := p_le_one (S := S) (A := A) s a θ
          have h0 : 0 ≤ P a := hPn a
          linarith
      _ = 2 * P a := by ring
  calc ∑ a, ∑ b, |softmaxScore (fun a' => θ (s, a')) a b|
      ≤ ∑ a, 2 * P a := Finset.sum_le_sum fun a _ => hrow a
    _ = 2 := by rw [← Finset.mul_sum, hP1, mul_one]

/-- The total operator-norm mass of the softmax derivative at a state is at most `2`. -/
theorem sum_norm_dp_le (s : S) (θ : E S A) :
    ∑ a, ‖dp (S := S) (A := A) s a θ‖ ≤ 2 := by
  refine le_trans (Finset.sum_le_sum (fun a _ => ?_)) (score_l1_le_two (S := S) (A := A) s θ)
  exact norm_comb_le s (fun b => softmaxScore (fun a' => θ (s, a')) a b)


/-! ### Uniform bounds on `W` and `DW` -/

variable (M : FiniteMDP S A)

/-- `|W n θ s| ≤ 1/(1-γ)`: the geometric bound, uniform in the horizon. -/
theorem abs_W_le (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (n : ℕ) (θ : E S A) (s : S) : |W M n θ s| ≤ 1 / (1 - M.γ) := by
  have hpos : 0 < 1 - M.γ := by linarith
  induction n generalizing s with
  | zero =>
    simp only [W_zero, abs_zero]
    positivity
  | succ n ih =>
    rw [W_succ]
    have hq : ∀ a, |M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s'| ≤ 1 / (1 - M.γ) := by
      intro a
      have hin : |∑ s', (M.P s a) s' * W M n θ s'| ≤ 1 / (1 - M.γ) := by
        calc |∑ s', (M.P s a) s' * W M n θ s'|
            ≤ ∑ s', |(M.P s a) s' * W M n θ s'| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ s', (M.P s a) s' * |W M n θ s'| := by
              refine Finset.sum_congr rfl fun s' _ => ?_
              rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
          _ ≤ ∑ s', (M.P s a) s' * (1 / (1 - M.γ)) :=
              Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (ih s') ((M.P s a).nonneg s')
          _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
      calc |M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s'|
          ≤ |M.r s a| + |M.γ * ∑ s', (M.P s a) s' * W M n θ s'| := abs_add_le _ _
        _ ≤ 1 + M.γ * (1 / (1 - M.γ)) := by
            refine add_le_add (hr s a) ?_
            rw [abs_mul, abs_of_nonneg hγ₀]
            exact mul_le_mul_of_nonneg_left hin hγ₀
        _ = 1 / (1 - M.γ) := by field_simp; ring
    calc |∑ a, p (S := S) (A := A) s a θ * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')|
        ≤ ∑ a, |p (S := S) (A := A) s a θ
            * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, p (S := S) (A := A) s a θ
            * |M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s'| := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [abs_mul, abs_of_nonneg (p_nonneg (S := S) (A := A) s a θ)]
      _ ≤ ∑ a, p (S := S) (A := A) s a θ * (1 / (1 - M.γ)) :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (hq a) (p_nonneg (S := S) (A := A) s a θ)
      _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, p_sum_eq_one, one_mul]

/-- `‖DW n θ s‖ ≤ 2/(1-γ)²`, uniform in the horizon: two units from the score's
`ℓ¹` mass, and the two powers of `1/(1-γ)` from `Q` and the contraction. -/
theorem norm_DW_le (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (n : ℕ) (θ : E S A) (s : S) : ‖DW M n θ s‖ ≤ 2 / (1 - M.γ) ^ 2 := by
  have hpos : 0 < 1 - M.γ := by linarith
  induction n generalizing s with
  | zero =>
    simp only [DW_zero, norm_zero]
    positivity
  | succ n ih =>
    rw [DW_succ]
    have hterm : ∀ a : A,
        ‖((M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s') • dp (S := S) (A := A) s a θ
          + (p (S := S) (A := A) s a θ * M.γ) • ∑ s', ((M.P s a) s' • DW M n θ s'))‖
        ≤ (1 / (1 - M.γ)) * ‖dp (S := S) (A := A) s a θ‖
          + p (S := S) (A := A) s a θ * (M.γ * (2 / (1 - M.γ) ^ 2)) := by
      intro a
      have hq : |M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s'| ≤ 1 / (1 - M.γ) := by
        have hin : |∑ s', (M.P s a) s' * W M n θ s'| ≤ 1 / (1 - M.γ) := by
          calc |∑ s', (M.P s a) s' * W M n θ s'|
              ≤ ∑ s', |(M.P s a) s' * W M n θ s'| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ s', (M.P s a) s' * |W M n θ s'| := by
                refine Finset.sum_congr rfl fun s' _ => ?_
                rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
            _ ≤ ∑ s', (M.P s a) s' * (1 / (1 - M.γ)) :=
                Finset.sum_le_sum fun s' _ =>
                  mul_le_mul_of_nonneg_left (abs_W_le M hr hγ₀ hγ₁ n θ s')
                    ((M.P s a).nonneg s')
            _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
        calc |M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s'|
            ≤ |M.r s a| + |M.γ * ∑ s', (M.P s a) s' * W M n θ s'| := abs_add_le _ _
          _ ≤ 1 + M.γ * (1 / (1 - M.γ)) := by
              refine add_le_add (hr s a) ?_
              rw [abs_mul, abs_of_nonneg hγ₀]
              exact mul_le_mul_of_nonneg_left hin hγ₀
          _ = 1 / (1 - M.γ) := by field_simp; ring
      have htail : ‖∑ s' : S, ((M.P s a) s' • DW M n θ s')‖ ≤ 2 / (1 - M.γ) ^ 2 := by
        calc ‖∑ s' : S, ((M.P s a) s' • DW M n θ s')‖
            ≤ ∑ s', ‖(M.P s a) s' • DW M n θ s'‖ := norm_sum_le _ _
          _ = ∑ s', (M.P s a) s' * ‖DW M n θ s'‖ := by
              refine Finset.sum_congr rfl fun s' _ => ?_
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((M.P s a).nonneg s')]
          _ ≤ ∑ s', (M.P s a) s' * (2 / (1 - M.γ) ^ 2) :=
              Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (ih s') ((M.P s a).nonneg s')
          _ = 2 / (1 - M.γ) ^ 2 := by
              rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (p_nonneg (S := S) (A := A) s a θ) hγ₀), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htail hγ₀) (p_nonneg (S := S) (A := A) s a θ)
    calc ‖∑ a, ((M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s') • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ) • ∑ s', ((M.P s a) s' • DW M n θ s'))‖
        ≤ ∑ a, ‖((M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s') • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ) • ∑ s', ((M.P s a) s' • DW M n θ s'))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ a, ((1 / (1 - M.γ)) * ‖dp (S := S) (A := A) s a θ‖
            + p (S := S) (A := A) s a θ * (M.γ * (2 / (1 - M.γ) ^ 2))) :=
          Finset.sum_le_sum fun a _ => hterm a
      _ = (1 / (1 - M.γ)) * (∑ a, ‖dp (S := S) (A := A) s a θ‖)
            + M.γ * (2 / (1 - M.γ) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, p_sum_eq_one, one_mul]
      _ ≤ (1 / (1 - M.γ)) * 2 + M.γ * (2 / (1 - M.γ) ^ 2) := by
          have hc : (0:ℝ) ≤ 1 / (1 - M.γ) := by positivity
          have := mul_le_mul_of_nonneg_left (sum_norm_dp_le (S := S) (A := A) s θ) hc
          linarith
      _ = 2 / (1 - M.γ) ^ 2 := by field_simp; ring


/-! ### Lipschitz estimates for the softmax layer

The `ℓ¹` Lipschitz bound for the probability vector is obtained without any
`ℓ¹`-valued calculus: `∑_b |x_b|` is `∑_b ε_b x_b` for the sign vector `ε`, and
`θ ↦ ∑_b ε_b p_b(θ)` is exactly the `g` of `Proofs.g` with weights `ε`, already
known to be `2‖ε‖_∞`-Lipschitz. -/

/-- **The softmax probability vector is `2`-Lipschitz in `ℓ¹`.** -/
theorem sum_abs_p_sub_le (s : S) (θ₁ θ₂ : E S A) :
    ∑ b, |p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂| ≤ 2 * ‖θ₁ - θ₂‖ := by
  classical
  set ε : A → ℝ := fun b =>
    if p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂ < 0 then -1 else 1 with hε
  have hεb : ∀ b, |ε b| ≤ 1 := by
    intro b; rw [hε]; by_cases h : p (S := S) (A := A) s b θ₁ - p s b θ₂ < 0 <;> simp [h]
  have hkey : ∀ b, |p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂|
      = ε b * (p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂) := by
    intro b
    rw [hε]
    by_cases h : p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂ < 0
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_nonneg (not_lt.mp h)]
  have hg : ∑ b, ε b * (p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂)
      = g (S := S) (A := A) s ε θ₁ - g (S := S) (A := A) s ε θ₂ := by
    unfold g
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by unfold p; ring
  calc ∑ b, |p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂|
      = ∑ b, ε b * (p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂) :=
        Finset.sum_congr rfl fun b _ => hkey b
    _ = g (S := S) (A := A) s ε θ₁ - g (S := S) (A := A) s ε θ₂ := hg
    _ ≤ |g (S := S) (A := A) s ε θ₁ - g (S := S) (A := A) s ε θ₂| := le_abs_self _
    _ ≤ 2 * 1 * ‖θ₁ - θ₂‖ := g_lipschitz s ε 1 hεb θ₁ θ₂
    _ = 2 * ‖θ₁ - θ₂‖ := by ring


theorem abs_g_le (s : S) (q : A → ℝ) (B : ℝ) (hq : ∀ a, |q a| ≤ B) (t : E S A) :
    |g (S := S) (A := A) s q t| ≤ B := by
  unfold g
  calc |∑ a, (softmax fun a' => t (s, a')) a * q a|
      ≤ ∑ a, |(softmax fun a' => t (s, a')) a * q a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, (softmax fun a' => t (s, a')) a * |q a| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [abs_mul, abs_of_nonneg ((softmax fun a' => t (s, a')).nonneg a)]
    _ ≤ ∑ a, (softmax fun a' => t (s, a')) a * B :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hq a) ((softmax fun a' => t (s, a')).nonneg a)
    _ = B := by rw [← Finset.sum_mul, (softmax fun a' => t (s, a')).sum_eq_one, one_mul]

/-- **The softmax score contracted against a bounded weight is `6B`-Lipschitz.**

This is the only second-order input the whole argument needs, and it is proved
without differentiating twice: the coefficient of `dg` is `p_b·(q_b - ḡ)`, whose
`ℓ¹` variation splits into `2B·‖Δp‖₁` (bounded by `sum_abs_p_sub_le`) and
`‖p‖₁·|Δḡ|` (bounded by `g_lipschitz`). -/
theorem dg_lipschitz (s : S) (q : A → ℝ) (B : ℝ) (hq : ∀ a, |q a| ≤ B) (θ₁ θ₂ : E S A) :
    ‖dg (S := S) (A := A) s q θ₁ - dg (S := S) (A := A) s q θ₂‖ ≤ 6 * B * ‖θ₁ - θ₂‖ := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hq (Classical.arbitrary A))
  set P₁ : A → ℝ := fun b => p (S := S) (A := A) s b θ₁ with hP₁
  set P₂ : A → ℝ := fun b => p (S := S) (A := A) s b θ₂ with hP₂
  set G₁ : ℝ := g (S := S) (A := A) s q θ₁ with hG₁
  set G₂ : ℝ := g (S := S) (A := A) s q θ₂ with hG₂
  have hdiff : dg (S := S) (A := A) s q θ₁ - dg (S := S) (A := A) s q θ₂
      = ∑ b : A, ((P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂))) • (pr (S := S) (A := A) (s, b)) := by
    unfold dg
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    show (P₁ b * (q b - G₁)) • (pr (S := S) (A := A) (s, b))
        - (P₂ b * (q b - G₂)) • (pr (S := S) (A := A) (s, b)) = _
    module
  rw [hdiff]
  refine le_trans (norm_comb_le s (fun b => (P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂)))) ?_
  have hbnd : ∀ b : A, |(P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂))|
      ≤ 2 * B * |P₁ b - P₂ b| + P₂ b * (2 * B * ‖θ₁ - θ₂‖) := by
    intro b
    have hsplit : (P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂))
        = (P₁ b - P₂ b) * (q b - G₁) + P₂ b * (G₂ - G₁) := by ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul]
      have hin : |q b - G₁| ≤ 2 * B := by
        calc |q b - G₁| ≤ |q b| + |G₁| := abs_sub _ _
          _ ≤ B + B := add_le_add (hq b) (abs_g_le s q B hq θ₁)
          _ = 2 * B := by ring
      have := mul_le_mul_of_nonneg_left hin (abs_nonneg (P₁ b - P₂ b))
      linarith [this]
    · rw [abs_mul, abs_of_nonneg (p_nonneg (S := S) (A := A) s b θ₂)]
      refine mul_le_mul_of_nonneg_left ?_ (p_nonneg (S := S) (A := A) s b θ₂)
      rw [abs_sub_comm]
      exact g_lipschitz s q B hq θ₁ θ₂
  calc ∑ b, |(P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂))|
      ≤ ∑ b, (2 * B * |P₁ b - P₂ b| + P₂ b * (2 * B * ‖θ₁ - θ₂‖)) :=
        Finset.sum_le_sum fun b _ => hbnd b
    _ = 2 * B * (∑ b, |P₁ b - P₂ b|) + 2 * B * ‖θ₁ - θ₂‖ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          hP₂, p_sum_eq_one, one_mul]
    _ ≤ 2 * B * (2 * ‖θ₁ - θ₂‖) + 2 * B * ‖θ₁ - θ₂‖ := by
        have := sum_abs_p_sub_le (S := S) (A := A) s θ₁ θ₂
        nlinarith [norm_nonneg (θ₁ - θ₂)]
    _ = 6 * B * ‖θ₁ - θ₂‖ := by ring


/-- `dg` is the `q`-contraction of the score derivatives: `∑_a q_a · dp_a = dg`.

Both sides are the derivative of `g s q` at `t` (`hasFDeriv_g` and the sum rule
applied to `hasFDeriv_p`), so they agree by uniqueness of the Fréchet
derivative. -/
theorem sum_smul_dp_eq_dg (s : S) (q : A → ℝ) (t : E S A) :
    ∑ a : A, q a • dp (S := S) (A := A) s a t = dg (S := S) (A := A) s q t := by
  have h1 : HasFDerivAt (g (S := S) (A := A) s q) (∑ a : A, q a • dp (S := S) (A := A) s a t) t := by
    have key : (g (S := S) (A := A) s q)
        = ∑ a : A, (fun x : E S A => p (S := S) (A := A) s a x * q a) := by
      funext x; simp [g, p, Finset.sum_apply]
    rw [key]
    refine HasFDerivAt.sum (fun a _ => ?_)
    have h := (hasFDeriv_p (S := S) (A := A) s a t).mul_const (q a)
    refine h.congr_fderiv ?_
    ext v
    simp [mul_comm]
  exact h1.unique (hasFDeriv_g s q t)


/-! ### `W` is Lipschitz, uniformly in the horizon -/

theorem W_lipschitz (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (n : ℕ) (θ₁ θ₂ : E S A) (s : S) :
    |W M n θ₁ s - W M n θ₂ s| ≤ 2 / (1 - M.γ) ^ 2 * ‖θ₁ - θ₂‖ := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
    (f := fun t : E S A => W M n t s) (s := (Set.univ : Set (E S A)))
    (C := 2 / (1 - M.γ) ^ 2)
    (fun x _ => (hasFDeriv_W M n x s).differentiableAt)
    (fun x _ => by rw [(hasFDeriv_W M n x s).fderiv]; exact norm_DW_le M hr hγ₀ hγ₁ n x s)
    convex_univ (Set.mem_univ θ₂) (Set.mem_univ θ₁)
  simpa [Real.norm_eq_abs] using hmvt


/-! ### `dg` is linear in the weights -/

theorem dg_sub (s : S) (q₁ q₂ : A → ℝ) (t : E S A) :
    dg (S := S) (A := A) s q₁ t - dg (S := S) (A := A) s q₂ t
      = dg (S := S) (A := A) s (fun a => q₁ a - q₂ a) t := by
  unfold dg
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  set P : A → ℝ := fun a => (softmax fun a' => t (s, a')) a with hP
  show (P b * (q₁ b - ∑ a, P a * q₁ a)) • (pr (S := S) (A := A) (s, b))
      - (P b * (q₂ b - ∑ a, P a * q₂ a)) • (pr (S := S) (A := A) (s, b)) = _
  have hcoef : P b * (q₁ b - ∑ a, P a * q₁ a) - P b * (q₂ b - ∑ a, P a * q₂ a)
      = P b * ((q₁ b - q₂ b) - ∑ a, P a * (q₁ a - q₂ a)) := by
    have : ∑ a, P a * (q₁ a - q₂ a) = (∑ a, P a * q₁ a) - ∑ a, P a * q₂ a := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this]; ring
  calc (P b * (q₁ b - ∑ a, P a * q₁ a)) • (pr (S := S) (A := A) (s, b))
        - (P b * (q₂ b - ∑ a, P a * q₂ a)) • (pr (S := S) (A := A) (s, b))
      = (P b * (q₁ b - ∑ a, P a * q₁ a) - P b * (q₂ b - ∑ a, P a * q₂ a))
          • (pr (S := S) (A := A) (s, b)) := by module
    _ = (P b * ((q₁ b - q₂ b) - ∑ a, P a * (q₁ a - q₂ a)))
          • (pr (S := S) (A := A) (s, b)) := by rw [hcoef]

/-! ### The gradient map of the finite-horizon value is `8/(1-γ)³`-Lipschitz -/

/-- **The key induction.** The Lipschitz constant of `DW (n+1)` is at most
`6/(1-γ) + 8γ/(1-γ)² + γ ·` that of `DW n`; `8/(1-γ)³` is a fixed point of that
recursion with room to spare (`-2(1-γ)²` of slack per step). -/
theorem DW_lipschitz (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (n : ℕ) (θ₁ θ₂ : E S A) (s : S) :
    ‖DW M n θ₁ s - DW M n θ₂ s‖ ≤ 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hdn : (0:ℝ) ≤ ‖θ₁ - θ₂‖ := norm_nonneg _
  induction n generalizing s with
  | zero =>
    simp only [DW_zero, sub_zero, norm_zero]
    positivity
  | succ n ih =>
    rw [DW_succ, DW_succ]
    set Q : E S A → A → ℝ :=
      fun θ a => M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s' with hQ
    set T : E S A → A → (E S A →L[ℝ] ℝ) :=
      fun θ a => ∑ s', ((M.P s a) s' • DW M n θ s') with hT
    -- bounds on the pieces
    have hQb : ∀ θ a, |Q θ a| ≤ 1 / (1 - M.γ) := by
      intro θ a
      have hin : |∑ s', (M.P s a) s' * W M n θ s'| ≤ 1 / (1 - M.γ) := by
        calc |∑ s', (M.P s a) s' * W M n θ s'|
            ≤ ∑ s', |(M.P s a) s' * W M n θ s'| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ s', (M.P s a) s' * |W M n θ s'| := by
              refine Finset.sum_congr rfl fun s' _ => ?_
              rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
          _ ≤ ∑ s', (M.P s a) s' * (1 / (1 - M.γ)) :=
              Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (abs_W_le M hr hγ₀ hγ₁ n θ s') ((M.P s a).nonneg s')
          _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
      calc |Q θ a| ≤ |M.r s a| + |M.γ * ∑ s', (M.P s a) s' * W M n θ s'| := abs_add_le _ _
        _ ≤ 1 + M.γ * (1 / (1 - M.γ)) := by
            refine add_le_add (hr s a) ?_
            rw [abs_mul, abs_of_nonneg hγ₀]
            exact mul_le_mul_of_nonneg_left hin hγ₀
        _ = 1 / (1 - M.γ) := by field_simp; ring
    have hQd : ∀ a, |Q θ₁ a - Q θ₂ a| ≤ M.γ * (2 / (1 - M.γ) ^ 2) * ‖θ₁ - θ₂‖ := by
      intro a
      have hexp : Q θ₁ a - Q θ₂ a
          = M.γ * ∑ s', (M.P s a) s' * (W M n θ₁ s' - W M n θ₂ s') := by
        rw [hQ]
        have : ∑ s', (M.P s a) s' * (W M n θ₁ s' - W M n θ₂ s')
            = (∑ s', (M.P s a) s' * W M n θ₁ s') - ∑ s', (M.P s a) s' * W M n θ₂ s' := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s' _ => by ring
        rw [this]; ring
      rw [hexp, abs_mul, abs_of_nonneg hγ₀, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hγ₀
      calc |∑ s', (M.P s a) s' * (W M n θ₁ s' - W M n θ₂ s')|
          ≤ ∑ s', |(M.P s a) s' * (W M n θ₁ s' - W M n θ₂ s')| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s', (M.P s a) s' * |W M n θ₁ s' - W M n θ₂ s'| := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
        _ ≤ ∑ s', (M.P s a) s' * (2 / (1 - M.γ) ^ 2 * ‖θ₁ - θ₂‖) :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (W_lipschitz M hr hγ₀ hγ₁ n θ₁ θ₂ s')
                ((M.P s a).nonneg s')
        _ = 2 / (1 - M.γ) ^ 2 * ‖θ₁ - θ₂‖ := by
            rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    have hTb : ∀ θ a, ‖T θ a‖ ≤ 2 / (1 - M.γ) ^ 2 := by
      intro θ a
      calc ‖T θ a‖ ≤ ∑ s', ‖(M.P s a) s' • DW M n θ s'‖ := norm_sum_le _ _
        _ = ∑ s', (M.P s a) s' * ‖DW M n θ s'‖ := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((M.P s a).nonneg s')]
        _ ≤ ∑ s', (M.P s a) s' * (2 / (1 - M.γ) ^ 2) :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (norm_DW_le M hr hγ₀ hγ₁ n θ s') ((M.P s a).nonneg s')
        _ = 2 / (1 - M.γ) ^ 2 := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    have hTd : ∀ a, ‖T θ₁ a - T θ₂ a‖ ≤ 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
      intro a
      have hexp : T θ₁ a - T θ₂ a
          = ∑ s', ((M.P s a) s' • (DW M n θ₁ s' - DW M n θ₂ s')) := by
        rw [hT, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s' _ => by rw [smul_sub]
      rw [hexp]
      calc ‖∑ s', ((M.P s a) s' • (DW M n θ₁ s' - DW M n θ₂ s'))‖
          ≤ ∑ s', ‖(M.P s a) s' • (DW M n θ₁ s' - DW M n θ₂ s')‖ := norm_sum_le _ _
        _ = ∑ s', (M.P s a) s' * ‖DW M n θ₁ s' - DW M n θ₂ s'‖ := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((M.P s a).nonneg s')]
        _ ≤ ∑ s', (M.P s a) s' * (8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖) :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (ih s') ((M.P s a).nonneg s')
        _ = 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
            rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    -- split the two sums
    have hsplit : ∀ θ : E S A,
        ∑ a, ((Q θ a) • dp (S := S) (A := A) s a θ
          + (p (S := S) (A := A) s a θ * M.γ) • T θ a)
        = dg (S := S) (A := A) s (Q θ) θ
          + M.γ • ∑ a, (p (S := S) (A := A) s a θ) • T θ a := by
      intro θ
      rw [Finset.sum_add_distrib, sum_smul_dp_eq_dg]
      congr 1
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_smul, mul_comm]
    rw [hsplit θ₁, hsplit θ₂]
    -- the four estimates
    have hA : ‖dg (S := S) (A := A) s (Q θ₁) θ₁ - dg (S := S) (A := A) s (Q θ₂) θ₂‖
        ≤ (6 / (1 - M.γ) + M.γ * (4 / (1 - M.γ) ^ 2)) * ‖θ₁ - θ₂‖ := by
      have hsp : dg (S := S) (A := A) s (Q θ₁) θ₁ - dg (S := S) (A := A) s (Q θ₂) θ₂
          = (dg (S := S) (A := A) s (Q θ₁) θ₁ - dg (S := S) (A := A) s (Q θ₁) θ₂)
            + (dg (S := S) (A := A) s (Q θ₁) θ₂ - dg (S := S) (A := A) s (Q θ₂) θ₂) := by
        abel
      rw [hsp]
      refine le_trans (norm_add_le _ _) ?_
      have h1 : ‖dg (S := S) (A := A) s (Q θ₁) θ₁ - dg (S := S) (A := A) s (Q θ₁) θ₂‖
          ≤ 6 * (1 / (1 - M.γ)) * ‖θ₁ - θ₂‖ :=
        dg_lipschitz s (Q θ₁) (1 / (1 - M.γ)) (hQb θ₁) θ₁ θ₂
      have h2 : ‖dg (S := S) (A := A) s (Q θ₁) θ₂ - dg (S := S) (A := A) s (Q θ₂) θ₂‖
          ≤ 2 * (M.γ * (2 / (1 - M.γ) ^ 2) * ‖θ₁ - θ₂‖) := by
        rw [dg_sub]
        exact norm_dg_le s (fun a => Q θ₁ a - Q θ₂ a) _ hQd θ₂
      have := add_le_add h1 h2
      calc ‖dg (S := S) (A := A) s (Q θ₁) θ₁ - dg (S := S) (A := A) s (Q θ₁) θ₂‖
            + ‖dg (S := S) (A := A) s (Q θ₁) θ₂ - dg (S := S) (A := A) s (Q θ₂) θ₂‖
          ≤ 6 * (1 / (1 - M.γ)) * ‖θ₁ - θ₂‖ + 2 * (M.γ * (2 / (1 - M.γ) ^ 2) * ‖θ₁ - θ₂‖) := this
        _ = (6 / (1 - M.γ) + M.γ * (4 / (1 - M.γ) ^ 2)) * ‖θ₁ - θ₂‖ := by ring
    have hB : ‖(∑ a, (p (S := S) (A := A) s a θ₁) • T θ₁ a)
          - ∑ a, (p (S := S) (A := A) s a θ₂) • T θ₂ a‖
        ≤ (2 * (2 / (1 - M.γ) ^ 2) + 8 / (1 - M.γ) ^ 3) * ‖θ₁ - θ₂‖ := by
      have hsp : (∑ a, (p (S := S) (A := A) s a θ₁) • T θ₁ a)
            - ∑ a, (p (S := S) (A := A) s a θ₂) • T θ₂ a
          = ∑ a, ((p (S := S) (A := A) s a θ₁ - p (S := S) (A := A) s a θ₂) • T θ₁ a
              + (p (S := S) (A := A) s a θ₂) • (T θ₁ a - T θ₂ a)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        module
      rw [hsp]
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ a : A,
          ‖(p (S := S) (A := A) s a θ₁ - p (S := S) (A := A) s a θ₂) • T θ₁ a
            + (p (S := S) (A := A) s a θ₂) • (T θ₁ a - T θ₂ a)‖
          ≤ |p (S := S) (A := A) s a θ₁ - p (S := S) (A := A) s a θ₂| * (2 / (1 - M.γ) ^ 2)
            + p (S := S) (A := A) s a θ₂ * (8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖) := by
        intro a
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hTb θ₁ a) (abs_nonneg _)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (p_nonneg (S := S) (A := A) s a θ₂)]
          exact mul_le_mul_of_nonneg_left (hTd a) (p_nonneg (S := S) (A := A) s a θ₂)
      calc ∑ a, ‖(p (S := S) (A := A) s a θ₁ - p (S := S) (A := A) s a θ₂) • T θ₁ a
              + (p (S := S) (A := A) s a θ₂) • (T θ₁ a - T θ₂ a)‖
          ≤ ∑ a, (|p (S := S) (A := A) s a θ₁ - p (S := S) (A := A) s a θ₂| * (2 / (1 - M.γ) ^ 2)
              + p (S := S) (A := A) s a θ₂ * (8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖)) :=
            Finset.sum_le_sum fun a _ => hterm a
        _ = (∑ a, |p (S := S) (A := A) s a θ₁ - p (S := S) (A := A) s a θ₂|)
              * (2 / (1 - M.γ) ^ 2) + 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
              p_sum_eq_one, one_mul]
        _ ≤ (2 * ‖θ₁ - θ₂‖) * (2 / (1 - M.γ) ^ 2) + 8 / (1 - M.γ) ^ 3 * ‖θ₁ - θ₂‖ := by
            have hp := sum_abs_p_sub_le (S := S) (A := A) s θ₁ θ₂
            have hc : (0:ℝ) ≤ 2 / (1 - M.γ) ^ 2 := by positivity
            nlinarith
        _ = (2 * (2 / (1 - M.γ) ^ 2) + 8 / (1 - M.γ) ^ 3) * ‖θ₁ - θ₂‖ := by ring
    -- combine
    have hcomb : ‖(dg (S := S) (A := A) s (Q θ₁) θ₁
          + M.γ • ∑ a, (p (S := S) (A := A) s a θ₁) • T θ₁ a)
        - (dg (S := S) (A := A) s (Q θ₂) θ₂
          + M.γ • ∑ a, (p (S := S) (A := A) s a θ₂) • T θ₂ a)‖
        ≤ (6 / (1 - M.γ) + M.γ * (4 / (1 - M.γ) ^ 2)) * ‖θ₁ - θ₂‖
          + M.γ * ((2 * (2 / (1 - M.γ) ^ 2) + 8 / (1 - M.γ) ^ 3) * ‖θ₁ - θ₂‖) := by
      have hre : (dg (S := S) (A := A) s (Q θ₁) θ₁
            + M.γ • ∑ a, (p (S := S) (A := A) s a θ₁) • T θ₁ a)
          - (dg (S := S) (A := A) s (Q θ₂) θ₂
            + M.γ • ∑ a, (p (S := S) (A := A) s a θ₂) • T θ₂ a)
          = (dg (S := S) (A := A) s (Q θ₁) θ₁ - dg (S := S) (A := A) s (Q θ₂) θ₂)
            + M.γ • ((∑ a, (p (S := S) (A := A) s a θ₁) • T θ₁ a)
              - ∑ a, (p (S := S) (A := A) s a θ₂) • T θ₂ a) := by
        rw [smul_sub]; abel
      rw [hre]
      refine le_trans (norm_add_le _ _) (add_le_add hA ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ₀]
      exact mul_le_mul_of_nonneg_left hB hγ₀
    refine le_trans hcomb ?_
    have hkey : (6 / (1 - M.γ) + M.γ * (4 / (1 - M.γ) ^ 2))
        + M.γ * (2 * (2 / (1 - M.γ) ^ 2) + 8 / (1 - M.γ) ^ 3) ≤ 8 / (1 - M.γ) ^ 3 := by
      rw [← sub_nonneg]
      have expand : 8 / (1 - M.γ) ^ 3
          - ((6 / (1 - M.γ) + M.γ * (4 / (1 - M.γ) ^ 2))
            + M.γ * (2 * (2 / (1 - M.γ) ^ 2) + 8 / (1 - M.γ) ^ 3))
          = (2 * (1 - M.γ) ^ 2) / (1 - M.γ) ^ 3 := by
        field_simp; ring
      rw [expand]
      positivity
    nlinarith [hdn]


/-! ### Geometric control of the horizon increments -/

theorem abs_W_succ_sub (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ)
    (n : ℕ) (θ : E S A) (s : S) : |W M (n + 1) θ s - W M n θ s| ≤ M.γ ^ n := by
  induction n generalizing s with
  | zero =>
    simp only [W_zero, sub_zero, pow_zero, W_succ]
    have : ∀ a : A, |p (S := S) (A := A) s a θ
        * (M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ))| ≤ p (S := S) (A := A) s a θ * 1 := by
      intro a
      rw [abs_mul, abs_of_nonneg (p_nonneg (S := S) (A := A) s a θ)]
      refine mul_le_mul_of_nonneg_left ?_ (p_nonneg (S := S) (A := A) s a θ)
      simpa using hr s a
    calc |∑ a, p (S := S) (A := A) s a θ * (M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ))|
        ≤ ∑ a, |p (S := S) (A := A) s a θ
            * (M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, p (S := S) (A := A) s a θ * 1 := Finset.sum_le_sum fun a _ => this a
      _ = 1 := by rw [← Finset.sum_mul, p_sum_eq_one, one_mul]
  | succ n ih =>
    rw [W_succ, W_succ, ← Finset.sum_sub_distrib]
    have hterm : ∀ a : A,
        |p (S := S) (A := A) s a θ * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s')
          - p (S := S) (A := A) s a θ * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')|
        ≤ p (S := S) (A := A) s a θ * (M.γ * M.γ ^ n) := by
      intro a
      have hexp : p (S := S) (A := A) s a θ
            * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s')
          - p (S := S) (A := A) s a θ * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')
          = p (S := S) (A := A) s a θ * (M.γ
              * ∑ s', (M.P s a) s' * (W M (n + 1) θ s' - W M n θ s')) := by
        have hd : ∑ s', (M.P s a) s' * (W M (n + 1) θ s' - W M n θ s')
            = (∑ s', (M.P s a) s' * W M (n + 1) θ s') - ∑ s', (M.P s a) s' * W M n θ s' := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s' _ => by ring
        rw [hd]; ring
      rw [hexp, abs_mul, abs_of_nonneg (p_nonneg (S := S) (A := A) s a θ)]
      refine mul_le_mul_of_nonneg_left ?_ (p_nonneg (S := S) (A := A) s a θ)
      rw [abs_mul, abs_of_nonneg hγ₀]
      refine mul_le_mul_of_nonneg_left ?_ hγ₀
      calc |∑ s', (M.P s a) s' * (W M (n + 1) θ s' - W M n θ s')|
          ≤ ∑ s', |(M.P s a) s' * (W M (n + 1) θ s' - W M n θ s')| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s', (M.P s a) s' * |W M (n + 1) θ s' - W M n θ s'| := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
        _ ≤ ∑ s', (M.P s a) s' * M.γ ^ n :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (ih s') ((M.P s a).nonneg s')
        _ = M.γ ^ n := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    calc |∑ a, (p (S := S) (A := A) s a θ
              * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s')
            - p (S := S) (A := A) s a θ
              * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s'))|
        ≤ ∑ a, |p (S := S) (A := A) s a θ
              * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s')
            - p (S := S) (A := A) s a θ
              * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, p (S := S) (A := A) s a θ * (M.γ * M.γ ^ n) :=
          Finset.sum_le_sum fun a _ => hterm a
      _ = M.γ ^ (n + 1) := by
          rw [← Finset.sum_mul, p_sum_eq_one, one_mul, pow_succ]; ring


/-- The horizon increments of the gradient decay like `n γⁿ`, which is summable:
each extra step of horizon adds one discounted copy of the value increment
through the score, and passes the previous gradient increment through the
kernel. -/
theorem norm_DW_succ_sub (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ)
    (n : ℕ) (θ : E S A) (s : S) :
    ‖DW M (n + 1) θ s - DW M n θ s‖ ≤ 2 * (n + 1) * M.γ ^ n := by
  induction n generalizing s with
  | zero =>
    simp only [DW_zero, sub_zero, pow_zero, Nat.cast_zero, DW_succ, W_zero]
    have hterm : ∀ a : A,
        ‖((M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ)) • dp (S := S) (A := A) s a θ
          + (p (S := S) (A := A) s a θ * M.γ) • ∑ s' : S, ((M.P s a) s' • (0 : E S A →L[ℝ] ℝ)))‖
        ≤ ‖dp (S := S) (A := A) s a θ‖ := by
      intro a
      have hz : ∑ s' : S, ((M.P s a) s' • (0 : E S A →L[ℝ] ℝ)) = 0 := by simp
      rw [hz, smul_zero, add_zero, norm_smul, Real.norm_eq_abs]
      have : |M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ)| ≤ 1 := by simpa using hr s a
      nlinarith [norm_nonneg (dp (S := S) (A := A) s a θ), abs_nonneg
        (M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ))]
    calc ‖∑ a, ((M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ)) • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ) • ∑ s' : S, ((M.P s a) s' • (0 : E S A →L[ℝ] ℝ)))‖
        ≤ ∑ a, ‖((M.r s a + M.γ * ∑ s', (M.P s a) s' * (0:ℝ)) • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ)
              • ∑ s' : S, ((M.P s a) s' • (0 : E S A →L[ℝ] ℝ)))‖ := norm_sum_le _ _
      _ ≤ ∑ a, ‖dp (S := S) (A := A) s a θ‖ := Finset.sum_le_sum fun a _ => hterm a
      _ ≤ 2 := sum_norm_dp_le (S := S) (A := A) s θ
      _ = 2 * (0 + 1) * 1 := by ring
  | succ n ih =>
    rw [DW_succ, DW_succ, ← Finset.sum_sub_distrib]
    have hQd : ∀ a : A,
        |(M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s')
          - (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')| ≤ M.γ * M.γ ^ n := by
      intro a
      have hexp : (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s')
            - (M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')
          = M.γ * ∑ s', (M.P s a) s' * (W M (n + 1) θ s' - W M n θ s') := by
        have hd : ∑ s', (M.P s a) s' * (W M (n + 1) θ s' - W M n θ s')
            = (∑ s', (M.P s a) s' * W M (n + 1) θ s') - ∑ s', (M.P s a) s' * W M n θ s' := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun s' _ => by ring
        rw [hd]; ring
      rw [hexp, abs_mul, abs_of_nonneg hγ₀]
      refine mul_le_mul_of_nonneg_left ?_ hγ₀
      calc |∑ s', (M.P s a) s' * (W M (n + 1) θ s' - W M n θ s')|
          ≤ ∑ s', |(M.P s a) s' * (W M (n + 1) θ s' - W M n θ s')| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s', (M.P s a) s' * |W M (n + 1) θ s' - W M n θ s'| := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
        _ ≤ ∑ s', (M.P s a) s' * M.γ ^ n :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (abs_W_succ_sub M hr hγ₀ n θ s') ((M.P s a).nonneg s')
        _ = M.γ ^ n := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    have hTd : ∀ a : A,
        ‖(∑ s' : S, ((M.P s a) s' • DW M (n + 1) θ s'))
          - ∑ s' : S, ((M.P s a) s' • DW M n θ s')‖ ≤ 2 * (n + 1) * M.γ ^ n := by
      intro a
      have hexp : (∑ s' : S, ((M.P s a) s' • DW M (n + 1) θ s'))
            - ∑ s' : S, ((M.P s a) s' • DW M n θ s')
          = ∑ s' : S, ((M.P s a) s' • (DW M (n + 1) θ s' - DW M n θ s')) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s' _ => by module
      rw [hexp]
      calc ‖∑ s' : S, ((M.P s a) s' • (DW M (n + 1) θ s' - DW M n θ s'))‖
          ≤ ∑ s', ‖(M.P s a) s' • (DW M (n + 1) θ s' - DW M n θ s')‖ := norm_sum_le _ _
        _ = ∑ s', (M.P s a) s' * ‖DW M (n + 1) θ s' - DW M n θ s'‖ := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((M.P s a).nonneg s')]
        _ ≤ ∑ s', (M.P s a) s' * (2 * (n + 1) * M.γ ^ n) :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (ih s') ((M.P s a).nonneg s')
        _ = 2 * (n + 1) * M.γ ^ n := by
            rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
    have hterm : ∀ a : A,
        ‖(((M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s')
              • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ)
              • ∑ s' : S, ((M.P s a) s' • DW M (n + 1) θ s'))
          - ((M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s')
              • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ)
              • ∑ s' : S, ((M.P s a) s' • DW M n θ s')))‖
        ≤ (M.γ * M.γ ^ n) * ‖dp (S := S) (A := A) s a θ‖
          + p (S := S) (A := A) s a θ * (M.γ * (2 * (n + 1) * M.γ ^ n)) := by
      intro a
      set QA := M.r s a + M.γ * ∑ s', (M.P s a) s' * W M (n + 1) θ s' with hQA
      set QB := M.r s a + M.γ * ∑ s', (M.P s a) s' * W M n θ s' with hQB
      set TA := ∑ s' : S, ((M.P s a) s' • DW M (n + 1) θ s') with hTA
      set TB := ∑ s' : S, ((M.P s a) s' • DW M n θ s') with hTB
      have hre : (QA • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ) • TA)
          - (QB • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ) • TB)
          = (QA - QB) • dp (S := S) (A := A) s a θ
            + (p (S := S) (A := A) s a θ * M.γ) • (TA - TB) := by module
      rw [hre]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hQd a) (norm_nonneg _)
      · rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (p_nonneg (S := S) (A := A) s a θ) hγ₀), mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hTd a) hγ₀) (p_nonneg (S := S) (A := A) s a θ)
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun a _ => hterm a) ?_
    have hsum : ∑ a, ((M.γ * M.γ ^ n) * ‖dp (S := S) (A := A) s a θ‖
          + p (S := S) (A := A) s a θ * (M.γ * (2 * (n + 1) * M.γ ^ n)))
        = (M.γ * M.γ ^ n) * (∑ a, ‖dp (S := S) (A := A) s a θ‖)
          + M.γ * (2 * (n + 1) * M.γ ^ n) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, p_sum_eq_one, one_mul]
    rw [hsum]
    have hdp := sum_norm_dp_le (S := S) (A := A) s θ
    have hgn : (0:ℝ) ≤ M.γ ^ n := pow_nonneg hγ₀ n
    have hgg : (0:ℝ) ≤ M.γ * M.γ ^ n := mul_nonneg hγ₀ hgn
    have hb : (M.γ * M.γ ^ n) * (∑ a, ‖dp (S := S) (A := A) s a θ‖)
        ≤ (M.γ * M.γ ^ n) * 2 := mul_le_mul_of_nonneg_left hdp hgg
    have hgoal : (M.γ * M.γ ^ n) * 2 + M.γ * (2 * (n + 1) * M.γ ^ n)
        = 2 * ((n : ℝ) + 1 + 1) * M.γ ^ (n + 1) := by rw [pow_succ]; ring
    push_cast
    linarith [hb, hgoal.le, hgoal.ge]

end G7b

end Proofs
end PolicyGradient
