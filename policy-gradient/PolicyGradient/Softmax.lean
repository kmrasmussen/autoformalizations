/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.PerformanceDifference
import PolicyGradient.Infinite
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Softmax policies

The softmax parameterization `π_θ(a|s) = exp(θ_{s,a}) / ∑_{a'} exp(θ_{s,a'})`,
its score function, and the results of Agarwal–Kakade–Lee–Mahajan (JMLR 2021)
that depend on it.

## The score

`∂/∂θ_{s,a'} log π_θ(a|s) = [a = a'] - π_θ(a'|s)`, so

  `∂π_θ(a|s)/∂θ_{s,a'} = π_θ(a|s) · ([a = a'] - π_θ(a'|s))`

which is the identity every softmax policy-gradient computation runs on.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- The softmax distribution over actions determined by a score vector. -/
noncomputable def softmax [Nonempty A] (w : A → ℝ) : Dist A where
  prob a := Real.exp (w a) / ∑ a', Real.exp (w a')
  nonneg a := by
    have hpos : 0 < ∑ a', Real.exp (w a') :=
      Finset.sum_pos (fun a' _ => Real.exp_pos _) ⟨a, mem_univ a⟩
    positivity
  sum_eq_one := by
    have hpos : 0 < ∑ a', Real.exp (w a') :=
      Finset.sum_pos (fun a' _ => Real.exp_pos _) ⟨Classical.arbitrary A, mem_univ _⟩
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (ne_of_gt hpos)

@[simp] theorem softmax_apply [Nonempty A] (w : A → ℝ) (a : A) :
    (softmax w) a = Real.exp (w a) / ∑ a', Real.exp (w a') := rfl

/-- The softmax denominator is positive. -/
theorem softmax_denom_pos [Nonempty A] (w : A → ℝ) : 0 < ∑ a', Real.exp (w a') :=
  Finset.sum_pos (fun a' _ => Real.exp_pos _) ⟨Classical.arbitrary A, mem_univ _⟩

/-- Softmax probabilities are strictly positive — the fact that makes softmax
policies never permanently rule out an action. -/
theorem softmax_pos [Nonempty A] (w : A → ℝ) (a : A) : 0 < (softmax w) a := by
  rw [softmax_apply]
  exact div_pos (Real.exp_pos _) (softmax_denom_pos w)

end PolicyGradient
