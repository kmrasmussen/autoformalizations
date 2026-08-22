/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Chain
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

/-!
### The softmax score

`∂π_θ(a|s)/∂θ_{s,b} = π_θ(a|s) · ([a = b] - π_θ(b|s))`.
-/

variable [Nonempty A]

/-- The softmax score: the derivative of `softmax w a` with respect to `w b`. -/
noncomputable def softmaxScore (w : A → ℝ) (a b : A) : ℝ :=
  (softmax w) a * ((if a = b then 1 else 0) - (softmax w) b)

/-- The scores at a state sum to zero over actions — the reason the policy
gradient is invariant to adding a constant to all logits. -/
theorem softmaxScore_sum_eq_zero (w : A → ℝ) (b : A) :
    ∑ a, softmaxScore w a b = 0 := by
  have expand : ∀ a, softmaxScore w a b
      = (if a = b then (softmax w) a else 0) - (softmax w) a * (softmax w) b := by
    intro a
    unfold softmaxScore
    by_cases h : a = b <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl (fun a _ => expand a)]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq' univ b (fun a => (softmax w) a)]
  rw [← Finset.sum_mul, (softmax w).sum_eq_one, one_mul]
  simp

/-!
### The softmax policy family

A softmax-parameterized family of policies, and the fact that its score is the
`softmaxScore` above.

**This does not yet package a `DiffPolicy`** (gap **G6**): `softmaxPolicy`
returns a bare `ℝ → Policy S A`, and no differentiability proof is given. So the
policy gradient theorem is **not** currently applicable to softmax policies, and
`sum_abs_score_le_one` has no Lean-level link to the `hscore` hypothesis of
`smoothAt_V_final`. Building `softmaxC2Policy` is what closes this.
-/

/-- A softmax policy family driven by logits that depend on the parameter. -/
noncomputable def softmaxPolicy (logits : ℝ → S → A → ℝ) : ℝ → Policy S A :=
  fun θ s => softmax (logits θ s)

@[simp] theorem softmaxPolicy_apply (logits : ℝ → S → A → ℝ) (θ : ℝ) (s : S) (a : A) :
    (softmaxPolicy logits θ s) a
      = Real.exp (logits θ s a) / ∑ a', Real.exp (logits θ s a') := rfl

/-- Softmax policies assign strictly positive probability to every action, at
every parameter value. This is the property AKM's global-convergence argument
relies on: no action is ever permanently ruled out. -/
theorem softmaxPolicy_pos (logits : ℝ → S → A → ℝ) (θ : ℝ) (s : S) (a : A) :
    0 < (softmaxPolicy logits θ s) a :=
  softmax_pos _ _

/-!
### AKM Lemma C.1 — the softmax policy gradient

For softmax parameterization the policy gradient has the closed form

  `∂V/∂θ_{s,a} = (1/(1-γ)) · d^π(s) · π(a|s) · A^π(s,a)`

The `π(a|s)·A(s,a)` factor is `softmaxScore` contracted against the advantage;
the `d^π(s)` is the occupancy weighting from the policy gradient theorem. Here
we prove the state-local part: the score contracted against `Q` equals the score
contracted against the *advantage*, because the scores sum to zero.
-/

variable (M : FiniteMDP S A)

/-- **The score-advantage identity.** Contracting the softmax score against `Q`
gives the same result as contracting it against the advantage `Q - V`.

This is why the policy gradient can be written with advantages rather than
action-values, which is what makes the AKM/Mei analyses work: the advantage is
centered, so the gradient vanishes exactly at policies that are greedy. -/
theorem score_dot_Q_eq_score_dot_adv (w : A → ℝ) (q : A → ℝ) (v : ℝ) (b : A) :
    ∑ a, softmaxScore w a b * q a
      = ∑ a, softmaxScore w a b * (q a - v) := by
  have hsplit : ∑ a, softmaxScore w a b * (q a - v)
      = (∑ a, softmaxScore w a b * q a) - v * ∑ a, softmaxScore w a b := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hsplit, softmaxScore_sum_eq_zero]
  ring

/-- The softmax score contracted against a constant is zero. -/
theorem score_dot_const (w : A → ℝ) (v : ℝ) (b : A) :
    ∑ a, softmaxScore w a b * v = 0 := by
  rw [← Finset.sum_mul, softmaxScore_sum_eq_zero, zero_mul]

end PolicyGradient
