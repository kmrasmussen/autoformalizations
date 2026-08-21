/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.GradientDomination
import PolicyGradient.Rate

/-!
# Agarwal–Kakade–Lee–Mahajan: the ascent machinery

*On the Theory of Policy Gradient Methods: Optimality, Approximation, and
Distribution Shift*, JMLR 22(98), 2021.

This file develops the optimization-side machinery of the paper — the smoothness
predicate the ascent lemma needs, and the ascent lemma itself — in the form the
convergence theorems consume.

## Smoothness

AKM (and Mei et al.) use a **two-sided second-order Taylor bound**, not a
Lipschitz-gradient condition:

  `|f(θ') - f(θ) - ⟨∇f(θ), θ' - θ⟩| ≤ (β/2)‖θ' - θ‖²`

Mathlib has no predicate in this form, so we define it.
-/

open Finset

namespace PolicyGradient

/-- `β`-smoothness in the sense used by AKM: a two-sided second-order Taylor
bound. Stated for a one-dimensional parameter, which is what the `HasDerivAt`
development uses. -/
def SmoothAt (f : ℝ → ℝ) (f' : ℝ → ℝ) (β : ℝ) : Prop :=
  ∀ x y : ℝ, |f y - f x - f' x * (y - x)| ≤ β / 2 * (y - x) ^ 2

/-- **The ascent lemma.** One gradient-ascent step with stepsize `η = 1/β` on a
`β`-smooth function increases the value by at least `(1/(2β))·|f'|²`.

This is AKM's Lemma (and Mei et al.'s Lemma 17): the engine that converts a
lower bound on the gradient into per-step progress. -/
theorem ascent_step {f f' : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hs : SmoothAt f f' β)
    (x : ℝ) :
    f x + 1 / (2 * β) * (f' x) ^ 2 ≤ f (x + (1 / β) * f' x) := by
  set y := x + (1 / β) * f' x with hy
  have hdiff : y - x = (1 / β) * f' x := by rw [hy]; ring
  have h := hs x y
  rw [abs_le] at h
  have hlow := h.1
  rw [hdiff] at hlow
  have hβ' : β ≠ 0 := ne_of_gt hβ
  have expand : f' x * ((1 / β) * f' x) - β / 2 * ((1 / β) * f' x) ^ 2
      = 1 / (2 * β) * (f' x) ^ 2 := by
    field_simp
    ring
  nlinarith [hlow, expand]

end PolicyGradient
