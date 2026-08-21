/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Softmax

/-!
# Gradient domination

Agarwal–Kakade–Lee–Mahajan (JMLR 22(98), 2021), Lemma 4.1.

The suboptimality of a policy is controlled by how much a *better* policy could
gain against it. This is what converts a statement about gradients (local) into
a statement about the global optimum, and it is the reason policy gradient
methods find global optima despite the objective being non-convex.

Everything here is stated in the finite-horizon vocabulary of the rest of the
development, so `performance_difference` does the work.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
variable (M : FiniteMDP S A)

/-- **Suboptimality equals the visitation-weighted advantage gap.**

For any comparison policy `π*`, the shortfall of `π` against `π*` from `s₀` is
exactly the `π*`-visitation-weighted advantage of `π`:

  `V^π*(s₀) - V^π(s₀) = ∑ₖ γᵏ ∑ₛ visit^π* k s₀ s · advGap^{π*,π}(s)`

This is `performance_difference` read as a statement about suboptimality, and it
is the first half of gradient domination: it says the only way `π` can be far
from optimal is for some state that `π*` visits to have a large advantage gap. -/
theorem suboptimality_eq (π πstar : Policy S A) (m : ℕ) (s₀ : S) :
    V M πstar m s₀ - V M π m s₀ = pdSum M πstar π m s₀ :=
  performance_difference M πstar π m s₀

/-- If no state has a positive advantage gap under `π*`'s visitation, then `π`
is at least as good as `π*`. The contrapositive of gradient domination. -/
theorem le_of_advGap_nonpos (π πstar : Policy S A) (m : ℕ) (s₀ : S)
    (hγ₀ : 0 ≤ M.γ)
    (h : ∀ k s, advGap M πstar π (m - 1 - k) s ≤ 0) :
    V M πstar m s₀ ≤ V M π m s₀ := by
  have hpd := suboptimality_eq M π πstar m s₀
  have hle : pdSum M πstar π m s₀ ≤ 0 := by
    unfold pdSum
    refine Finset.sum_nonpos fun k _ => ?_
    refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ₀ k) ?_
    refine Finset.sum_nonpos fun s _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (visit_nonneg M πstar k s₀ s) (h k s)
  linarith

end PolicyGradient
