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

/-!
### Optimality certificates

The converse direction: a policy with no improving advantage anywhere is
optimal against *every* comparison policy — the global-optimality conclusion.
-/

/-- **Global optimality from a local condition.**

If under every policy's visitation no state has a positive advantage gap
against `π`, then `π` is optimal: no policy beats it from any start state.

This is the shape of AKM Theorem 5.1's conclusion. The content is that a purely
*local* condition (nothing to gain by deviating at any state) certifies a
*global* property (optimality), which is exactly what one cannot conclude for a
general non-convex objective — it holds here because of the MDP structure that
`performance_difference` encodes. -/
theorem optimal_of_no_advantage (π : Policy S A) (m : ℕ) (hγ₀ : 0 ≤ M.γ)
    (h : ∀ (πstar : Policy S A) (j : ℕ) (s : S), advGap M πstar π j s ≤ 0) :
    ∀ (πstar : Policy S A) (s₀ : S), V M πstar m s₀ ≤ V M π m s₀ := by
  intro πstar s₀
  exact le_of_advGap_nonpos M π πstar m s₀ hγ₀ (fun k s => h πstar (m - 1 - k) s)

/-- The advantage gap against `π` is nonpositive at `s` exactly when no action
distribution beats `π`'s own — the pointwise optimality condition. -/
theorem advGap_nonpos_iff (π πstar : Policy S A) (j : ℕ) (s : S) :
    advGap M πstar π j s ≤ 0
      ↔ ∑ a, (πstar s) a * Q M π j s a ≤ V M π (j + 1) s := by
  unfold advGap adv
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (πstar s).sum_eq_one, one_mul]
  constructor <;> intro h <;> linarith

end PolicyGradient
