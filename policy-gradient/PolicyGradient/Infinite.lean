/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Bounded
import PolicyGradient.Theorem

/-!
# Infinite-horizon values

`Vinf` is the expected discounted return over an unbounded horizon, defined as
the `tsum` of the per-step contributions. Well-definedness comes from bounded
rewards and `γ < 1` by geometric domination.

## Design

The finite-horizon `V m` is *not* discarded: `Vinf` is built so that the
finite-horizon results become the approximating sequence (`V m → Vinf`
geometrically at rate `γ`, checked numerically in `inf_horizon.py`).
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
variable (M : FiniteMDP S A)

/-- The per-step contribution to the return: the expected reward collected at
time `t`, already discounted. -/
noncomputable def stepReward (π : Policy S A) (t : ℕ) (s₀ : S) : ℝ :=
  M.γ ^ t * ∑ s, visit M π t s₀ s * ∑ a, (π s) a * M.r s a

/-- `visit` is a probability distribution over states at each time. -/
theorem visit_sum_eq_one (π : Policy S A) (t : ℕ) (s₀ : S) :
    ∑ s, visit M π t s₀ s = 1 := by
  induction t generalizing s₀ with
  | zero => simp [visit]
  | succ t ih =>
    simp only [visit_succ]
    rw [Finset.sum_comm]
    have : ∀ s' : S, ∑ s, visit M π t s₀ s' * step M π s' s
        = visit M π t s₀ s' := by
      intro s'
      rw [← Finset.mul_sum]
      unfold step
      rw [Finset.sum_comm]
      have hone : ∑ a, ∑ s, (π s') a * (M.P s' a) s = 1 := by
        rw [← (π s').sum_eq_one]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, (M.P s' a).sum_eq_one, mul_one]
      rw [hone, mul_one]
    rw [Finset.sum_congr rfl fun s' _ => this s']
    exact ih s₀

/-- `visit` is nonnegative. -/
theorem visit_nonneg (π : Policy S A) (t : ℕ) (s₀ s : S) :
    0 ≤ visit M π t s₀ s := by
  induction t generalizing s₀ s with
  | zero => unfold visit; split <;> norm_num
  | succ t ih =>
    rw [visit_succ]
    refine Finset.sum_nonneg fun s' _ => ?_
    refine mul_nonneg (ih s₀ s') ?_
    unfold step
    exact Finset.sum_nonneg fun a _ => mul_nonneg ((π s').nonneg a) ((M.P s' a).nonneg s)

/-- The expected reward collected at a single time step is bounded by `R`. -/
theorem abs_stepReward_le (π : Policy S A) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ s a, |M.r s a| ≤ R) (hγ₀ : 0 ≤ M.γ) (t : ℕ) (s₀ : S) :
    |stepReward M π t s₀| ≤ M.γ ^ t * R := by
  unfold stepReward
  rw [abs_mul, abs_of_nonneg (pow_nonneg hγ₀ t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ₀ t)
  -- the state distribution at time t is a probability vector
  calc |∑ s, visit M π t s₀ s * ∑ a, (π s) a * M.r s a|
      ≤ ∑ s, |visit M π t s₀ s * ∑ a, (π s) a * M.r s a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, visit M π t s₀ s * |∑ a, (π s) a * M.r s a| := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (visit_nonneg M π t s₀ s)]
    _ ≤ ∑ s, visit M π t s₀ s * R := by
        refine Finset.sum_le_sum fun s _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (visit_nonneg M π t s₀ s)
        exact Dist.expect_le (π s) _ R hR (fun a => hr s a)
    _ = R := by rw [← Finset.sum_mul, visit_sum_eq_one, one_mul]

/-- The discounted rewards are summable: geometric domination. -/
theorem summable_stepReward (π : Policy S A) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ s a, |M.r s a| ≤ R) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Summable (fun t => stepReward M π t s₀) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ₀ hγ₁).mul_right R) ?_
  intro t
  simpa [Real.norm_eq_abs] using abs_stepReward_le M π R hR hr hγ₀ t s₀

/-- **The infinite-horizon value function.** -/
noncomputable def Vinf (π : Policy S A) (s₀ : S) : ℝ :=
  ∑' t, stepReward M π t s₀

/-- **The discounted state-occupancy measure** `d^π(s₀, s) = ∑ₜ γᵗ Pr(sₜ = s)`.

Unnormalized: it sums to `1/(1-γ)`, not `1`. Sources that normalize it into a
probability distribution must carry a compensating `1/(1-γ)` in the policy
gradient theorem; ours does not. (Checked numerically in `inf_horizon.py`.) -/
noncomputable def dinf (π : Policy S A) (s₀ s : S) : ℝ :=
  ∑' t, M.γ ^ t * visit M π t s₀ s

theorem summable_dvisit (π : Policy S A) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ s : S) :
    Summable (fun t => M.γ ^ t * visit M π t s₀ s) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ₀ hγ₁).mul_right 1) ?_
  intro t
  have h1 : visit M π t s₀ s ≤ 1 := by
    have := visit_sum_eq_one M π t s₀
    have hle : visit M π t s₀ s ≤ ∑ s', visit M π t s₀ s' :=
      Finset.single_le_sum (fun s' _ => visit_nonneg M π t s₀ s') (mem_univ s)
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ₀ t),
      abs_of_nonneg (visit_nonneg M π t s₀ s), mul_one]
  simpa using mul_le_mul_of_nonneg_left h1 (pow_nonneg hγ₀ t)

/-- The infinite-horizon action-value. -/
noncomputable def Qinf (π : Policy S A) (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * ∑ s', (M.P s a) s' * Vinf M π s'

/-!
### The Bellman equation

`Vinf` was defined as a `tsum` over time. The Bellman equation is what connects
that to the recursive structure the finite-horizon development uses, and it is
the bridge every later result crosses.
-/

/-- The time-`t+1` visitation is the time-`t` visitation pushed one step. -/
theorem stepReward_succ (π : Policy S A) (t : ℕ) (s₀ : S) :
    stepReward M π (t + 1) s₀
      = M.γ * ∑ s', step M π s₀ s' * stepReward M π t s' := by
  unfold stepReward
  -- γ^(t+1) ∑_s visit (t+1) s₀ s · rbar s = γ · ∑_{s'} step s₀ s' · γ^t ∑_s visit t s' s · rbar s
  have hswap : ∑ s, visit M π (t + 1) s₀ s * ∑ a, (π s) a * M.r s a
      = ∑ s', step M π s₀ s' * ∑ s, visit M π t s' s * ∑ a, (π s) a * M.r s a := by
    calc ∑ s, visit M π (t + 1) s₀ s * ∑ a, (π s) a * M.r s a
        = ∑ s, (∑ s', step M π s₀ s' * visit M π t s' s) * ∑ a, (π s) a * M.r s a := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [step_visit M π t s₀ s]
      _ = ∑ s, ∑ s', step M π s₀ s' * (visit M π t s' s * ∑ a, (π s) a * M.r s a) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun s' _ => ?_
          ring
      _ = ∑ s', step M π s₀ s' * ∑ s, visit M π t s' s * ∑ a, (π s) a * M.r s a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [Finset.mul_sum]
  rw [hswap, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

end PolicyGradient
