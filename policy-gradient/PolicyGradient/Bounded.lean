/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Chain

/-!
# Uniform bounds on rewards and finite-horizon values

Groundwork for the infinite-horizon theory: `V_m` is bounded uniformly in `m`,
and `V_m` is Cauchy at geometric rate. Both follow from `S` and `A` being
finite, so no boundedness hypothesis needs to be added to `FiniteMDP`.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
variable (M : FiniteMDP S A)

/-- Rewards are bounded: `S` and `A` are finite, so `|r|` attains a maximum. -/
theorem exists_reward_bound [Nonempty S] [Nonempty A] :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s a, |M.r s a| ≤ R := by
  obtain ⟨sa, -, hsa⟩ :=
    Finset.exists_max_image (univ : Finset (S × A)) (fun p => |M.r p.1 p.2|)
      ⟨(Classical.arbitrary S, Classical.arbitrary A), mem_univ _⟩
  refine ⟨|M.r sa.1 sa.2|, abs_nonneg _, fun s a => hsa (s, a) (mem_univ _)⟩

/-- A convex combination under a `Dist` is bounded by a bound on the summands. -/
theorem Dist.expect_le {ι : Type*} [Fintype ι] (p : Dist ι) (f : ι → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, |f i| ≤ C) : |∑ i, p i * f i| ≤ C := by
  calc |∑ i, p i * f i| ≤ ∑ i, |p i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p i * |f i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (p.nonneg i)]
    _ ≤ ∑ i, p i * C := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (hf i) (p.nonneg i)
    _ = C := by rw [← Finset.sum_mul, p.sum_eq_one, one_mul]

/-- `V_m` is bounded uniformly in the horizon: `|V_m s| ≤ R * ∑_{i<m} γ^i`.

By induction: one more step adds at most `R` of immediate reward plus `γ` times
the previous bound. This is the estimate that makes `lim V_m` exist. -/
theorem abs_V_le (π : Policy S A) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ s a, |M.r s a| ≤ R) (hγ₀ : 0 ≤ M.γ) (m : ℕ) (s : S) :
    |V M π m s| ≤ R * ∑ i ∈ range m, M.γ ^ i := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [V_succ]
    have hQ : ∀ a, |Q M π m s a| ≤ R * ∑ i ∈ range (m + 1), M.γ ^ i := by
      intro a
      unfold Q
      have h1 : |M.γ * ∑ s', (M.P s a) s' * V M π m s'|
          ≤ M.γ * (R * ∑ i ∈ range m, M.γ ^ i) := by
        rw [abs_mul, abs_of_nonneg hγ₀]
        refine mul_le_mul_of_nonneg_left ?_ hγ₀
        exact Dist.expect_le (M.P s a) _ _ (by positivity) (fun s' => ih s')
      calc |M.r s a + M.γ * ∑ s', (M.P s a) s' * V M π m s'|
          ≤ |M.r s a| + |M.γ * ∑ s', (M.P s a) s' * V M π m s'| := abs_add_le _ _
        _ ≤ R + M.γ * (R * ∑ i ∈ range m, M.γ ^ i) := add_le_add (hr s a) h1
        _ = R * ∑ i ∈ range (m + 1), M.γ ^ i := by
            -- ∑_{i<m+1} γ^i = 1 + γ * ∑_{i<m} γ^i  (split off i = 0)
            rw [Finset.sum_range_succ']
            simp only [pow_zero, pow_succ]
            rw [← Finset.sum_mul]
            ring
    exact Dist.expect_le (π s) _ _ (by positivity) hQ

end PolicyGradient
