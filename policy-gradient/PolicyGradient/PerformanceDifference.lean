/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Theorem

/-!
# The performance difference lemma, finite horizon

For two policies `π` and `π'`,

  V_m^π(s₀) - V_m^π'(s₀)
    = ∑_{k<m} γ^k ∑_s visit^π k s₀ s · ∑_a π(a|s) · A^π'_{m-1-k}(s,a)

where `A^π'_j(s,a) = Q^π'_j(s,a) - V^π'_{j+1}(s)` is the advantage.

## Notes

Kakade & Langford (2002); Agarwal, Kakade, Lee & Mahajan (JMLR 2021) Lemma 3.2.
The infinite-horizon statement carries a `1/(1-γ)` because it uses the
*normalized* occupancy measure. Our `visit` is unnormalized, so that factor is
absent and the discounting appears as the explicit `∑_{k<m} γ^k`.

The asymmetry is the whole content: the advantage is that of `π'`, but it is
averaged under `π`'s state visitation.

Index convention: `Q_j` pairs with `V_(j+1)`, since `V_(j+1) s = ∑ₐ π(a|s) Q_j s a`.
Verified numerically (`pdl_check.py`) before proving.

## Reuse

This file shares the entire vocabulary of the policy gradient development —
`V`, `Q`, `visit`, `step`, and the `∑ₖ γᵏ ∑ₛ visit k` weighting with the same
`m-1-k` indexing — and its induction turns on `step_visit`, the same
Chapman-Kolmogorov lemma that `step_pgSum` needs.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
variable (M : FiniteMDP S A)

/-- The advantage of policy `π` at horizon `j`: how much better taking `a` now is
than acting under `π`, when `j` further steps remain after the action. -/
noncomputable def adv (π : Policy S A) (j : ℕ) (s : S) (a : A) : ℝ :=
  Q M π j s a - V M π (j + 1) s

/-- The expected advantage of `π'` under `π`'s action distribution at `s`. -/
noncomputable def advGap (π π' : Policy S A) (j : ℕ) (s : S) : ℝ :=
  ∑ a, (π s) a * adv M π' j s a

/-- The visitation-weighted sum of advantage gaps — the right-hand side of the
performance difference lemma. Note the shape is exactly `pgSum`'s, with
`advGap` in place of `localTerm`. -/
noncomputable def pdSum (π π' : Policy S A) (m : ℕ) (s₀ : S) : ℝ :=
  ∑ k ∈ range m, M.γ ^ k * ∑ s, visit M π k s₀ s * advGap M π π' (m - 1 - k) s


/-- One-step lookahead: averaging over the policy-induced transition equals
averaging over actions, then next states. Pure `Finset.sum_comm`, but stated
separately so the main proof need not steer a rewrite through a
partially-normalized goal. -/
theorem step_expect (π ρ : Policy S A) (m : ℕ) (s : S) :
    ∑ s', step M π s s' * V M ρ m s'
      = ∑ a, (π s) a * ∑ s', (M.P s a) s' * V M ρ m s' := by
  unfold step
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

/-- The telescoping step: one step of `π` against one step of `π'`.

`V^π_(m+1) s - V^π'_(m+1) s = advGap m s + γ · ∑_{s'} step^π s s' · (V^π_m s' - V^π'_m s')`

The `Q^π'` terms cancel against the definition of `advGap`; what makes the
bookkeeping work is that `advGap` subtracts `V^π'_(m+1) s` once per action and
the policy sums to one. Verified numerically (`pdl_step.py`, 4.4e-16). -/
theorem perfDiff_succ (π π' : Policy S A) (m : ℕ) (s : S) :
    V M π (m + 1) s - V M π' (m + 1) s
      = advGap M π π' m s
        + M.γ * ∑ s', step M π s s' * (V M π m s' - V M π' m s') := by
  have hone : ∑ a, (π s) a = 1 := (π s).sum_eq_one
  have hgap : advGap M π π' m s
      = (∑ a, (π s) a * Q M π' m s a) - V M π' (m + 1) s := by
    unfold advGap adv
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hone, one_mul]
  have hsplit : (∑ s', step M π s s' * (V M π m s' - V M π' m s'))
      = (∑ s', step M π s s' * V M π m s') - ∑ s', step M π s s' * V M π' m s' := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hgap, hsplit, step_expect M π π m s, step_expect M π π' m s]
  rw [V_succ M π m s]
  unfold Q
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, sub_mul,
             Finset.sum_add_distrib, mul_add, add_mul]
  -- Both sides are the same sum up to order/association inside the binders.
  -- `ring` cannot see under `∑`, so normalize products with AC-lemmas first.
  simp only [mul_comm, mul_assoc, mul_left_comm]
  ring

/-- Weighting `pdSum` by one transition advances every visitation index by one.

Exactly `step_pgSum`'s statement with `advGap` in place of `localTerm`, and it
turns on the same `step_visit` (Chapman-Kolmogorov) lemma. -/
theorem step_pdSum (π π' : Policy S A) (m : ℕ) (s₀ : S) :
    ∑ s', step M π s₀ s' * pdSum M π π' m s'
      = ∑ k ∈ range m, M.γ ^ k *
          ∑ s, visit M π (k + 1) s₀ s * advGap M π π' (m - 1 - k) s := by
  unfold pdSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  calc ∑ s', step M π s₀ s' * (M.γ ^ k *
          (visit M π k s' s * advGap M π π' (m - 1 - k) s))
      = (∑ s', step M π s₀ s' * visit M π k s' s) *
          (M.γ ^ k * advGap M π π' (m - 1 - k) s) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
    _ = M.γ ^ k * (visit M π (k + 1) s₀ s * advGap M π π' (m - 1 - k) s) := by
        rw [step_visit M π k s₀ s]; ring

/-- **Performance difference lemma** (finite horizon).

`V_m^π(s₀) - V_m^π'(s₀) = ∑_{k<m} γ^k ∑_s visit^π k s₀ s · advGap_(m-1-k) s`

Kakade & Langford (2002); Agarwal-Kakade-Lee-Mahajan (JMLR 2021) Lemma 3.2.

The advantage is that of `π'`, but averaged under `π`'s state visitation --
that asymmetry is the whole content of the lemma. -/
theorem performance_difference (π π' : Policy S A) (m : ℕ) (s₀ : S) :
    V M π m s₀ - V M π' m s₀ = pdSum M π π' m s₀ := by
  induction m generalizing s₀ with
  | zero => simp [pdSum]
  | succ m ih =>
    rw [perfDiff_succ]
    have hIH : ∑ s', step M π s₀ s' * (V M π m s' - V M π' m s')
        = ∑ s', step M π s₀ s' * pdSum M π π' m s' := by
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [ih s']
    rw [hIH, step_pdSum]
    unfold pdSum
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hidx : m + 1 - 1 - (j + 1) = m - 1 - j := by omega
      rw [hidx, pow_succ]
      ring
    · simp

end PolicyGradient
