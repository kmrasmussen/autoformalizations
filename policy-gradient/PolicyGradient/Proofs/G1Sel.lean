/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1c

/-!
# G1Sel — the aggregate Łojasiewicz bound at the maximizing selector

Work file for the frozen goal `g1_aggregate_bound` (`@[infra "G1-aggregate"]`)
in its restated form, which carries a selector `b : S → A` with

```
hb : ∀ s a, π(a|s)·A^π(s,a) ≤ π(b s|s)·A^π(s,b s)
```

i.e. `b s = argmax_a π(a|s)·A^π(s,a)`.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Sel

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

open scoped BigOperators

/-- `∑_a π(a|s)·A^π(s,a) = 0`: the advantage has zero mean under `π`. -/
theorem sum_pi_advInf_eq_zero (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) :
    ∑ a, (π s) a * advInf M π s a = 0 := by
  have hV : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  have h : ∀ a, (π s) a * advInf M π s a
      = (π s) a * Qinf M π s a - (π s) a * Vinf M π s := by
    intro a; rw [advInf_eq]; ring
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_sub_distrib,
    ← Finset.sum_mul, (π s).sum_eq_one, one_mul, ← hV]
  ring

/-- The maximizing selector value `m(s) = π(b s|s)·A^π(s,b s)` is nonnegative,
because the `π`-weighted advantages sum to zero and `m(s)` dominates each of
them. -/
theorem sel_nonneg (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s))
    (s : S) : 0 ≤ (π s) (b s) * advInf M π s (b s) := by
  by_contra hneg
  rw [not_le] at hneg
  have hsum : ∑ a, (π s) a * advInf M π s a < 0 := by
    have hlt : ∀ a ∈ (univ : Finset A), (π s) a * advInf M π s a
        ≤ (π s) (b s) * advInf M π s (b s) := fun a _ => hb s a
    calc ∑ a, (π s) a * advInf M π s a
        ≤ ∑ _a : A, (π s) (b s) * advInf M π s (b s) := Finset.sum_le_sum hlt
      _ = (Fintype.card A : ℝ) * ((π s) (b s) * advInf M π s (b s)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < 0 := by
          have hc : (0:ℝ) < (Fintype.card A : ℝ) := by
            have := Fintype.card_pos_iff.mpr ‹Nonempty A›
            exact_mod_cast this
          exact mul_neg_of_pos_of_neg hc hneg
  rw [sum_pi_advInf_eq_zero M hr hγ₀ hγ₁ π s] at hsum
  exact lt_irrefl 0 hsum

/-- The RHS of the frozen goal, with the absolute value removed:
`m(s) ≥ 0` and `d^π_μ(s) ≥ 0`, so each summand is already nonnegative. -/
theorem sel_rhs_eq (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (μ : Dist S) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s)) :
    ∑ s, |dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))|
      = ∑ s, dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s)) := by
  refine Finset.sum_congr rfl fun s _ => ?_
  have hd : 0 ≤ dinfDist M π μ s := by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ => mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ π s₀ s)
  exact abs_of_nonneg (mul_nonneg hd (sel_nonneg M hr hγ₀ hγ₁ π b hb s))

/-- **Change of measure at the selector `b`.**

`d^{πstar}_μ(s) ≤ mism·μ(s) ≤ mism·d^π_μ(s)` and `m(s) ≥ 0`, so the
`πstar`-occupancy-weighted selector sum is dominated by `mism` times the
`π`-occupancy-weighted one. -/
theorem sum_dinfDistStar_sel_le (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (μ : Dist S) (hμ : ∀ s, 0 < μ s) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s)) :
    ∑ s, dinfDist M πstar μ s * ((π s) (b s) * advInf M π s (b s))
      ≤ mismatchCoeff M πstar μ
          * ∑ s, dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have hm : 0 ≤ (π s) (b s) * advInf M π s (b s) := sel_nonneg M hr hγ₀ hγ₁ π b hb s
  have h1 : dinfDist M πstar μ s ≤ mismatchCoeff M πstar μ * μ s :=
    mismatch_bound_proof_of_support M hγ₀ hγ₁ πstar μ hμ s
  have h2 : μ s ≤ dinfDist M π μ s := mu_le_dinfDist M hγ₀ hγ₁ π μ s
  have hm0 : 0 < mismatchCoeff M πstar μ := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have h3 : dinfDist M πstar μ s ≤ mismatchCoeff M πstar μ * dinfDist M π μ s :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 hm0.le)
  calc dinfDist M πstar μ s * ((π s) (b s) * advInf M π s (b s))
      ≤ (mismatchCoeff M πstar μ * dinfDist M π μ s)
          * ((π s) (b s) * advInf M π s (b s)) := mul_le_mul_of_nonneg_right h3 hm
    _ = mismatchCoeff M πstar μ * (dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))) := by
        ring

end Sel

end Proofs
end PolicyGradient
