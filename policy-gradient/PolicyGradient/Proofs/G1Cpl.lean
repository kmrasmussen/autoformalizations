/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1Sel

/-!
# G1Cpl — closing `g1_aggregate_bound` by a coupled use of `mismatchCoeff`

Work file. The frozen goal (selector form) is

```
c · (V*_μ - V^π_μ)  ≤  mism · ∑_s |d^π_μ(s) · m(s)|,
    c = ⨅_s π(a*(s)|s),   m(s) = π(b s|s)·A^π(s, b s).
```

`G1Sel` removes the absolute value (`sel_rhs_eq`, since `m ≥ 0`).  This file
routes the left-hand side through the **dual** performance-difference identity
`VstarDist_sub_VinfDist_dual`, which already expands the value gap along
`d^π_μ` — the *same* occupancy the right-hand side carries — so that no change
of measure is needed on that half at all.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Cpl

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

open scoped BigOperators

/-- `1 ≤ mismatchCoeff`: `μ(s) ≤ d^π_μ(s)` at any `s`. -/
theorem one_le_mismatchCoeff (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S)
    (hμ : ∀ s, 0 < μ s) : 1 ≤ mismatchCoeff M π μ := by
  classical
  obtain ⟨s⟩ := ‹Nonempty S›
  have h := le_ciSup (bddAbove_mismatch M π μ) s
  have hmu : μ s ≤ dinfDist M π μ s := mu_le_dinfDist M hγ₀ hγ₁ π μ s
  have h1 : (1:ℝ) ≤ dinfDist M π μ s / μ s :=
    (one_le_div (hμ s)).mpr hmu
  exact le_trans h1 h

/-- **The reduction.**  With the dual identity on the left and `sel_rhs_eq` on
the right, the frozen goal follows from the single pointwise inequality

```
c · dualGap(s)  ≤  mism · m(s).
```
-/
theorem g1_aggregate_of_pointwise_dual (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (μ : Dist S) (hμ : ∀ s, 0 < μ s) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s))
    (hpt : ∀ s, (⨅ x : S, (π x) (astar x)) * dualGap M π πstar s
      ≤ mismatchCoeff M πstar μ * ((π s) (b s) * advInf M π s (b s))) :
    (⨅ s : S, (π s) (astar s)) * (VstarDist M μ - VinfDist M π μ)
      ≤ mismatchCoeff M πstar μ
          * ∑ s, |dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))| := by
  classical
  rw [sel_rhs_eq M hr hγ₀ hγ₁ π μ b hb,
    VstarDist_sub_VinfDist_dual M π πstar hr hγ₀ hγ₁ hstar μ,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have hd : 0 ≤ dinfDist M π μ s := by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ π s₀ s)
  have := mul_le_mul_of_nonneg_left (hpt s) hd
  calc (⨅ x : S, (π x) (astar x)) * (dinfDist M π μ s * dualGap M π πstar s)
      = dinfDist M π μ s * ((⨅ x : S, (π x) (astar x)) * dualGap M π πstar s) := by ring
    _ ≤ dinfDist M π μ s
          * (mismatchCoeff M πstar μ * ((π s) (b s) * advInf M π s (b s))) := this
    _ = mismatchCoeff M πstar μ
          * (dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))) := by ring

end Cpl

end Proofs
end PolicyGradient
