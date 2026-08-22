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


/-! ## The argmax-selector chain

The route that closes.  Take `astar` to be the **`A^π`-argmax within `supp πstar`**
(hypothesis `hmax` below); then, with `m(s) := π(b s|s)·A^π(s, b s)` the frozen
right-hand side's per-state factor,

* **(S1)** `X(s) := ∑_a πstar(a|s)·A^π(s,a) ≤ A^π(s, astar s)` — a mixture is at
  most the maximum over its own support;
* **(S2)** `c·A^π(s, astar s) ≤ m(s)`, from `c ≤ π(astar s|s)` and `hb` when
  `A^π(s, astar s) ≥ 0`, and from `m(s) ≥ 0` when it is negative;
* **(S3)** hence `c·X(s) ≤ m(s)` **per state**;
* then globally, with **no** cross-state argument,
  `c·(V*_μ - V^π_μ) = c·∑_s d^{πstar}_μ(s)·X(s) ≤ ∑_s d^{πstar}_μ(s)·m(s)
     ≤ mism·∑_s μ(s)·m(s) ≤ mism·∑_s d^π_μ(s)·m(s)`.

**Order matters**: collapse `X → m` *first*, and only then introduce `mism`.
Applying `d^{πstar} ≤ mism·μ` while still carrying `X` is what every earlier
refutation did. -/

/-- **(S1)** A `πstar`-mixture of advantages is at most the advantage at the
`A^π`-argmax over `supp πstar`. -/
theorem advGapInf_le_advInf_argmax (M : FiniteMDP S A)
    (π πstar : Policy S A) (astar : S → A)
    (hmax : ∀ s a, 0 < (πstar s) a → advInf M π s a ≤ advInf M π s (astar s))
    (s : S) : advGapInf M π πstar s ≤ advInf M π s (astar s) := by
  classical
  unfold advGapInf
  have hle : ∀ a ∈ (univ : Finset A), (πstar s) a * advInf M π s a
      ≤ (πstar s) a * advInf M π s (astar s) := by
    intro a _
    rcases lt_or_eq_of_le ((πstar s).nonneg a) with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hmax s a hpos) hpos.le
    · rw [← hzero]; simp
  calc ∑ a, (πstar s) a * advInf M π s a
      ≤ ∑ _a : A, (πstar s) _a * advInf M π s (astar s) := Finset.sum_le_sum hle
    _ = advInf M π s (astar s) := by
        rw [← Finset.sum_mul, (πstar s).sum_eq_one, one_mul]

/-- **(S2)–(S3)** `c·X(s) ≤ m(s)` at every state, where `c = ⨅_x π(astar x|x)`.

This is the per-state collapse that the aggregate bound needs.  It uses the
selector fact `hb` only at `a = astar s`. -/
theorem iInf_mul_advGapInf_le_sel (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (astar : S → A)
    (hmax : ∀ s a, 0 < (πstar s) a → advInf M π s a ≤ advInf M π s (astar s))
    (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s))
    (s : S) :
    (⨅ x : S, (π x) (astar x)) * advGapInf M π πstar s
      ≤ (π s) (b s) * advInf M π s (b s) := by
  classical
  set c : ℝ := ⨅ x : S, (π x) (astar x) with hc
  have hbdd : BddBelow (Set.range fun x : S => (π x) (astar x)) :=
    ⟨0, by rintro y ⟨x, rfl⟩; exact (π x).nonneg _⟩
  have hcle : c ≤ (π s) (astar s) := ciInf_le hbdd s
  have hc0 : 0 ≤ c := le_ciInf fun x => (π x).nonneg _
  have hm0 : 0 ≤ (π s) (b s) * advInf M π s (b s) := sel_nonneg M hr hγ₀ hγ₁ π b hb s
  have hS1 : advGapInf M π πstar s ≤ advInf M π s (astar s) :=
    advGapInf_le_advInf_argmax M π πstar astar hmax s
  rcases le_or_gt (advInf M π s (astar s)) 0 with hA | hA
  · -- the advantage at `astar s` is nonpositive, so is `c · X(s)`
    have : c * advGapInf M π πstar s ≤ c * advInf M π s (astar s) :=
      mul_le_mul_of_nonneg_left hS1 hc0
    have h2 : c * advInf M π s (astar s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hA
    linarith
  · calc c * advGapInf M π πstar s
        ≤ c * advInf M π s (astar s) := mul_le_mul_of_nonneg_left hS1 hc0
      _ ≤ (π s) (astar s) * advInf M π s (astar s) :=
          mul_le_mul_of_nonneg_right hcle hA.le
      _ ≤ (π s) (b s) * advInf M π s (b s) := hb s (astar s)

/-- **`g1_aggregate_bound` at the `A^π`-argmax selector `astar`.**

The frozen conclusion, verbatim, under the extra hypothesis `hmax` pinning
`astar s` to an `A^π`-maximiser inside `supp πstar(·|s)`. -/
theorem g1_aggregate_bound_at_argmax (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (π πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A)
    (hmax : ∀ s a, 0 < (πstar s) a → advInf M π s a ≤ advInf M π s (astar s))
    (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s)) :
    (⨅ s : S, (π s) (astar s)) * (VstarDist M μ - VinfDist M π μ)
      ≤ mismatchCoeff M πstar μ
          * ∑ s, |dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))| := by
  classical
  set c : ℝ := ⨅ x : S, (π x) (astar x) with hc
  set mism : ℝ := mismatchCoeff M πstar μ with hmism
  set m : S → ℝ := fun s => (π s) (b s) * advInf M π s (b s) with hm
  have hc0 : 0 ≤ c := le_ciInf fun x => (π x).nonneg _
  have hm0 : ∀ s, 0 ≤ m s := fun s => sel_nonneg M hr hγ₀ hγ₁ π b hb s
  have hmism0 : 0 < mism := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hdstar0 : ∀ s, 0 ≤ dinfDist M πstar μ s := fun s => by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ πstar s₀ s)
  rw [sel_rhs_eq M hr hγ₀ hγ₁ π μ b hb,
    VstarDist_sub_VinfDist_eq M π πstar hr hγ₀ hγ₁ hstar μ]
  -- Step 1: collapse `X → m` under the `d^{πstar}` sum.
  have step1 : c * ∑ s, dinfDist M πstar μ s * advGapInf M π πstar s
      ≤ ∑ s, dinfDist M πstar μ s * m s := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h := iInf_mul_advGapInf_le_sel M hr hγ₀ hγ₁ π πstar astar hmax b hb s
    calc c * (dinfDist M πstar μ s * advGapInf M π πstar s)
        = dinfDist M πstar μ s * (c * advGapInf M π πstar s) := by ring
      _ ≤ dinfDist M πstar μ s * m s := mul_le_mul_of_nonneg_left h (hdstar0 s)
  -- Step 2: only now introduce `mism`, on a sum whose factors are nonnegative.
  have step2 : ∑ s, dinfDist M πstar μ s * m s
      ≤ mism * ∑ s, dinfDist M π μ s * m s := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h1 : dinfDist M πstar μ s ≤ mism * μ s :=
      mismatch_bound_proof_of_support M hγ₀ hγ₁ πstar μ hμ s
    have h2 : μ s ≤ dinfDist M π μ s := mu_le_dinfDist M hγ₀ hγ₁ π μ s
    have h3 : dinfDist M πstar μ s ≤ mism * dinfDist M π μ s :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hmism0.le)
    calc dinfDist M πstar μ s * m s
        ≤ (mism * dinfDist M π μ s) * m s := mul_le_mul_of_nonneg_right h3 (hm0 s)
      _ = mism * (dinfDist M π μ s * m s) := by ring
  exact le_trans step1 step2

end Cpl

end Proofs
end PolicyGradient
