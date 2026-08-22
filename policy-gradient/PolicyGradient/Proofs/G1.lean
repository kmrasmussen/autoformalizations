/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target
import PolicyGradient.Proofs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# G1 — Mei et al. Lemma 8, the non-uniform Łojasiewicz inequality

Work file for the frozen goal `Goal.g1_lojasiewicz`.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section G1

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ### Infinite-horizon performance difference

`Vinf π' s₀ - Vinf π s₀ = ∑_s dinf π' s₀ s · ∑_a π'(a|s) · advInf π s a`.
-/

/-- The `π'`-averaged advantage of `π` at a state. -/
noncomputable def advGapInf (M : FiniteMDP S A) (π π' : Policy S A) (s : S) : ℝ :=
  ∑ a, (π' s) a * advInf M π s a

/-- `advInf` is `Qinf - Vinf`. -/
theorem advInf_eq (M : FiniteMDP S A) (π : Policy S A) (s : S) (a : A) :
    advInf M π s a = Qinf M π s a - Vinf M π s := rfl

/-- One-step performance difference: the value gap at `s` is the local advantage
gap plus a discounted push through `π'`'s transition. -/
theorem perfDiffInf_step (M : FiniteMDP S A) (π π' : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vinf M π' s - Vinf M π s
      = advGapInf M π π' s
        + M.γ * ∑ s', step M π' s s' * (Vinf M π' s' - Vinf M π s') := by
  have hπ' : Vinf M π' s = ∑ a, (π' s) a * Qinf M π' s a :=
    Vinf_eq_rbar_add M π' 1 zero_le_one hr hγ₀ hγ₁ s
  have hadv : advGapInf M π π' s = (∑ a, (π' s) a * Qinf M π s a) - Vinf M π s := by
    unfold advGapInf
    have : ∀ a, (π' s) a * advInf M π s a
        = (π' s) a * Qinf M π s a - (π' s) a * Vinf M π s := by
      intro a; rw [advInf_eq]; ring
    rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_sub_distrib,
      ← Finset.sum_mul, (π' s).sum_eq_one, one_mul]
  rw [hadv, hπ']
  -- the γ-term: expand Qinf on both sides
  have hstep : M.γ * ∑ s', step M π' s s' * (Vinf M π' s' - Vinf M π s')
      = (∑ a, (π' s) a * Qinf M π' s a) - ∑ a, (π' s) a * Qinf M π s a := by
    have hQ : ∀ a, Qinf M π' s a - Qinf M π s a
        = M.γ * ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s') := by
      intro a
      unfold Qinf
      have : ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s')
          = (∑ s', (M.P s a) s' * Vinf M π' s') - ∑ s', (M.P s a) s' * Vinf M π s' := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s' _ => by ring
      rw [this]; ring
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun a _ => by rw [← mul_sub, hQ a] :
      ∀ a ∈ (univ : Finset A), (π' s) a * Qinf M π' s a - (π' s) a * Qinf M π s a
        = (π' s) a * (M.γ * ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s')))]
    unfold step
    calc M.γ * ∑ s', (∑ a, (π' s) a * (M.P s a) s') * (Vinf M π' s' - Vinf M π s')
        = ∑ s', ∑ a, M.γ * ((π' s) a * (M.P s a) s' * (Vinf M π' s' - Vinf M π s')) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ a, ∑ s', M.γ * ((π' s) a * (M.P s a) s' * (Vinf M π' s' - Vinf M π s')) :=
          Finset.sum_comm
      _ = ∑ a, (π' s) a * (M.γ * ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s')) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s' _ => by ring
  rw [hstep]; ring

/-! ### The closed form

Define the defect `D s₀ = (Vinf π' s₀ - Vinf π s₀) - ∑_s dinf π' s₀ s · advGapInf s`.
Both sides satisfy the same one-step recursion (`perfDiffInf_step` for the value
gap, `dinf_eq` for the occupancy), so `D` satisfies `D s₀ = γ ∑ step · D s'`,
and `sup |D| ≤ γ · sup |D|` with `γ < 1` forces `D ≡ 0`. -/

/-- The occupancy-weighted advantage sum. -/
noncomputable def pdInf (M : FiniteMDP S A) (π π' : Policy S A) (s₀ : S) : ℝ :=
  ∑ s, dinf M π' s₀ s * advGapInf M π π' s

/-- `pdInf` satisfies the same one-step recursion as the value gap. -/
theorem pdInf_step (M : FiniteMDP S A) (π π' : Policy S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    pdInf M π π' s₀
      = advGapInf M π π' s₀ + M.γ * ∑ s', step M π' s₀ s' * pdInf M π π' s' := by
  unfold pdInf
  have hd : ∀ s, dinf M π' s₀ s
      = (if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π' s₀ s' * dinf M π' s' s :=
    fun s => dinf_eq M π' hγ₀ hγ₁ s₀ s
  rw [Finset.sum_congr rfl (fun s _ => by rw [hd s] :
    ∀ s ∈ (univ : Finset S), dinf M π' s₀ s * advGapInf M π π' s
      = ((if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π' s₀ s' * dinf M π' s' s)
          * advGapInf M π π' s)]
  rw [Finset.sum_congr rfl (fun s _ => by by_cases h : s = s₀ <;> simp [h] <;> ring :
    ∀ s ∈ (univ : Finset S),
      ((if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π' s₀ s' * dinf M π' s' s)
          * advGapInf M π π' s
      = (if s = s₀ then advGapInf M π π' s else 0)
        + M.γ * ((∑ s', step M π' s₀ s' * dinf M π' s' s) * advGapInf M π π' s))]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ s₀ (fun s => advGapInf M π π' s)]
  simp only [mem_univ, if_true]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ s, (∑ s', step M π' s₀ s' * dinf M π' s' s) * advGapInf M π π' s
      = ∑ s, ∑ s', step M π' s₀ s' * (dinf M π' s' s * advGapInf M π π' s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s' _ => by ring
    _ = ∑ s', ∑ s, step M π' s₀ s' * (dinf M π' s' s * advGapInf M π π' s) :=
        Finset.sum_comm
    _ = ∑ s', step M π' s₀ s' * ∑ s, dinf M π' s' s * advGapInf M π π' s := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [Finset.mul_sum]

/-- A bounded family satisfying `D s₀ = γ ∑ step · D s'` is identically zero. -/
theorem eq_zero_of_contraction (M : FiniteMDP S A) (π' : Policy S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (D : S → ℝ)
    (hD : ∀ s₀, D s₀ = M.γ * ∑ s', step M π' s₀ s' * D s') (s : S) : D s = 0 := by
  classical
  obtain ⟨s₁⟩ := ‹Nonempty S›
  set C : ℝ := Finset.univ.sup' ⟨s₁, mem_univ s₁⟩ (fun x => |D x|) with hC
  have hle : ∀ x, |D x| ≤ C := fun x =>
    Finset.le_sup' (f := fun x => |D x|) (mem_univ x)
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hle s₁)
  have hstep : C ≤ M.γ * C := by
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' (⟨s₁, mem_univ s₁⟩ :
      (Finset.univ : Finset S).Nonempty) (fun x => |D x|)
    have hCx : C = |D x| := by rw [hC]; exact hx
    have hinner : |∑ s', step M π' x s' * D s'| ≤ C := by
      calc |∑ s', step M π' x s' * D s'| ≤ ∑ s', |step M π' x s' * D s'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s', step M π' x s' * |D s'| := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [abs_mul, abs_of_nonneg (step_nonneg M π' x s')]
        _ ≤ ∑ s', step M π' x s' * C :=
            Finset.sum_le_sum fun s' _ =>
              mul_le_mul_of_nonneg_left (hle s') (step_nonneg M π' x s')
        _ = C := by rw [← Finset.sum_mul, step_sum_eq_one M π' x, one_mul]
    have hDx : |D x| ≤ M.γ * C := by
      rw [hD x, abs_mul, abs_of_nonneg hγ₀]
      exact mul_le_mul_of_nonneg_left hinner hγ₀
    linarith [hCx.le, hDx, hCx.ge]
  have hCzero : C = 0 := by nlinarith
  have := hle s
  rw [hCzero] at this
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

/-- **Infinite-horizon performance difference lemma.**

`V^{π'}(s₀) - V^π(s₀) = ∑_s d^{π'}(s₀,s) · ∑_a π'(a|s) · A^π(s,a)`. -/
theorem perfDiffInf (M : FiniteMDP S A) (π π' : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Vinf M π' s₀ - Vinf M π s₀ = pdInf M π π' s₀ := by
  set D : S → ℝ := fun s => (Vinf M π' s - Vinf M π s) - pdInf M π π' s with hDdef
  have hD : ∀ s, D s = M.γ * ∑ s', step M π' s s' * D s' := by
    intro s
    have h1 := perfDiffInf_step M π π' hr hγ₀ hγ₁ s
    have h2 := pdInf_step M π π' hγ₀ hγ₁ s
    have hsplit : ∑ s', step M π' s s' * D s'
        = (∑ s', step M π' s s' * (Vinf M π' s' - Vinf M π s'))
          - ∑ s', step M π' s s' * pdInf M π π' s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s' _ => by simp [hDdef]; ring
    rw [hDdef]
    simp only []
    rw [hsplit, h1, h2]
    ring
  have := eq_zero_of_contraction M π' hγ₀ hγ₁ D hD s₀
  rw [hDdef] at this
  simp only [] at this
  linarith

end G1

end Proofs
end PolicyGradient
