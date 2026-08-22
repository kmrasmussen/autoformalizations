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

/-! ### The policy gradient theorem, Fréchet form

The candidate derivative of `θ ↦ Vinf M (F.toPolicy θ) s₀` is

`L s₀ = ∑_s d^π(s₀,s) • dg s (Qinf π s ·) θ`,

with `dg` the softmax value-weighting derivative from `Proofs.G7a`. -/

/-- The candidate derivative of `Vinf` at a start state. -/
noncomputable def dVinf (M : FiniteMDP S A) (π : Policy S A) (θ : E S A) (s₀ : S) :
    E S A →L[ℝ] ℝ :=
  ∑ s : S, dinf M π s₀ s • dg (S:=S) (A:=A) s (fun a => Qinf M π s a) θ

/-- A policy has no advantage over itself: `∑_a π(a|s)·A^π(s,a) = 0`. -/
theorem advGapInf_self (M : FiniteMDP S A) (π : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    advGapInf M π π s = 0 := by
  unfold advGapInf
  have h : ∀ a, (π s) a * advInf M π s a
      = (π s) a * Qinf M π s a - (π s) a * Vinf M π s := by
    intro a; rw [advInf_eq]; ring
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_sub_distrib,
    ← Finset.sum_mul, (π s).sum_eq_one, one_mul,
    ← Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s]
  ring

/-- The `π'`-averaged advantage of `π` equals the `g`-difference at `s`:
`∑_a π'(a|s)·A^π(s,a) = g s A^π θ' - g s A^π θ` when `π = π_θ`, `π' = π_θ'`. -/
theorem advGapInf_eq_g_sub (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ θ' : E S A) (s : S) :
    advGapInf M (F.toPolicy θ) (F.toPolicy θ') s
      = g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ'
        - g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ := by
  have hzero := advGapInf_self M (F.toPolicy θ) hr hγ₀ hγ₁ s
  unfold g advGapInf at *
  rw [Finset.sum_congr rfl (fun a _ => by rw [hF θ' s a] :
    ∀ a ∈ (univ : Finset A), (F.toPolicy θ' s) a * advInf M (F.toPolicy θ) s a
      = softmax (fun a' => θ' (s, a')) a * advInf M (F.toPolicy θ) s a)] at *
  rw [Finset.sum_congr rfl (fun a _ => by rw [hF θ s a] :
    ∀ a ∈ (univ : Finset A), (F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a
      = softmax (fun a' => θ (s, a')) a * advInf M (F.toPolicy θ) s a)] at hzero
  rw [hzero]
  ring

/-! ### Continuity of the occupancy measure in the policy

`dinf` obeys `dinf π s₀ s = [s=s₀] + γ ∑_{s'} step π s₀ s' · dinf π s' s`. The
difference of two occupancies therefore contracts, leaving a bound in terms of
`‖step π' - step π‖`. -/

/-- A family dominated by `B + γ · c` for every upper bound `c` of `|D|` is
bounded by `B/(1-γ)`. Stated with the bound `c` abstract so callers need not
reconstruct the same `sup'` term. -/
theorem sup_le_of_contraction (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (D : S → ℝ) (B : ℝ) (hBnn : 0 ≤ B)
    (hD : ∀ (c : ℝ), (∀ y, |D y| ≤ c) → ∀ s₀, |D s₀| ≤ B + M.γ * c) (s : S) :
    |D s| ≤ B / (1 - M.γ) := by
  classical
  obtain ⟨s₁⟩ := ‹Nonempty S›
  have hne : (Finset.univ : Finset S).Nonempty := ⟨s₁, mem_univ s₁⟩
  set C : ℝ := Finset.univ.sup' hne (fun x => |D x|) with hC
  have hle : ∀ x, |D x| ≤ C := fun x =>
    Finset.le_sup' (f := fun x => |D x|) (mem_univ x)
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hle s₁)
  have hstep : C ≤ B + M.γ * C := by
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup' hne (fun x => |D x|)
    have hCx : C = |D x| := by rw [hC]; exact hx
    have := hD C hle x
    linarith [hCx.le, hCx.ge]
  have hpos : 0 < 1 - M.γ := by linarith
  have : C ≤ B / (1 - M.γ) := by rw [le_div_iff₀ hpos]; nlinarith
  exact le_trans (hle s) this

/-- **The occupancy measure is Lipschitz in the induced transition kernel.** -/
theorem dinf_diff_le (M : FiniteMDP S A) (π π' : Policy S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (K : ℝ) (hKnn : 0 ≤ K)
    (hK : ∀ s₀, ∑ s', |step M π' s₀ s' - step M π s₀ s'| ≤ K) (s₀ s : S) :
    |dinf M π' s₀ s - dinf M π s₀ s| ≤ (M.γ * K / (1 - M.γ)) / (1 - M.γ) := by
  classical
  have hpos : 0 < 1 - M.γ := by linarith
  set D : S → ℝ := fun x => dinf M π' x s - dinf M π x s with hDdef
  refine sup_le_of_contraction M hγ₀ hγ₁ D (M.γ * K / (1 - M.γ))
    (by positivity) ?_ s₀
  intro C hle x
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hle x)
  -- expand both occupancies one step
  have h1 := dinf_eq M π' hγ₀ hγ₁ x s
  have h2 := dinf_eq M π hγ₀ hγ₁ x s
  have hexp : D x
      = M.γ * ((∑ s', step M π' x s' * dinf M π' s' s)
        - ∑ s', step M π x s' * dinf M π s' s) := by
    rw [hDdef]; simp only []; rw [h1, h2]; ring
  -- split the difference: kernel change + occupancy change
  have hsplit : (∑ s', step M π' x s' * dinf M π' s' s)
        - ∑ s', step M π x s' * dinf M π s' s
      = (∑ s', (step M π' x s' - step M π x s') * dinf M π' s' s)
        + ∑ s', step M π x s' * D s' := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [hDdef]; simp only []; ring
  have hA : |∑ s', (step M π' x s' - step M π x s') * dinf M π' s' s| ≤ K / (1 - M.γ) := by
    calc |∑ s', (step M π' x s' - step M π x s') * dinf M π' s' s|
        ≤ ∑ s', |(step M π' x s' - step M π x s') * dinf M π' s' s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s', |step M π' x s' - step M π x s'| * dinf M π' s' s := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [abs_mul, abs_of_nonneg (dinf_nonneg M hγ₀ π' s' s)]
      _ ≤ ∑ s', |step M π' x s' - step M π x s'| * (1 / (1 - M.γ)) := by
          refine Finset.sum_le_sum fun s' _ => ?_
          exact mul_le_mul_of_nonneg_left (dinf_le_one_div M hγ₀ hγ₁ π' s' s)
            (abs_nonneg _)
      _ = (∑ s', |step M π' x s' - step M π x s'|) * (1 / (1 - M.γ)) := by
          rw [Finset.sum_mul]
      _ ≤ K * (1 / (1 - M.γ)) := by
          refine mul_le_mul_of_nonneg_right (hK x) (by positivity)
      _ = K / (1 - M.γ) := by ring
  have hB : |∑ s', step M π x s' * D s'| ≤ C := by
    calc |∑ s', step M π x s' * D s'| ≤ ∑ s', |step M π x s' * D s'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s', step M π x s' * |D s'| := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [abs_mul, abs_of_nonneg (step_nonneg M π x s')]
      _ ≤ ∑ s', step M π x s' * C :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (hle s') (step_nonneg M π x s')
      _ = C := by rw [← Finset.sum_mul, step_sum_eq_one M π x, one_mul]
  rw [hexp, hsplit, abs_mul, abs_of_nonneg hγ₀]
  have : |(∑ s', (step M π' x s' - step M π x s') * dinf M π' s' s)
      + ∑ s', step M π x s' * D s'| ≤ K / (1 - M.γ) + C :=
    le_trans (abs_add_le _ _) (add_le_add hA hB)
  calc M.γ * |(∑ s', (step M π' x s' - step M π x s') * dinf M π' s' s)
        + ∑ s', step M π x s' * D s'|
      ≤ M.γ * (K / (1 - M.γ) + C) := mul_le_mul_of_nonneg_left this hγ₀
    _ = M.γ * K / (1 - M.γ) + M.γ * C := by ring

/-! ### The softmax policy is Lipschitz in `θ`

Each probability is a `g` with an indicator `q`, so `g_lipschitz` with `B = 1`
gives `|π_θ'(a|s) - π_θ(a|s)| ≤ 2‖θ'-θ‖`; summing over actions gives the `ℓ¹`
bound, and pushing through `P` gives the kernel bound `dinf_diff_le` wants. -/

/-- A single softmax probability is `2`-Lipschitz in `θ`. -/
theorem softmax_prob_lipschitz (s : S) (a : A) (θ θ' : E S A) :
    |softmax (fun a' => θ' (s, a')) a - softmax (fun a' => θ (s, a')) a|
      ≤ 2 * ‖θ' - θ‖ := by
  have hq : ∀ b : A, |(if b = a then (1:ℝ) else 0)| ≤ 1 := by
    intro b; by_cases h : b = a <;> simp [h]
  have h := g_lipschitz (S:=S) (A:=A) s (fun b => if b = a then (1:ℝ) else 0) 1 hq θ' θ
  have hg : ∀ t : E S A, g (S:=S) (A:=A) s (fun b => if b = a then (1:ℝ) else 0) t
      = softmax (fun a' => t (s, a')) a := by
    intro t
    unfold g
    rw [Finset.sum_congr rfl (fun b _ => by by_cases hb : b = a <;> simp [hb] :
      ∀ b ∈ (univ : Finset A),
        (softmax (fun a' => t (s,a'))) b * (if b = a then (1:ℝ) else 0)
          = if b = a then (softmax (fun a' => t (s,a'))) a else 0)]
    rw [Finset.sum_ite_eq' univ a (fun _ => (softmax (fun a' => t (s,a'))) a)]
    simp
  rw [hg, hg] at h
  linarith

/-- The induced transition kernel is `2|A|`-Lipschitz in `ℓ¹`. -/
theorem step_diff_le (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ θ' : E S A) (s₀ : S) :
    ∑ s', |step M (F.toPolicy θ') s₀ s' - step M (F.toPolicy θ) s₀ s'|
      ≤ 2 * (Fintype.card A) * ‖θ' - θ‖ := by
  have hbound : ∀ s', |step M (F.toPolicy θ') s₀ s' - step M (F.toPolicy θ) s₀ s'|
      ≤ ∑ a, |(F.toPolicy θ' s₀) a - (F.toPolicy θ s₀) a| * (M.P s₀ a) s' := by
    intro s'
    unfold step
    rw [← Finset.sum_sub_distrib]
    calc |∑ a, ((F.toPolicy θ' s₀) a * (M.P s₀ a) s' - (F.toPolicy θ s₀) a * (M.P s₀ a) s')|
        ≤ ∑ a, |(F.toPolicy θ' s₀) a * (M.P s₀ a) s' - (F.toPolicy θ s₀) a * (M.P s₀ a) s'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, |(F.toPolicy θ' s₀) a - (F.toPolicy θ s₀) a| * (M.P s₀ a) s' := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← sub_mul, abs_mul, abs_of_nonneg ((M.P s₀ a).nonneg s')]
  calc ∑ s', |step M (F.toPolicy θ') s₀ s' - step M (F.toPolicy θ) s₀ s'|
      ≤ ∑ s', ∑ a, |(F.toPolicy θ' s₀) a - (F.toPolicy θ s₀) a| * (M.P s₀ a) s' :=
        Finset.sum_le_sum fun s' _ => hbound s'
    _ = ∑ a, ∑ s', |(F.toPolicy θ' s₀) a - (F.toPolicy θ s₀) a| * (M.P s₀ a) s' :=
        Finset.sum_comm
    _ = ∑ a, |(F.toPolicy θ' s₀) a - (F.toPolicy θ s₀) a| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, (M.P s₀ a).sum_eq_one, mul_one]
    _ ≤ ∑ _a : A, 2 * ‖θ' - θ‖ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [hF θ' s₀ a, hF θ s₀ a]
        exact softmax_prob_lipschitz s₀ a θ θ'
    _ = 2 * (Fintype.card A) * ‖θ' - θ‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-! ### `Vinf` is Fréchet differentiable, with the policy-gradient derivative

Assemble: the performance difference lemma linearizes `Vinf` exactly, `dg` is the
derivative of each local `g`, and `dinf_diff_le` controls the occupancy drift.
The occupancy-drift term is `O(‖h‖²)`, hence `o(‖h‖)`. -/

/-- The advantage is bounded by `2/(1-γ)`. -/
theorem abs_advInf_le (M : FiniteMDP S A) (π : Policy S A) (hr : ∀ s a, |M.r s a| ≤ 1)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) (a : A) :
    |advInf M π s a| ≤ 2 / (1 - M.γ) := by
  have hpos : 0 < 1 - M.γ := by linarith
  rw [advInf_eq]
  calc |Qinf M π s a - Vinf M π s| ≤ |Qinf M π s a| + |Vinf M π s| := abs_sub _ _
    _ ≤ 1 / (1 - M.γ) + 1 / (1 - M.γ) :=
        add_le_add (abs_Qinf_le M π hr hγ₀ hγ₁ s a)
          (abs_Vinf_le M π 1 zero_le_one hr hγ₀ hγ₁ s)
    _ = 2 / (1 - M.γ) := by ring

/-- `dg` is invariant under adding a constant to `q`: it subtracts the mean, so a
uniform shift cancels. This is why the `Qinf` and `advInf` forms of the
derivative agree. -/
theorem dg_sub_const (s : S) (q : A → ℝ) (c : ℝ) (t : E S A) :
    dg (S:=S) (A:=A) s (fun a => q a - c) t = dg (S:=S) (A:=A) s q t := by
  unfold dg
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  set P : Dist A := softmax (fun a' => t (s,a')) with hP
  have hsum : ∑ a, P a * (q a - c) = (∑ a, P a * q a) - c := by
    rw [Finset.sum_congr rfl (fun a _ => by ring :
      ∀ a ∈ (univ : Finset A), P a * (q a - c) = P a * q a - P a * c),
      Finset.sum_sub_distrib, ← Finset.sum_mul, P.sum_eq_one, one_mul]
  rw [hsum]
  ring

/-- `dg` at the advantage equals `dg` at the action-value. -/
theorem dg_advInf_eq (M : FiniteMDP S A) (π : Policy S A) (s : S) (t : E S A) :
    dg (S:=S) (A:=A) s (fun a => advInf M π s a) t
      = dg (S:=S) (A:=A) s (fun a => Qinf M π s a) t := by
  have : (fun a => advInf M π s a) = fun a => Qinf M π s a - Vinf M π s := by
    funext a; exact advInf_eq M π s a
  rw [this]
  exact dg_sub_const s (fun a => Qinf M π s a) (Vinf M π s) t

/-- The exact error decomposition supplied by the performance difference lemma. -/
theorem Vinf_error_eq (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ θ' : E S A) (s₀ : S) :
    Vinf M (F.toPolicy θ') s₀ - Vinf M (F.toPolicy θ) s₀
        - dVinf M (F.toPolicy θ) θ s₀ (θ' - θ)
      = (∑ s, (dinf M (F.toPolicy θ') s₀ s - dinf M (F.toPolicy θ) s₀ s)
            * (g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ'
              - g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ))
        + ∑ s, dinf M (F.toPolicy θ) s₀ s
            * ((g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ'
                - g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ)
              - dg (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ (θ' - θ)) := by
  have hpd := perfDiffInf M (F.toPolicy θ) (F.toPolicy θ') hr hγ₀ hγ₁ s₀
  have hbridge : ∀ s, advGapInf M (F.toPolicy θ) (F.toPolicy θ') s
      = g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ'
        - g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ :=
    fun s => advGapInf_eq_g_sub M F hF hr hγ₀ hγ₁ θ θ' s
  have hL : dVinf M (F.toPolicy θ) θ s₀ (θ' - θ)
      = ∑ s, dinf M (F.toPolicy θ) s₀ s
          * dg (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ (θ' - θ) := by
    unfold dVinf
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, dg_advInf_eq]
  rw [hpd]
  unfold pdInf
  rw [Finset.sum_congr rfl (fun s _ => by rw [hbridge s] :
    ∀ s ∈ (univ : Finset S), dinf M (F.toPolicy θ') s₀ s * advGapInf M (F.toPolicy θ) (F.toPolicy θ') s
      = dinf M (F.toPolicy θ') s₀ s
        * (g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ'
          - g (S:=S) (A:=A) s (fun a => advInf M (F.toPolicy θ) s a) θ))]
  rw [hL, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => by ring

/-- **`Vinf` is Fréchet differentiable in `θ`, with the policy-gradient
derivative `dVinf`.** -/
theorem hasFDerivAt_Vinf (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : E S A) (s₀ : S) :
    HasFDerivAt (fun t => Vinf M (F.toPolicy t) s₀) (dVinf M (F.toPolicy θ) θ s₀) θ := by
  have hpos : 0 < 1 - M.γ := by linarith
  classical
  set q : S → A → ℝ := fun s a => advInf M (F.toPolicy θ) s a with hq
  -- Term 2 is little-o: a finite sum of little-o's.
  have hT2 : (fun t : E S A => ∑ s, dinf M (F.toPolicy θ) s₀ s
      * ((g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ)
        - dg (S:=S) (A:=A) s (q s) θ (t - θ)))
      =o[nhds θ] (fun t => t - θ) := by
    have hone : ∀ s : S, (fun t : E S A =>
        (g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ)
          - dg (S:=S) (A:=A) s (q s) θ (t - θ)) =o[nhds θ] (fun t => t - θ) := by
      intro s
      have := (hasFDeriv_g (S:=S) (A:=A) s (q s) θ).isLittleO
      simpa using this
    have hsum := Asymptotics.IsLittleO.sum (s := (univ : Finset S))
      (fun s (_ : s ∈ (univ : Finset S)) =>
        (hone s).const_mul_left (dinf M (F.toPolicy θ) s₀ s))
    refine hsum.congr_left (fun t => ?_)
    simp [Finset.sum_apply]
  -- Term 1 is O(‖t-θ‖²), hence little-o.
  have hT1 : (fun t : E S A => ∑ s, (dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s)
      * (g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ))
      =o[nhds θ] (fun t => t - θ) := by
    -- constants
    set K : ℝ := 2 * (Fintype.card A) with hK
    set c1 : ℝ := M.γ * K / (1 - M.γ) / (1 - M.γ) with hc1
    set c2 : ℝ := 2 * (2 / (1 - M.γ)) with hc2
    have hKnn : 0 ≤ K := by positivity
    have hbound : ∀ t : E S A,
        ‖∑ s, (dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s)
          * (g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ)‖
        ≤ ((Fintype.card S) * (c1 * c2)) * ‖t - θ‖ * ‖t - θ‖ := by
      intro t
      have hstep : ∀ x, ∑ s', |step M (F.toPolicy t) x s' - step M (F.toPolicy θ) x s'|
          ≤ K * ‖t - θ‖ := by
        intro x
        have := step_diff_le M F hF θ t x
        rw [hK]; linarith [this]
      have hd : ∀ s, |dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s|
          ≤ c1 * ‖t - θ‖ := by
        intro s
        have h := dinf_diff_le M (F.toPolicy θ) (F.toPolicy t) hγ₀ hγ₁
          (K * ‖t - θ‖) (by positivity) hstep s₀ s
        rw [hc1]
        calc |dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s|
            ≤ M.γ * (K * ‖t - θ‖) / (1 - M.γ) / (1 - M.γ) := h
          _ = M.γ * K / (1 - M.γ) / (1 - M.γ) * ‖t - θ‖ := by ring
      have hgd : ∀ s, |g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ|
          ≤ c2 * ‖t - θ‖ := by
        intro s
        have hqb : ∀ a, |q s a| ≤ 2 / (1 - M.γ) :=
          fun a => abs_advInf_le M (F.toPolicy θ) hr hγ₀ hγ₁ s a
        have := g_lipschitz (S:=S) (A:=A) s (q s) (2 / (1 - M.γ)) hqb t θ
        rw [hc2]; exact this
      rw [Real.norm_eq_abs]
      calc |∑ s, (dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s)
              * (g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ)|
          ≤ ∑ s, |(dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s)
              * (g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _s : S, (c1 * ‖t - θ‖) * (c2 * ‖t - θ‖) := by
            refine Finset.sum_le_sum fun s _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hd s) (hgd s) (abs_nonneg _) (by positivity)
        _ = ((Fintype.card S) * (c1 * c2)) * ‖t - θ‖ * ‖t - θ‖ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    -- O(‖h‖²) is o(‖h‖)
    have hbig : (fun t : E S A => ∑ s, (dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s)
        * (g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ))
        =O[nhds θ] (fun t => ‖t - θ‖ * ‖t - θ‖) := by
      refine Asymptotics.isBigO_of_le' (c := (Fintype.card S) * (c1 * c2)) _ (fun t => ?_)
      have hn : ‖‖t - θ‖ * ‖t - θ‖‖ = ‖t - θ‖ * ‖t - θ‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hn]
      have := hbound t
      calc ‖∑ s, (dinf M (F.toPolicy t) s₀ s - dinf M (F.toPolicy θ) s₀ s)
              * (g (S:=S) (A:=A) s (q s) t - g (S:=S) (A:=A) s (q s) θ)‖
          ≤ ((Fintype.card S) * (c1 * c2)) * ‖t - θ‖ * ‖t - θ‖ := this
        _ = ((Fintype.card S) * (c1 * c2)) * (‖t - θ‖ * ‖t - θ‖) := by ring
    refine hbig.trans_isLittleO ?_
    -- ‖t-θ‖² = o(t-θ): directly from the ε-definition, taking ‖t-θ‖ < ε.
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have hball : ∀ᶠ t : E S A in nhds θ, ‖t - θ‖ < ε := by
      have hc : Continuous (fun t : E S A => t - θ) :=
        continuous_id.sub continuous_const
      have htend : Filter.Tendsto (fun t : E S A => ‖t - θ‖) (nhds θ) (nhds 0) := by
        have := (hc.tendsto θ).norm
        simpa using this
      exact htend.eventually (eventually_lt_nhds hε) |>.mono (fun t ht => by
        simpa using ht)
    refine hball.mono (fun t ht => ?_)
    have hnn : (0:ℝ) ≤ ‖t - θ‖ := norm_nonneg _
    have hn : ‖‖t - θ‖ * ‖t - θ‖‖ = ‖t - θ‖ * ‖t - θ‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hn]
    calc ‖t - θ‖ * ‖t - θ‖ ≤ ε * ‖t - θ‖ :=
          mul_le_mul_of_nonneg_right ht.le hnn
      _ = ε * ‖t - θ‖ := rfl

  -- assemble
  rw [hasFDerivAt_iff_isLittleO]
  refine (hT1.add hT2).congr_left (fun t => ?_)
  exact (Vinf_error_eq M F hF hr hγ₀ hγ₁ θ t s₀).symm

end G1

end Proofs
end PolicyGradient
