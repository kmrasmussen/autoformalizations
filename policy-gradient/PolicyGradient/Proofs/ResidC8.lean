/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Resid

/-!
# ResidC8 — AKM Lemma C.8 (`lem:diverge`), the `min → -∞` half

Companion to `PolicyGradient.Proofs.Resid`: given the conservation law
`∑_a θ^{(t)}(s,a) = c` and `max_a θ^{(t)}(s,a) → ∞` (AKM Lemma C.7,
`tendsto_max_theta_atTop`), the minimum coordinate diverges to `-∞`.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section ResidC8

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- The conservation law, iterated: `∑_a θ^{(t)}(s,a) = ∑_a θ^{(0)}(s,a)`. -/
theorem sum_theta_eq_zero (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S)
    (hconst : ∀ t, ∑ a, (θ (t + 1)) (s, a) = ∑ a, (θ t) (s, a)) (t : ℕ) :
    ∑ a, (θ t) (s, a) = ∑ a, (θ 0) (s, a) := by
  induction t with
  | zero => rfl
  | succ n ih => rw [hconst n, ih]

/-- **AKM Lemma C.8** (`lem:diverge`), second half.  With the sum over actions
conserved, `max_a θ^{(t)}(s,a) → ∞` forces `min_a θ^{(t)}(s,a) → -∞`.

If `|A| = 1` the max equals the sum, which is constant, so `hmax` is
contradictory and the conclusion is vacuous; otherwise `|A| ≥ 2` and
`c ≥ Mx t + (|A| - 1) * mn t`, i.e. `mn t ≤ (c - Mx t)/(|A| - 1) → -∞`. -/
theorem tendsto_min_theta_atBot
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S)
    (hconst : ∀ t, ∑ a, (θ (t + 1)) (s, a) = ∑ a, (θ t) (s, a))
    (hmax : Filter.Tendsto (fun t => (Finset.univ : Finset A).sup' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun t => (Finset.univ : Finset A).inf' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atBot := by
  classical
  set c : ℝ := ∑ a, (θ 0) (s, a) with hc
  set Mx : ℕ → ℝ := fun t => (Finset.univ : Finset A).sup' Finset.univ_nonempty
    (fun b => (θ t) (s, b)) with hMxdef
  set mn : ℕ → ℝ := fun t => (Finset.univ : Finset A).inf' Finset.univ_nonempty
    (fun b => (θ t) (s, b)) with hmndef
  have hsum : ∀ t, ∑ a, (θ t) (s, a) = c := fun t => sum_theta_eq_zero θ s hconst t
  -- key inequality: `Mx t + (|A| - 1) * mn t ≤ c`
  have hkey : ∀ t, Mx t + ((Fintype.card A : ℝ) - 1) * mn t ≤ c := by
    intro t
    obtain ⟨a₀, -, ha₀⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A)) (fun b => (θ t) (s, b))
    have hmem : a₀ ∈ (Finset.univ : Finset A) := Finset.mem_univ a₀
    have hlow : ∀ b ∈ (Finset.univ : Finset A).erase a₀, mn t ≤ (θ t) (s, b) := by
      intro b _
      exact Finset.inf'_le (fun b => (θ t) (s, b)) (Finset.mem_univ b)
    have hsplit : (θ t) (s, a₀) + ∑ b ∈ (Finset.univ : Finset A).erase a₀, (θ t) (s, b)
        = ∑ a, (θ t) (s, a) :=
      Finset.add_sum_erase (Finset.univ : Finset A) (fun b => (θ t) (s, b)) hmem
    have hcard : ((Finset.univ : Finset A).erase a₀).card = Fintype.card A - 1 := by
      rw [Finset.card_erase_of_mem hmem, Finset.card_univ]
    have hge : ((Fintype.card A : ℝ) - 1) * mn t
        ≤ ∑ b ∈ (Finset.univ : Finset A).erase a₀, (θ t) (s, b) := by
      have h1 : ∑ _b ∈ (Finset.univ : Finset A).erase a₀, mn t
          ≤ ∑ b ∈ (Finset.univ : Finset A).erase a₀, (θ t) (s, b) :=
        Finset.sum_le_sum hlow
      have h2 : ∑ _b ∈ (Finset.univ : Finset A).erase a₀, mn t
          = ((Fintype.card A : ℝ) - 1) * mn t := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        congr 1
        have : 1 ≤ Fintype.card A := Fintype.card_pos
        push_cast [Nat.cast_sub this]
        ring
      rw [h2] at h1
      exact h1
    have hMx : Mx t = (θ t) (s, a₀) := ha₀
    rw [hMx]
    calc (θ t) (s, a₀) + ((Fintype.card A : ℝ) - 1) * mn t
        ≤ (θ t) (s, a₀) + ∑ b ∈ (Finset.univ : Finset A).erase a₀, (θ t) (s, b) := by
          linarith
      _ = ∑ a, (θ t) (s, a) := hsplit
      _ = c := hsum t
  rcases Nat.lt_or_ge (Fintype.card A) 2 with hsmall | hbig
  · -- `|A| = 1`: `Mx t = c` for all `t`, contradicting `hmax`.
    exfalso
    have hone : Fintype.card A = 1 := by
      have : 1 ≤ Fintype.card A := Fintype.card_pos
      omega
    have hMxc : ∀ t, Mx t = c := by
      intro t
      have := hkey t
      rw [hone] at this
      push_cast at this
      -- now `Mx t + 0 * mn t ≤ c`; need also `c ≤ Mx t` from the sum being a
      -- single term bounded by the max.
      have hub : ∑ a, (θ t) (s, a) ≤ ∑ _a : A, Mx t :=
        Finset.sum_le_sum fun b _ =>
          Finset.le_sup' (fun b => (θ t) (s, b)) (Finset.mem_univ b)
      rw [Finset.sum_const, Finset.card_univ, hone, one_smul, hsum t] at hub
      linarith
    have := (Filter.tendsto_atTop.mp hmax) (c + 1)
    obtain ⟨t, ht⟩ := this.exists
    rw [hMxc t] at ht
    linarith
  · -- `|A| ≥ 2`
    have hpos : (0:ℝ) < (Fintype.card A : ℝ) - 1 := by
      have : (2:ℝ) ≤ (Fintype.card A : ℝ) := by exact_mod_cast hbig
      linarith
    refine Filter.tendsto_atBot.mpr fun b => ?_
    have hMxev := (Filter.tendsto_atTop.mp hmax) (c - ((Fintype.card A : ℝ) - 1) * b)
    filter_upwards [hMxev] with t ht
    have h1 := hkey t
    -- `Mx t ≥ c - (card - 1) * b` and `Mx t + (card-1) * mn t ≤ c`
    have h2 : ((Fintype.card A : ℝ) - 1) * mn t ≤ ((Fintype.card A : ℝ) - 1) * b := by
      linarith
    exact le_of_mul_le_mul_left h2 hpos

end ResidC8

end Proofs
end PolicyGradient
