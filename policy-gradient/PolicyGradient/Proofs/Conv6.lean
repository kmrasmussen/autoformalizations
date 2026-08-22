/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv5

/-!
# Conv6 — the value-gap vector obeys its own Bellman recursion

WORK IN PROGRESS.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv6

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- The limiting advantage of `Vbar`: `Abar(s,a) = r(s,a) + γ⟨P(·|s,a),Vbar⟩ - Vbar s`.
This is `advInf` with `Vinf M π` replaced by the limit `Vbar`; it is a function of
`Vbar` alone, with no policy in it. -/
noncomputable def advOf (M : FiniteMDP S A) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * (∑ s', (M.P s a) s' * V s') - V s

/-- The **gap source term** `c_t(s) := -∑_a π(a|s) · Abar(s,a)`. -/
noncomputable def gapSource (M : FiniteMDP S A) (Vbar : S → ℝ) (π : Policy S A)
    (s : S) : ℝ :=
  -∑ a, (π s) a * advOf M Vbar s a

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- **(★) The value-gap Bellman recursion.**  Writing `δ s := Vbar s - V^π s`,

```
δ s = c(s) + γ · ∑_a π(a|s) ∑_{s'} P(s'|s,a) · δ s'
```

with `c = gapSource`.  Unconditional: no limit policy, no hypothesis on `Vbar`
beyond being a function.  It is the exact statement that `δ` is the value of the
*reward* `c` under `π`, i.e. `δ = (I - γ P^π)⁻¹ c`. -/
theorem gap_bellman (M : FiniteMDP S A) (hr : ∀ s a, |M.r s a| ≤ 1)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (Vbar : S → ℝ) (π : Policy S A) (s : S) :
    Vbar s - Vinf M π s
      = gapSource M Vbar π s
        + M.γ * (∑ a, (π s) a * (∑ s', (M.P s a) s' * (Vbar s' - Vinf M π s'))) := by
  classical
  have hV : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  have hone : ∑ a, (π s) a = 1 := (π s).sum_eq_one
  -- expand everything into a single sum over `a`
  have hsplit : ∀ a : A, (π s) a * (∑ s', (M.P s a) s' * (Vbar s' - Vinf M π s'))
      = (π s) a * (∑ s', (M.P s a) s' * Vbar s')
        - (π s) a * (∑ s', (M.P s a) s' * Vinf M π s') := by
    intro a
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    exact congrArg _ (Finset.sum_congr rfl (fun s' _ => by ring))
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hsplit a),
    Finset.sum_sub_distrib]
  unfold gapSource advOf
  rw [hV]
  have hQ : ∀ a : A, (π s) a * Qinf M π s a
      = (π s) a * M.r s a + (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vinf M π s') := by
    intro a; unfold Qinf; ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hQ a),
    Finset.sum_add_distrib]
  have hA : ∀ a : A, (π s) a * (M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s') - Vbar s)
      = (π s) a * M.r s a + (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vbar s')
        - (π s) a * Vbar s := by
    intro a; ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hA a),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hone, one_mul]
  have hmulγ : ∀ a : A, (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vbar s')
      = M.γ * ((π s) a * ∑ s', (M.P s a) s' * Vbar s') := by intro a; ring
  have hmulγ' : ∀ a : A, (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vinf M π s')
      = M.γ * ((π s) a * ∑ s', (M.P s a) s' * Vinf M π s') := by intro a; ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hmulγ a),
    Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hmulγ' a),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring


/-! ## The max/min sandwich: the gap vector is controlled by its source -/

omit [DecidableEq S] [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- A convex combination of transition rows against a vector bounded above by `M`
is bounded above by `M`. -/
theorem pi_row_le (M : FiniteMDP S A) (π : Policy S A) (s : S) (δ : S → ℝ)
    (c : ℝ) (hδ : ∀ s', δ s' ≤ c) :
    ∑ a, (π s) a * (∑ s', (M.P s a) s' * δ s') ≤ c := by
  classical
  have hrow : ∀ a : A, ∑ s', (M.P s a) s' * δ s' ≤ c := by
    intro a
    calc ∑ s', (M.P s a) s' * δ s'
        ≤ ∑ s', (M.P s a) s' * c :=
          Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hδ s') ((M.P s a).nonneg s')
      _ = c := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
  calc ∑ a, (π s) a * (∑ s', (M.P s a) s' * δ s')
      ≤ ∑ a, (π s) a * c :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrow a) ((π s).nonneg a)
    _ = c := by rw [← Finset.sum_mul, (π s).sum_eq_one, one_mul]

omit [DecidableEq S] [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- The dual bound: a convex combination of rows against a vector bounded below
by `c` is bounded below by `c`. -/
theorem le_pi_row (M : FiniteMDP S A) (π : Policy S A) (s : S) (δ : S → ℝ)
    (c : ℝ) (hδ : ∀ s', c ≤ δ s') :
    c ≤ ∑ a, (π s) a * (∑ s', (M.P s a) s' * δ s') := by
  classical
  have h := pi_row_le M π s (fun s' => -δ s') (-c) (fun s' => by simpa using hδ s')
  have hneg : ∑ a, (π s) a * (∑ s', (M.P s a) s' * (-δ s'))
      = -∑ a, (π s) a * (∑ s', (M.P s a) s' * δ s') := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    exact congrArg _ (Finset.sum_congr rfl (fun s' _ => by ring))
  rw [hneg] at h
  linarith

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- **The max-state sandwich, upper half.**  At a state `s` maximising the value
gap `δ = Vbar - V^π`, the source dominates: `(1-γ)·δ s ≤ c s`.

This is the resolvent bound `‖δ‖_∞ ≤ ‖c‖_∞/(1-γ)` in the form the argument
needs: it turns a *rate* statement about `δ_t` into an *explicit policy*
statement about `c_t = -∑_a π(a|s) Abar(s,a)`, which is a sum of vanishing
off-tie masses. -/
theorem one_sub_gamma_mul_gap_le_gapSource (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (Vbar : S → ℝ) (π : Policy S A) (s : S)
    (hmax : ∀ s', Vbar s' - Vinf M π s' ≤ Vbar s - Vinf M π s) :
    (1 - M.γ) * (Vbar s - Vinf M π s) ≤ gapSource M Vbar π s := by
  have hb := gap_bellman M hr hγ₀ hγ₁ Vbar π s
  have hrow := pi_row_le M π s (fun s' => Vbar s' - Vinf M π s')
    (Vbar s - Vinf M π s) hmax
  nlinarith [hrow]

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- **The min-state sandwich, lower half.**  At a state `s` minimising the value
gap, `c s ≤ (1-γ)·δ s`. -/
theorem gapSource_le_one_sub_gamma_mul_gap (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (Vbar : S → ℝ) (π : Policy S A) (s : S)
    (hmin : ∀ s', Vbar s - Vinf M π s ≤ Vbar s' - Vinf M π s') :
    gapSource M Vbar π s ≤ (1 - M.γ) * (Vbar s - Vinf M π s) := by
  have hb := gap_bellman M hr hγ₀ hγ₁ Vbar π s
  have hrow := le_pi_row M π s (fun s' => Vbar s' - Vinf M π s')
    (Vbar s - Vinf M π s) hmin
  nlinarith [hrow]

/-! ## The tied set: exact spread, and nonnegativity on a whole band of states -/

-- (all section variables are used via `adv_eq_value_gap_of_zero_limit`)
/-- **The exact spread of two tied advantages.**  For `a, b` both with vanishing
limiting advantage at `s`, `(‡)` subtracts to

```
A^{(t)}(s,a) - A^{(t)}(s,b) = γ · ⟨P(·|s,b) - P(·|s,a), δ_t⟩
```

— the whole difference is a fixed linear functional of the gap vector, with the
state-diagonal term `δ_t s` cancelling.  This is the quantity whose *sign* the
leader hypothesis needs. -/
theorem tied_adv_sub (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a b : A) (t : ℕ)
    (hVa : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hVb : Vbar s = M.r s b + M.γ * (∑ s', (M.P s b) s' * Vbar s')) :
    advInf M (π t) s a - advInf M (π t) s b
      = M.γ * ((∑ s', (M.P s b) s' * (Vbar s' - Vinf M (π t) s'))
        - ∑ s', (M.P s a) s' * (Vbar s' - Vinf M (π t) s')) := by
  rw [adv_eq_value_gap_of_zero_limit M π Vbar s a hVa t,
    adv_eq_value_gap_of_zero_limit M π Vbar s b hVb t]
  ring

-- (all section variables are used via `tied_adv_sub`)
/-- **The tied spread is at most `2γ‖δ_t‖_∞`.**  Two tied advantages at the same
state differ by at most twice the discounted sup-norm of the gap vector — so on
the tied set the advantages are asymptotically *equal*, not merely
asymptotically zero. -/
theorem abs_tied_adv_sub_le (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a b : A) (t : ℕ) (c : ℝ)
    (hγ₀ : 0 ≤ M.γ)
    (hVa : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hVb : Vbar s = M.r s b + M.γ * (∑ s', (M.P s b) s' * Vbar s'))
    (hnn : ∀ s', 0 ≤ Vbar s' - Vinf M (π t) s')
    (hub : ∀ s', Vbar s' - Vinf M (π t) s' ≤ c) :
    |advInf M (π t) s a - advInf M (π t) s b| ≤ 2 * M.γ * c := by
  classical
  have hrow : ∀ x : A, (0 : ℝ) ≤ ∑ s', (M.P s x) s' * (Vbar s' - Vinf M (π t) s') ∧
      ∑ s', (M.P s x) s' * (Vbar s' - Vinf M (π t) s') ≤ c := by
    intro x
    refine ⟨Finset.sum_nonneg fun s' _ => mul_nonneg ((M.P s x).nonneg s') (hnn s'), ?_⟩
    calc ∑ s', (M.P s x) s' * (Vbar s' - Vinf M (π t) s')
        ≤ ∑ s', (M.P s x) s' * c :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (hub s') ((M.P s x).nonneg s')
      _ = c := by rw [← Finset.sum_mul, (M.P s x).sum_eq_one, one_mul]
  obtain ⟨hAnn, hAub⟩ := hrow a
  obtain ⟨hBnn, hBub⟩ := hrow b
  rw [tied_adv_sub M π Vbar s a b t hVa hVb, abs_le]
  constructor <;> nlinarith

/-- **Nonnegativity on a whole band of states, not just the argmax.**

If the gap at `s` is at least `γ` times a uniform upper bound `c` on the gap
vector, every tied advantage at `s` is nonnegative.  `adv_nonneg_at_argmax`
is the special case `c = δ_t s`; this version applies at *every* state whose gap
is within a factor `γ` of the largest, which is a strictly larger set of states
and is what makes the sign available at more than one state at a time. -/
theorem adv_nonneg_of_gap_ge (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a : A) (t : ℕ) (c : ℝ)
    (hγ₀ : 0 ≤ M.γ)
    (hVbar : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hub : ∀ s', Vbar s' - Vinf M (π t) s' ≤ c)
    (hband : M.γ * c ≤ Vbar s - Vinf M (π t) s) :
    0 ≤ advInf M (π t) s a := by
  classical
  rw [adv_eq_value_gap_of_zero_limit M π Vbar s a hVbar t]
  have hrow : ∑ s', (M.P s a) s' * (Vbar s' - Vinf M (π t) s') ≤ c := by
    calc ∑ s', (M.P s a) s' * (Vbar s' - Vinf M (π t) s')
        ≤ ∑ s', (M.P s a) s' * c :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (hub s') ((M.P s a).nonneg s')
      _ = c := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
  nlinarith
end Conv6

end Proofs
end PolicyGradient
