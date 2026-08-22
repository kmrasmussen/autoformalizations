
/-! ## The tied set: exact spread, and nonnegativity on a whole band of states -/

omit [DecidableEq S] [DecidableEq A] [Nonempty S] [Nonempty A] in
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

omit [DecidableEq S] [DecidableEq A] [Nonempty S] [Nonempty A] in
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
