
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
