
/-! ## Two unconditional consequences of `(★)`

### The gap vanishes when the source vanishes

`(★)` says `δ = c + γ P^π δ`.  Taking `s` to be a maximiser and then a minimiser
of `δ` gives `(1-γ)·max δ ≤ max c` and `min c ≤ (1-γ)·min δ`.  With `c ≡ 0` both
squeeze `δ` to `0`: the value gap is *identically zero* as soon as every action
is tied at every state.  That closes the "all actions tied everywhere" case of
the frozen goal outright — every advantage is `0` at every finite time, so no
logit ever moves. -/

/-- **`c ≡ 0` forces `δ ≡ 0`.**  If `Vbar` satisfies the Bellman identity for
*every* action at every state (equivalently, `gapSource` vanishes identically),
then `Vbar = V^π` for every policy `π`. -/
theorem gap_eq_zero_of_gapSource_eq_zero (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (Vbar : S → ℝ) (π : Policy S A)
    (hc : ∀ s, gapSource M Vbar π s = 0) (s : S) :
    Vbar s = Vinf M π s := by
  classical
  obtain ⟨smax, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset S)
    (fun s' => Vbar s' - Vinf M π s') Finset.univ_nonempty
  obtain ⟨smin, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset S)
    (fun s' => Vbar s' - Vinf M π s') Finset.univ_nonempty
  have hup : (1 - M.γ) * (Vbar smax - Vinf M π smax) ≤ 0 := by
    have := one_sub_gamma_mul_gap_le_gapSource M hr hγ₀ hγ₁ Vbar π smax
      (fun s' => hmax s' (Finset.mem_univ s'))
    rw [hc smax] at this; exact this
  have hlo : 0 ≤ (1 - M.γ) * (Vbar smin - Vinf M π smin) := by
    have := gapSource_le_one_sub_gamma_mul_gap M hr hγ₀ hγ₁ Vbar π smin
      (fun s' => hmin s' (Finset.mem_univ s'))
    rw [hc smin] at this; exact this
  have hγpos : 0 < 1 - M.γ := by linarith
  have hmaxle : Vbar smax - Vinf M π smax ≤ 0 := nonpos_of_mul_nonpos_left
    (by linarith) hγpos
  have hminge : 0 ≤ Vbar smin - Vinf M π smin := nonneg_of_mul_nonneg_right
    (by linarith) hγpos
  have h1 : Vbar s - Vinf M π s ≤ 0 :=
    le_trans (hmax s (Finset.mem_univ s)) hmaxle
  have h2 : 0 ≤ Vbar s - Vinf M π s :=
    le_trans hminge (hmin s (Finset.mem_univ s))
  linarith

/-! ### The logit sum at each state is a conserved quantity

`theta_decrement` gives `θ_{t+1}(s,a) - θ_t(s,a) = η · d^{(t)}(s) · π_t(a|s)
A^{(t)}(s,a)`.  Summing over `a` and applying the zero-mean identity
`∑_a π(a|s) A^π(s,a) = 0` makes the total move `0`: softmax policy gradient never
changes `∑_a θ_t(s,a)`, at any state.  This is an exact invariant of the flow,
πbar-free and unconditional, and it constrains where the logits can go: the mass
that the tied block gains in logit terms is exactly what the untied block
loses. -/

/-- **The logit sum at each state is invariant along the ascent.** -/
theorem logit_sum_invariant (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (t : ℕ) (s : S) :
    ∑ a, (θ (t + 1)) (s, a) = ∑ a, (θ t) (s, a) := by
  classical
  have hdec : ∀ a : A, (θ t) (s, a) - (θ (t + 1)) (s, a)
      = η * dinfDist M (F.toPolicy (θ t)) μ s
          * ((F.toPolicy (θ t) s) a * (- advInf M (F.toPolicy (θ t)) s a)) := by
    intro a
    rw [theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a]; ring
  have hzero := sum_pi_advInf_self M hr hγ₀ hγ₁ (F.toPolicy (θ t)) s
  have hsum : ∑ a, ((θ t) (s, a) - (θ (t + 1)) (s, a)) = 0 := by
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hdec a),
      ← Finset.mul_sum]
    have : ∑ a, (F.toPolicy (θ t) s) a * (- advInf M (F.toPolicy (θ t)) s a)
        = - ∑ a, (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [this, hzero, neg_zero, mul_zero]
  rw [Finset.sum_sub_distrib] at hsum
  linarith
