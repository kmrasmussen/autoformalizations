
/-! ## The residual is a statement about the *direction* of `δ_t`, not its rate

`tied_adv_sub` says the tied advantage order at `s` is the reverse of the order
of the linear forms `a ↦ ⟨P(·|s,a), δ_t⟩` on `Z`.  Those forms are **positively
homogeneous** in `δ_t`, so the order they induce depends on `δ_t` only through
its *direction* `δ_t / ‖δ_t‖`.  That is what converts the residual of
`softmax_policy_converges_of_tied_argmax_stable` from a rate question (how fast
do the coordinates of `δ_t` decay relative to one another?) into a question about
a sequence in a **compact** set: the direction vectors live in the simplex-like
set `{u ≥ 0 : max u = 1}`, which is compact, so directions always have convergent
subsequences.

What compactness does *not* give is *convergence of the whole* direction
sequence — and that is exactly the remaining gap, in its sharpest form.  See the
module header. -/

omit [Nonempty S] [Nonempty A] in
/-- **Positive homogeneity of the tied order.**  Scaling the gap vector by any
`κ > 0` scales every advantage difference on the tied set by `κ`, hence preserves
the order (and the argmax) of `A^{(t)}(s,·)` on `Z`.  So the tied argmax is a
function of the *direction* of `δ_t` alone. -/
theorem tied_order_pos_homogeneous (M : FiniteMDP S A)
    (s : S) (a b : A) (δ : S → ℝ) (κ : ℝ) :
    ((∑ s', (M.P s b) s' * (κ * δ s')) - ∑ s', (M.P s a) s' * (κ * δ s'))
      = κ * ((∑ s', (M.P s b) s' * δ s') - ∑ s', (M.P s a) s' * δ s') := by
  classical
  have h : ∀ x : A, ∑ s', (M.P s x) s' * (κ * δ s') = κ * ∑ s', (M.P s x) s' * δ s' := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s' _ => by ring)
  rw [h a, h b]; ring

/-- **The tied argmax is the argmin of the transition-weighted gap.**  For
`a₀, b` both tied at `s`, `A^{(t)}(s,b) ≤ A^{(t)}(s,a₀)` holds exactly when
`⟨P(·|s,a₀), δ_t⟩ ≤ ⟨P(·|s,b), δ_t⟩`, provided `γ > 0`.  (At `γ = 0` the two
advantages are equal and both orders are trivial — which is `Conv3`'s `γ = 0`
closure, recovered.) -/
theorem tied_adv_le_iff (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a₀ b : A) (t : ℕ)
    (hγ : 0 < M.γ)
    (hVa : Vbar s = M.r s a₀ + M.γ * (∑ s', (M.P s a₀) s' * Vbar s'))
    (hVb : Vbar s = M.r s b + M.γ * (∑ s', (M.P s b) s' * Vbar s')) :
    advInf M (π t) s b ≤ advInf M (π t) s a₀ ↔
      (∑ s', (M.P s a₀) s' * (Vbar s' - Vinf M (π t) s'))
        ≤ ∑ s', (M.P s b) s' * (Vbar s' - Vinf M (π t) s') := by
  have hsub := tied_adv_sub M π Vbar s a₀ b t hVa hVb
  constructor
  · intro h; nlinarith [hsub]
  · intro h; nlinarith [hsub]
