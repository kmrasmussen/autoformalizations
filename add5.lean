
/-! ## The reduction: an eventually-constant advantage-maximiser on the tied set

Putting the pieces together.  Fix a state `s` with tied set `Z`.  Suppose

* every action outside `Z` has nonpositive advantage from time `T` on, and
* one `a₀ ∈ Z` maximises `A^{(t)}(s,·)` over `Z` for every `t ≥ T`, and leads in
  logits at the single time `T`.

Then `exists_tied_adv_nonneg` makes `A^{(t)}(s,a₀) ≥ 0` (the maximiser over `Z`
is nonnegative because the zero-mean identity forces the tied block to carry the
nonnegative part), `gap_monotone_of_adv_max` makes every gap `θ_t(s,a₀) -
θ_t(s,b)` nondecreasing, and `Conv3.softmax_policy_converges_of_leader` closes
the frozen goal.

Compare `Conv5.softmax_policy_converges_of_argmax_stable`, whose `hstable`
demanded **nonnegativity of every tied advantage** and a comparability clause
tied to the logit order.  Here nonnegativity is *derived*, and the comparability
clause is replaced by the single statement that the argmax of `A^{(t)}(s,·)` over
`Z` is eventually constant — which by `tied_adv_sub` is precisely the statement
that the *order* of the linear functionals `a ↦ ⟨P(·|s,a), δ_t⟩` on `Z` is
eventually constant, i.e. a statement about the **direction** of `δ_t` and
nothing else. -/

/-- **The frozen goal from an eventually-constant tied-advantage maximiser.** -/
theorem softmax_policy_converges_of_tied_argmax_stable (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (hstable : ∀ (s : S) (Z : Finset A),
      (∀ a, a ∈ Z ↔ Tendsto (fun t => advInf M (F.toPolicy (θ t)) s a) atTop (nhds 0)) →
      Z.Nonempty →
      ∃ a₀ ∈ Z, ∃ T : ℕ,
        (∀ b ∈ Z, (θ T) (s, b) ≤ (θ T) (s, a₀)) ∧
        (∀ a ∉ Z, ∀ t, T ≤ t → advInf M (F.toPolicy (θ t)) s a ≤ 0) ∧
        (∀ b ∈ Z, ∀ t, T ≤ t →
          advInf M (F.toPolicy (θ t)) s b ≤ advInf M (F.toPolicy (θ t)) s a₀)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) := by
  classical
  refine softmax_policy_converges_of_leader M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep ?_
  intro s Z hchar
  -- `Z` is nonempty: otherwise the mass at `s` would vanish entirely.
  choose Abar hAbar using exists_adv_tendsto M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep
  have hout : ∀ b ∉ Z, Tendsto (fun t => (F.toPolicy (θ t) s) b) atTop (nhds 0) := by
    intro b hb
    refine tendsto_pi_zero_of_adv_limit_ne M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
      s b (Abar s b) (fun h => hb ((hchar b).mpr ?_)) (hAbar s b)
    rw [← h]; exact hAbar s b
  have hZ : Z.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hmass := tendsto_mass_on_zero_set (fun t => F.toPolicy (θ t)) s Z
      (fun b hb => hout b hb)
    rw [hemp] at hmass
    simp only [Finset.sum_empty] at hmass
    exact absurd (tendsto_nhds_unique tendsto_const_nhds hmass) (by norm_num)
  obtain ⟨a₀, ha₀, T, hTlead, hoffnp, hmaxZ⟩ := hstable s Z hchar hZ
  refine ⟨a₀, ha₀, T, hTlead, ?_⟩
  intro b hb t ht hle
  -- softmax gives every action strictly positive probability at `s`
  have hpos : ∀ a, 0 < (F.toPolicy (θ t) s) a := by
    intro a; rw [hF]; exact softmax_pos _ a
  -- the tied maximiser has nonnegative advantage
  have hAnn : 0 ≤ advInf M (F.toPolicy (θ t)) s a₀ := by
    obtain ⟨a₁, ha₁, hA₁⟩ := exists_tied_adv_nonneg M hr hγ₀ hγ₁
      (F.toPolicy (θ t)) s Z hZ hpos (fun a ha => hoffnp a ha t ht)
    exact le_trans hA₁ (hmaxZ a₁ ha₁ t ht)
  exact gap_monotone_of_adv_max M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s a₀ b t
    (hmaxZ b hb t ht) hAnn hle
