
/-! ## The tied set always carries a nonnegative advantage

The zero-mean identity `∑_a π(a|s) A(s,a) = 0` splits along `Z`.  If every
*untied* action has nonpositive advantage at time `t`, the tied block must carry
nonnegative total weight, and since softmax gives every action strictly positive
probability, **some** tied action has nonnegative advantage.  That is the missing
`hAnn` of `gap_monotone_of_adv_max`, and it is exactly what makes a *maximiser of
the advantage over `Z`* a usable leader: it dominates every tied action by
construction, and `gap_monotone_of_adv_max` then covers the whole tied set with
no further sign hypothesis. -/

/-- **Some tied action has nonnegative advantage.**  More precisely: the
advantage-maximiser over `Z` has nonnegative advantage, whenever every action
outside `Z` has nonpositive advantage. -/
theorem exists_tied_adv_nonneg (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) (Z : Finset A) (hZ : Z.Nonempty)
    (hpos : ∀ a, 0 < (π s) a)
    (hout : ∀ a ∉ Z, advInf M π s a ≤ 0) :
    ∃ a ∈ Z, 0 ≤ advInf M π s a := by
  classical
  by_contra hcon
  push Not at hcon
  have hneg : ∀ a ∈ Z, advInf M π s a < 0 := by
    intro a ha; exact hcon a ha
  have hzero := sum_pi_advInf_eq_zero M hr hγ₀ hγ₁ π s
  have hsplit : ∑ a, (π s) a * advInf M π s a
      = (∑ a ∈ Z, (π s) a * advInf M π s a)
        + ∑ a ∈ Finset.univ \ Z, (π s) a * advInf M π s a := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_self_right (s := Z))]
    · congr 1
      exact (Finset.union_sdiff_of_subset (Finset.subset_univ Z)).symm
  have hZneg : ∑ a ∈ Z, (π s) a * advInf M π s a < 0 := by
    obtain ⟨a₁, ha₁⟩ := hZ
    refine Finset.sum_lt_zero_of_nonpos_of_lt_zero ?_ ⟨a₁, ha₁, ?_⟩
    · intro a ha
      exact mul_nonpos_of_nonneg_of_nonpos (hpos a).le (hneg a ha).le
    · exact mul_neg_of_pos_of_neg (hpos a₁) (hneg a₁ ha₁)
  have hOnp : ∑ a ∈ Finset.univ \ Z, (π s) a * advInf M π s a ≤ 0 :=
    Finset.sum_nonpos fun a ha =>
      mul_nonpos_of_nonneg_of_nonpos (hpos a).le
        (hout a (Finset.mem_sdiff.mp ha).2)
  rw [hsplit] at hzero
  linarith
