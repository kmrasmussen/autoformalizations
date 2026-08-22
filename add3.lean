
/-! ## Gap monotonicity from a *sign split*, with no logit order

`Conv3.gap_monotone_of_adv_dominates` needs `0 ≤ A(s,b) ≤ A(s,a)` *and* the logit
order `θ(s,b) ≤ θ(s,a)`.  The variant below replaces all three by the single
sign split `A(s,b) ≤ 0 ≤ A(s,a)`: then `π(a|s) A(s,a) ≥ 0 ≥ π(b|s) A(s,b)`
outright, because the probabilities are nonnegative.  Together the two lemmas
cover **every** pair in which `a` has the larger advantage: if `A(s,b) ≥ 0` use
`gap_monotone_of_adv_dominates`, otherwise use this one. -/

/-- **Gap monotonicity from a sign split.** -/
theorem gap_monotone_of_sign_split (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a b : A) (t : ℕ)
    (hBnp : advInf M (F.toPolicy (θ t)) s b ≤ 0)
    (hAnn : 0 ≤ advInf M (F.toPolicy (θ t)) s a) :
    (θ t) (s, a) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a) - (θ (t + 1)) (s, b) := by
  have hda := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a
  have hdb := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s b
  have hdnn : 0 ≤ dinfDist M (F.toPolicy (θ t)) μ s := dinfDist_nonneg M hγ₀ _ _ _
  have hkey : (F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b
      ≤ (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a := by
    have h1 : (F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ((F.toPolicy (θ t) s).nonneg b) hBnp
    have h2 : (0 : ℝ) ≤ (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a :=
      mul_nonneg ((F.toPolicy (θ t) s).nonneg a) hAnn
    linarith
  have hprod : 0 ≤ η * (dinfDist M (F.toPolicy (θ t)) μ s
      * ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a
          - (F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b)) :=
    mul_nonneg hη₀.le (mul_nonneg hdnn (by linarith))
  nlinarith [hda, hdb, hprod]

/-- **The union of the two gap-monotonicity criteria.**  If `a`'s advantage
dominates `b`'s at time `t`, and either `b`'s advantage is nonnegative and `b`
trails `a` in logits, or `b`'s advantage is nonpositive, the gap `θ(s,a) - θ(s,b)`
does not shrink at that step.  In particular this covers **every** `b` once `a`
maximises the advantage over the tied set and that maximum is nonnegative. -/
theorem gap_monotone_of_adv_max (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a b : A) (t : ℕ)
    (hdom : advInf M (F.toPolicy (θ t)) s b ≤ advInf M (F.toPolicy (θ t)) s a)
    (hAnn : 0 ≤ advInf M (F.toPolicy (θ t)) s a)
    (hge : (θ t) (s, b) ≤ (θ t) (s, a)) :
    (θ t) (s, a) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a) - (θ (t + 1)) (s, b) := by
  rcases le_or_lt (advInf M (F.toPolicy (θ t)) s b) 0 with hb | hb
  · exact gap_monotone_of_sign_split M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s a b t hb hAnn
  · exact gap_monotone_of_adv_dominates M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s a b t
      hdom hb.le hge
