/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Resid

/-!
# ResidC9 — AKM Appendix C.1, Lemma C.9 second claim (`lem:ratios`)

Along the gradient-ascent trajectory, a coordinate whose limiting advantage is
negative diverges to `-∞`.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section ResidC9

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **AKM Lemma C.3, negative case.** Eventually `A^{(t)}(s,a) ≤ A^{π̄}(s,a)/2`
whenever `A^{π̄}(s,a) < 0`. -/
theorem eventually_adv_neg (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) (hneg : advInf M πbar s a < 0) :
    ∀ᶠ t in Filter.atTop, advInf M (F.toPolicy (θ t)) s a ≤ advInf M πbar s a / 2 := by
  have hA := tendsto_adv_traj M F hr hγ₀ hγ₁ θ πbar hlim s a
  have hhalf : advInf M πbar s a < advInf M πbar s a / 2 := by linarith
  exact (hA.eventually (eventually_lt_nhds hhalf)).mono fun t ht => le_of_lt ht

/-- **AKM Lemma C.5, negative case.** Once `A^{(t)}(s,a) < 0`, the coordinate
`θ^{(t)}(s,a)` is strictly decreasing. -/
theorem theta_decreasing_of_adv_neg (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (η : ℝ) (hη₀ : 0 < η)
    (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A)
    (hadv : advInf M (F.toPolicy θ) s a < 0) :
    (θ + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) θ) (s, a) < θ (s, a) := by
  have hgrad := gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ θ s a
  have hdpos : 0 < dinfDist M (F.toPolicy θ) μ s :=
    lt_of_lt_of_le (hμ s) (mu_le_dinfDist M hγ₀ hγ₁ _ μ s)
  have hpipos : 0 < (F.toPolicy θ s) a := by
    rw [hF]; exact softmax_pos _ a
  have hprod : dinfDist M (F.toPolicy θ) μ s
      * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) < 0 :=
    mul_neg_of_pos_of_neg hdpos (mul_neg_of_pos_of_neg hpipos hadv)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hgrad]
  nlinarith [hprod, hη₀]

/-- `θ^{(t)}(s,a)` is antitone from any time after which the advantage is
negative. -/
theorem theta_eventually_antitone (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a : A) (T : ℕ)
    (hT : ∀ t, T ≤ t → advInf M (F.toPolicy (θ t)) s a < 0) :
    ∀ t, T ≤ t → (θ t) (s, a) ≤ (θ T) (s, a) := by
  intro t ht
  induction t with
  | zero =>
      have : T = 0 := Nat.le_zero.mp ht
      rw [this]
  | succ n ih =>
      rcases Nat.lt_or_ge T (n + 1) with hlt | hge
      · have hTn : T ≤ n := Nat.lt_succ_iff.mp hlt
        have hd := theta_decreasing_of_adv_neg M F hF hr hγ₀ hγ₁ μ hμ η hη₀
          (θ n) s a (hT n hTn)
        rw [← hstep n] at hd
        exact le_trans (le_of_lt hd) (ih hTn)
      · have : T = n + 1 := le_antisymm ht hge
        rw [this]

/-! ### `min_a θ^{(t)}(s,a) → -∞` (the easy half of AKM Lemma C.8)

`tendsto_max_theta_atTop` gives `max_a θ^{(t)}(s,a) → ∞`, and `sum_theta_const`
says `∑_a θ^{(t)}(s,a)` is constant. Since
`∑_a θ ≥ max_a θ + (|A|-1) · min_a θ`, the minimum must diverge to `-∞`. -/

/-- `∑_a f a ≥ (sup' f) + (card - 1) * (inf' f)` on a nonempty finite type. -/
theorem sum_ge_sup_add_card_sub_one_mul_inf (f : A → ℝ) :
    (Finset.univ : Finset A).sup' Finset.univ_nonempty f
        + ((Fintype.card A : ℝ) - 1) * (Finset.univ : Finset A).inf' Finset.univ_nonempty f
      ≤ ∑ b, f b := by
  classical
  set Mx : ℝ := (Finset.univ : Finset A).sup' Finset.univ_nonempty f with hMx
  set mn : ℝ := (Finset.univ : Finset A).inf' Finset.univ_nonempty f with hmn
  obtain ⟨b₀, -, hb₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A)) f
  have hsplit : ∑ b, f b = f b₀ + ∑ b ∈ (Finset.univ : Finset A).erase b₀, f b := by
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ b₀)]
  have hlow : ∀ b ∈ (Finset.univ : Finset A).erase b₀, mn ≤ f b := fun b _ =>
    Finset.inf'_le f (Finset.mem_univ b)
  have hcard : ((Finset.univ : Finset A).erase b₀).card = Fintype.card A - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ b₀), Finset.card_univ]
  have hsum : ((Fintype.card A : ℝ) - 1) * mn
      ≤ ∑ b ∈ (Finset.univ : Finset A).erase b₀, f b := by
    have h1 : ∑ b ∈ (Finset.univ : Finset A).erase b₀, mn
        ≤ ∑ b ∈ (Finset.univ : Finset A).erase b₀, f b :=
      Finset.sum_le_sum hlow
    rw [Finset.sum_const, nsmul_eq_mul, hcard] at h1
    have hc1 : (1:ℕ) ≤ Fintype.card A := Fintype.card_pos
    have : ((Fintype.card A - 1 : ℕ) : ℝ) = (Fintype.card A : ℝ) - 1 := by
      push_cast [Nat.cast_sub hc1]; ring
    rwa [this] at h1
  rw [hsplit, hMx, ← hb₀]
  linarith [hsum]

/-- **The easy half of AKM Lemma C.8.** If `max_a θ^{(t)}(s,a) → ∞` while
`∑_a θ^{(t)}(s,a)` stays constant, then `min_a θ^{(t)}(s,a) → -∞`. -/
theorem tendsto_min_theta_atBot_of_max (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S)
    (C : ℝ) (hconst : ∀ t, ∑ b, (θ t) (s, b) = C)
    (hmax : Filter.Tendsto (fun t => (Finset.univ : Finset A).sup' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun t => (Finset.univ : Finset A).inf' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atBot := by
  classical
  set Mx : ℕ → ℝ := fun t => (Finset.univ : Finset A).sup' Finset.univ_nonempty
    (fun b => (θ t) (s, b)) with hMx
  set mn : ℕ → ℝ := fun t => (Finset.univ : Finset A).inf' Finset.univ_nonempty
    (fun b => (θ t) (s, b)) with hmn
  have hkey : ∀ t, Mx t + ((Fintype.card A : ℝ) - 1) * mn t ≤ C := by
    intro t
    have := sum_ge_sup_add_card_sub_one_mul_inf (fun b => (θ t) (s, b))
    rw [hconst t] at this
    exact this
  rcases Nat.lt_or_ge 1 (Fintype.card A) with hc | hc
  · -- `|A| ≥ 2`: `mn t ≤ (C - Mx t)/(|A|-1) → -∞`
    have hcpos : (0:ℝ) < (Fintype.card A : ℝ) - 1 := by
      have : (1:ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hc
      linarith
    refine Filter.tendsto_atBot.mpr fun b => ?_
    have hb := Filter.tendsto_atTop.mp hmax (C - ((Fintype.card A : ℝ) - 1) * b)
    refine hb.mono fun t ht => ?_
    have h := hkey t
    nlinarith [h, ht, hcpos]
  · -- `|A| = 1`: `Mx t ≤ C` for all `t`, contradicting `Mx → ∞`
    have hc1 : Fintype.card A = 1 := le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_succ_of_le hc))
      Fintype.card_pos
    exfalso
    have hMle : ∀ t, Mx t ≤ C := by
      intro t
      have := hkey t
      rw [hc1] at this
      simpa using this
    have := Filter.tendsto_atTop.mp hmax (C + 1)
    obtain ⟨t, ht⟩ := this.exists
    linarith [hMle t, ht]

/-! ### The step decrement, and the ratio bound (AKM `lem:ratios`)

For any action `b`, the decrement of `θ(s,b)` over one step is
`-η · d^{(t)}_μ(s) · π^{(t)}(b|s) · A^{(t)}(s,b)`. -/

/-- One step's decrement of a coordinate, in closed form. -/
theorem theta_decrement (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (t : ℕ) (s : S) (b : A) :
    (θ t) (s, b) - (θ (t + 1)) (s, b)
      = η * (dinfDist M (F.toPolicy (θ t)) μ s
          * ((F.toPolicy (θ t) s) b * (- advInf M (F.toPolicy (θ t)) s b))) := by
  rw [hstep t]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ (θ t) s b]
  ring

/-- **The uniform step bound.** No coordinate moves by more than
`2η/(1-γ)²` in one step. -/
theorem theta_step_bound (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (t : ℕ) (s : S) (b : A) :
    (θ t) (s, b) - 2 * η / (1 - M.γ) ^ 2 ≤ (θ (t + 1)) (s, b) := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hdec := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s b
  set d : ℝ := dinfDist M (F.toPolicy (θ t)) μ s with hd
  set π : ℝ := (F.toPolicy (θ t) s) b with hπ
  set Aq : ℝ := advInf M (F.toPolicy (θ t)) s b with hAq
  have hdnn : 0 ≤ d := dinfDist_nonneg M hγ₀ _ _ _
  have hdle : d ≤ 1 / (1 - M.γ) := by
    rw [hd]; unfold dinfDist
    calc ∑ s₀, μ s₀ * dinf M (F.toPolicy (θ t)) s₀ s
        ≤ ∑ s₀, μ s₀ * (1 / (1 - M.γ)) :=
          Finset.sum_le_sum fun s₀ _ =>
            mul_le_mul_of_nonneg_left (dinf_le_one_div M hγ₀ hγ₁ _ _ _) (μ.nonneg s₀)
      _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]
  have hπ0 : 0 ≤ π := (F.toPolicy (θ t) s).nonneg b
  have hπ1 : π ≤ 1 := by
    rw [hπ]
    have hle : (F.toPolicy (θ t) s) b ≤ ∑ j, (F.toPolicy (θ t) s) j :=
      Finset.single_le_sum (fun j _ => (F.toPolicy (θ t) s).nonneg j) (Finset.mem_univ b)
    rwa [(F.toPolicy (θ t) s).sum_eq_one] at hle
  have hAb : |Aq| ≤ 2 / (1 - M.γ) := abs_advInf_le M (F.toPolicy (θ t)) hr hγ₀ hγ₁ s b
  have hAle : -Aq ≤ 2 / (1 - M.γ) := le_trans (neg_le_abs _) hAb
  have hAge : -(2 / (1 - M.γ)) ≤ -Aq := by
    have := neg_abs_le Aq; linarith [abs_le.mp hAb]
  -- bound the product
  have hbound : d * (π * (-Aq)) ≤ 2 / (1 - M.γ) ^ 2 := by
    have hzz : (0:ℝ) ≤ 2 / (1 - M.γ) ^ 2 := by positivity
    have h1 : π * (-Aq) ≤ 2 / (1 - M.γ) := by
      rcases le_or_gt (-Aq) 0 with hn | hp
      · have hle0 : π * (-Aq) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hπ0 hn
        have : (0:ℝ) ≤ 2 / (1 - M.γ) := by positivity
        linarith
      · calc π * (-Aq) ≤ 1 * (-Aq) := by nlinarith
          _ = -Aq := one_mul _
          _ ≤ 2 / (1 - M.γ) := hAle
    rcases le_or_gt 0 (π * (-Aq)) with h2 | h2
    · calc d * (π * (-Aq)) ≤ (1 / (1 - M.γ)) * (2 / (1 - M.γ)) :=
            mul_le_mul hdle h1 h2 (by positivity)
        _ = 2 / (1 - M.γ) ^ 2 := by field_simp
    · have hle0 : d * (π * (-Aq)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hdnn (le_of_lt h2)
      linarith
  have : (θ t) (s, b) - (θ (t + 1)) (s, b) ≤ 2 * η / (1 - M.γ) ^ 2 := by
    rw [hdec]
    calc η * (d * (π * (-Aq))) ≤ η * (2 / (1 - M.γ) ^ 2) :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt hη₀)
      _ = 2 * η / (1 - M.γ) ^ 2 := by ring
  linarith

/-! ### The ratio bound

For a step `t` at which `θ^{(t)}(s,a) ≥ θ₀` and `θ^{(t)}(s,a') ≤ θ₀ - δ`, the
softmax identity `π(a|s) = exp(θ(s,a) - θ(s,a')) π(a'|s)` gives
`π^{(t)}(a|s) ≥ exp δ · π^{(t)}(a'|s)`. Combined with `-A^{(t)}(s,a) ≥ Δ` and
`-A^{(t)}(s,a') ≤ 2/(1-γ)`, one step decreases `θ(s,a)` at least
`ρ = exp δ · (1-γ)Δ/2` times as much as it decreases `θ(s,a')`. -/

theorem ratio_step (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a a' : A) (t : ℕ) (Δ δ : ℝ) (hΔ : 0 < Δ) (hδ : 0 ≤ δ)
    (hadv : advInf M (F.toPolicy (θ t)) s a ≤ -Δ)
    (hgap : (θ t) (s, a') + δ ≤ (θ t) (s, a)) :
    Real.exp δ * ((1 - M.γ) * Δ / 2) * ((θ t) (s, a') - (θ (t + 1)) (s, a'))
      ≤ (θ t) (s, a) - (θ (t + 1)) (s, a) := by
  have hpos : 0 < 1 - M.γ := by linarith
  set ρ : ℝ := Real.exp δ * ((1 - M.γ) * Δ / 2) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  set d : ℝ := dinfDist M (F.toPolicy (θ t)) μ s with hd
  have hdnn : 0 ≤ d := dinfDist_nonneg M hγ₀ _ _ _
  have hdeca := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a
  have hdeca' := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a'
  set πa : ℝ := (F.toPolicy (θ t) s) a with hπa
  set πa' : ℝ := (F.toPolicy (θ t) s) a' with hπa'
  set Aa : ℝ := advInf M (F.toPolicy (θ t)) s a with hAa
  set Aa' : ℝ := advInf M (F.toPolicy (θ t)) s a' with hAa'
  have hπa'pos : 0 < πa' := by rw [hπa', hF]; exact softmax_pos _ a'
  -- softmax ratio
  have hratio : πa = Real.exp ((θ t) (s, a) - (θ t) (s, a')) * πa' := by
    rw [hπa, hπa', hF, hF]
    exact softmax_ratio (fun a'' => (θ t) (s, a'')) a a'
  have hπge : Real.exp δ * πa' ≤ πa := by
    rw [hratio]
    have : Real.exp δ ≤ Real.exp ((θ t) (s, a) - (θ t) (s, a')) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right this (le_of_lt hπa'pos)
  -- the two decrements
  rw [hdeca, hdeca']
  have hπanonneg : 0 ≤ πa := (F.toPolicy (θ t) s).nonneg a
  have hAnn : 0 ≤ -Aa := by rw [hAa]; linarith [hadv]
  have hlhs : 0 ≤ d * (πa * (-Aa)) := mul_nonneg hdnn (mul_nonneg hπanonneg hAnn)
  rcases le_or_gt (-Aa') 0 with hn | hp
  · -- `θ(s,a')` does not decrease at this step: the right-hand side is `≤ 0`
    have hrhs : d * (πa' * (-Aa')) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdnn
        (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hπa'pos) hn)
    have hηr : η * (d * (πa' * (-Aa'))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hη₀) hrhs
    have hfin : ρ * (η * (d * (πa' * (-Aa')))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hρpos) hηr
    have hL : 0 ≤ η * (d * (πa * (-Aa))) := mul_nonneg (le_of_lt hη₀) hlhs
    linarith
  · -- both decrease: use the ratio
    have hAa'le : -Aa' ≤ 2 / (1 - M.γ) := by
      have hAb : |Aa'| ≤ 2 / (1 - M.γ) :=
        abs_advInf_le M (F.toPolicy (θ t)) hr hγ₀ hγ₁ s a'
      exact le_trans (neg_le_abs _) hAb
    -- `πa' * (-Aa') * ρ ≤ πa * (-Aa)`
    have hkey : ρ * (πa' * (-Aa')) ≤ πa * (-Aa) := by
      have h1 : ρ * (πa' * (-Aa')) ≤ ρ * (πa' * (2 / (1 - M.γ))) := by
        have : πa' * (-Aa') ≤ πa' * (2 / (1 - M.γ)) :=
          mul_le_mul_of_nonneg_left hAa'le (le_of_lt hπa'pos)
        exact mul_le_mul_of_nonneg_left this (le_of_lt hρpos)
      have h2 : ρ * (πa' * (2 / (1 - M.γ))) = (Real.exp δ * πa') * Δ := by
        rw [hρ]; field_simp
      have h3 : (Real.exp δ * πa') * Δ ≤ πa * Δ :=
        mul_le_mul_of_nonneg_right hπge (le_of_lt hΔ)
      have h4 : πa * Δ ≤ πa * (-Aa) := by
        have : Δ ≤ -Aa := by rw [hAa]; linarith [hadv]
        exact mul_le_mul_of_nonneg_left this hπanonneg
      linarith [h1, h2.le, h2.ge, h3, h4]
    -- multiply by `η * d ≥ 0`
    have hηd : 0 ≤ η * d := mul_nonneg (le_of_lt hη₀) hdnn
    have := mul_le_mul_of_nonneg_left hkey hηd
    nlinarith [this]

/-! ### The stopping-time induction (AKM's `τ(t)` construction, done by induction)

AKM define `τ(t)` as the last iteration at which `θ(s,a')` was still above the
threshold `L = θ₀ - δ`, then telescope the ratio bound over `(τ(t), t)`. The same
conclusion follows from a direct induction on `t`, which is what we do here: the
"last crossing" is never named, because the induction hypothesis at `t` already
encodes the accumulated ratio bound since that crossing.

`hstepineq` is the ratio bound (one step below the threshold), `hbnd` the uniform
step bound, `hanti` the antitonicity of `θ(s,a)`. -/

/-- A sequence with `u (t+1) ≤ u t` for all `t ≥ T` is antitone from `T`. -/
theorem antitone_from {u : ℕ → ℝ} {T : ℕ}
    (hanti : ∀ t, T ≤ t → u (t + 1) ≤ u t) : ∀ t, T ≤ t → u t ≤ u T := by
  intro t
  induction t with
  | zero => intro ht; rw [Nat.le_zero.mp ht]
  | succ n ih =>
      intro ht
      rcases Nat.lt_or_ge T (n + 1) with hlt | hge
      · have hTn : T ≤ n := Nat.lt_succ_iff.mp hlt
        exact le_trans (hanti n hTn) (ih hTn)
      · have : T = n + 1 := le_antisymm ht hge
        rw [this]

theorem ratio_induction {u v : ℕ → ℝ} {T : ℕ} {ρ B L : ℝ}
    (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hanti : ∀ t, T ≤ t → u (t + 1) ≤ u t)
    (hbnd : ∀ t, T ≤ t → v t - B ≤ v (t + 1))
    (hstart : L ≤ v T)
    (hstepineq : ∀ t, T ≤ t → v t ≤ L → ρ * (v t - v (t + 1)) ≤ u t - u (t + 1)) :
    ∀ t, T ≤ t → ρ * (L - B - v t) ≤ u T - u t := by
  have hmono := antitone_from hanti
  intro t
  induction t with
  | zero =>
      intro ht
      have hT : T = 0 := Nat.le_zero.mp ht
      rw [hT] at hstart ⊢
      nlinarith [hρ, hB, hstart]
  | succ n ih =>
      intro ht
      rcases Nat.lt_or_ge T (n + 1) with hlt | hge
      · have hTn : T ≤ n := Nat.lt_succ_iff.mp hlt
        rcases le_or_gt (v (n + 1)) (L - B) with hlow | hhigh
        · -- below the threshold: `v n ≤ L` must hold, else the step bound is violated
          have hvnL : v n ≤ L := by
            by_contra hcon
            push_neg at hcon
            have := hbnd n hTn
            linarith
          have hst := hstepineq n hTn hvnL
          have hIH := ih hTn
          linarith
        · -- above the threshold: the claim is trivial from antitonicity
          have hle : u (n + 1) ≤ u T := hmono (n + 1) ht
          nlinarith [hρ, hhigh, hle]
      · have hTe : T = n + 1 := le_antisymm ht hge
        rw [← hTe]
        nlinarith [hρ, hB, hstart]

/-! ### Extracting a single unboundedly-negative coordinate

`min_a θ^{(t)}(s,a) → -∞` means the coordinates are jointly unbounded below.
Since `A` is finite, one *fixed* action must already be unbounded below along
`t ≥ T` (otherwise each coordinate has its own floor and the minimum of those
floors bounds the minimum). -/

theorem exists_coord_unbounded_below (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S) (T : ℕ)
    (hmin : Filter.Tendsto (fun t => (Finset.univ : Finset A).inf' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atBot) :
    ∃ a', ∀ c : ℝ, ∃ t, T ≤ t ∧ (θ t) (s, a') < c := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every coordinate has a floor `c b` valid from `T` on
  have hfloor : ∀ b : A, ∃ c : ℝ, ∀ t, T ≤ t → c ≤ (θ t) (s, b) := by
    intro b
    obtain ⟨c, hc⟩ := hcon b
    exact ⟨c, fun t ht => hc t ht⟩
  choose c hc using hfloor
  set c₀ : ℝ := (Finset.univ : Finset A).inf' Finset.univ_nonempty c with hc₀
  have hlow : ∀ t, T ≤ t →
      c₀ ≤ (Finset.univ : Finset A).inf' Finset.univ_nonempty (fun b => (θ t) (s, b)) := by
    intro t ht
    refine Finset.le_inf' _ _ fun b _ => ?_
    exact le_trans (Finset.inf'_le c (Finset.mem_univ b)) (hc b t ht)
  have hev := Filter.tendsto_atBot.mp hmin (c₀ - 1)
  obtain ⟨t, ht₁, ht₂⟩ := ((Filter.eventually_ge_atTop T).and hev).exists
  linarith [hlow t ht₁, ht₂]

/-! ### `max_a θ^{(t)}(s,a) → ∞` under `hplus`

Given `a₊` with `A^{π̄}(s,a₊) > 0`: `eventually_adv_pos` gives a time `T₊` past
which `A^{(t)}(s,a₊) > 0`, so `theta_eventually_monotone` makes
`θ^{(t)}(s,a₊)` nondecreasing from `T₊`; extending the floor over the finitely
many earlier iterates gives a *global* lower bound, and
`tendsto_pi_zero_of_adv_pos` gives `π^{(t)}(a₊|s) → 0`. -/

/-- A sequence bounded below from `T` on is bounded below globally. -/
theorem exists_global_lower_bound (f : ℕ → ℝ) (T : ℕ) (c : ℝ)
    (h : ∀ t, T ≤ t → c ≤ f t) : ∃ c', ∀ t, c' ≤ f t := by
  classical
  refine ⟨min c ((Finset.range (T + 1)).inf' (by simp) f), fun t => ?_⟩
  rcases le_or_gt T t with ht | ht
  · exact le_trans (min_le_left _ _) (h t ht)
  · refine le_trans (min_le_right _ _) ?_
    exact Finset.inf'_le f (Finset.mem_range.mpr (by omega))

theorem tendsto_max_theta_atTop_of_hplus (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (ap : A) (hpos : 0 < advInf M πbar s ap) :
    Filter.Tendsto (fun t => (Finset.univ : Finset A).sup' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atTop := by
  -- `π^{(t)}(ap|s) → 0`
  have hbar : (πbar s) ap = 0 :=
    tendsto_pi_zero_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim s ap hpos
  have hzero : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) ap) Filter.atTop (nhds 0) := by
    have h1 := (tendsto_pi_nhds.mp hlim) s
    have h2 := (tendsto_pi_nhds.mp h1) ap
    rwa [hbar] at h2
  -- `θ^{(t)}(s,ap)` is bounded below
  obtain ⟨T, hT⟩ := (eventually_adv_pos M F hr hγ₀ hγ₁ θ πbar hlim s ap hpos).exists_forall_of_atTop
  have hTpos : ∀ t, T ≤ t → 0 < advInf M (F.toPolicy (θ t)) s ap := by
    intro t ht
    have := hT t ht
    linarith [hpos]
  have hmono := theta_eventually_monotone M F hF hr hγ₀ hγ₁ μ hμ η hη₀ θ hstep s ap T hTpos
  obtain ⟨c, hc⟩ := exists_global_lower_bound (fun t => (θ t) (s, ap)) T ((θ T) (s, ap)) hmono
  exact tendsto_max_theta_atTop M F hF θ s ap c hc hzero

/-! ## AKM Lemma C.9, second claim (`lem:ratios`)

`θ^{(t)}(s,a) → -∞` whenever `A^{π̄}(s,a) < 0` and `I^s_+ ≠ ∅`.

Structure of the proof. Let `Δ = -A^{π̄}(s,a)/2 > 0` and pick `T₁` past which
`A^{(t)}(s,a) ≤ -Δ`; then `θ^{(t)}(s,a)` is antitone from `T₁`
(`theta_decreasing_of_adv_neg`). Suppose it does **not** diverge; antitonicity
then makes it bounded below by some `θ₀` from `T₁` on.

`hplus` gives `max_b θ^{(t)}(s,b) → ∞` (`tendsto_max_theta_atTop_of_hplus`), and
the conservation law `∑_b θ^{(t)}(s,b) = const` (`sum_theta_const`) turns this
into `min_b θ^{(t)}(s,b) → -∞` (`tendsto_min_theta_atBot_of_max`), hence one
fixed action `a'` has `θ^{(t)}(s,a')` unbounded below on `t ≥ T₁`.

Choose `δ ≥ 0` with `L := θ₀ - δ ≤ θ^{(T₁)}(s,a')`. Whenever
`θ^{(t)}(s,a') ≤ L` we have `θ^{(t)}(s,a') + δ ≤ θ₀ ≤ θ^{(t)}(s,a)`, so
`ratio_step` applies with `ρ = exp δ · (1-γ)Δ/2 > 0`. `ratio_induction` — which
is AKM's `τ(t)` telescoping, recast as an induction — then gives, for all
`t ≥ T₁`,

`ρ · (L - B - θ^{(t)}(s,a')) ≤ θ^{(T₁)}(s,a) - θ^{(t)}(s,a) ≤ θ^{(T₁)}(s,a) - θ₀`,

with `B = 2η/(1-γ)²` the uniform step bound. Taking `t` with `θ^{(t)}(s,a')`
sufficiently negative contradicts that fixed upper bound. -/

theorem theta_tendsto_atBot_of_adv_neg (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) (hneg : advInf M πbar s a < 0)
    (hplus : ∃ ap, 0 < advInf M πbar s ap) :
    Filter.Tendsto (fun t => (θ t) (s, a)) Filter.atTop Filter.atBot := by
  classical
  have hposγ : 0 < 1 - M.γ := by linarith
  obtain ⟨ap, hap⟩ := hplus
  -- `Δ` from the negative limiting advantage
  set Δ : ℝ := -(advInf M πbar s a) / 2 with hΔdef
  have hΔ : 0 < Δ := by rw [hΔdef]; linarith
  obtain ⟨T₁, hT₁⟩ :=
    (eventually_adv_neg M F hr hγ₀ hγ₁ θ πbar hlim s a hneg).exists_forall_of_atTop
  have hadvle : ∀ t, T₁ ≤ t → advInf M (F.toPolicy (θ t)) s a ≤ -Δ := by
    intro t ht
    have := hT₁ t ht
    rw [hΔdef]; linarith
  have hadvneg : ∀ t, T₁ ≤ t → advInf M (F.toPolicy (θ t)) s a < 0 := by
    intro t ht; linarith [hadvle t ht, hΔ]
  -- `θ^{(t)}(s,a)` decreases from `T₁` on
  have hanti : ∀ t, T₁ ≤ t → (θ (t + 1)) (s, a) ≤ (θ t) (s, a) := by
    intro t ht
    have := theta_decreasing_of_adv_neg M F hF hr hγ₀ hγ₁ μ hμ η hη₀ (θ t) s a (hadvneg t ht)
    rw [← hstep t] at this
    exact le_of_lt this
  -- suppose it does not diverge
  by_contra hcon
  rw [Filter.tendsto_atBot] at hcon
  push_neg at hcon
  obtain ⟨θ₀, hθ₀⟩ := hcon
  have hfloor : ∀ t, T₁ ≤ t → θ₀ ≤ (θ t) (s, a) := by
    intro t ht
    obtain ⟨t', hlt', hgt'⟩ := ((hθ₀.and_eventually (Filter.eventually_ge_atTop t)).exists)
    have hmono' := antitone_from (u := fun k => (θ k) (s, a)) (T := t)
      (fun k hk => hanti k (le_trans ht hk)) t' hgt'
    simp only at hmono'
    linarith [hlt', hmono']
  -- `max_b θ^{(t)}(s,b) → ∞`, hence `min_b → -∞`
  have hmax := tendsto_max_theta_atTop_of_hplus M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
    πbar hlim s ap hap
  have hconst : ∀ t, ∑ b, (θ t) (s, b) = ∑ b, (θ 0) (s, b) := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [sum_theta_const M F hF hr hγ₀ hγ₁ μ η θ hstep s n]; exact ih
  have hmin := tendsto_min_theta_atBot_of_max θ s (∑ b, (θ 0) (s, b)) hconst hmax
  obtain ⟨a', ha'⟩ := exists_coord_unbounded_below θ s T₁ hmin
  -- the threshold `L` and the ratio constant `ρ`
  set δ : ℝ := max 0 (θ₀ - (θ T₁) (s, a')) with hδdef
  have hδ : 0 ≤ δ := le_max_left _ _
  set L : ℝ := θ₀ - δ with hLdef
  have hstart : L ≤ (θ T₁) (s, a') := by
    rw [hLdef, hδdef]
    rcases le_or_gt (θ₀ - (θ T₁) (s, a')) 0 with h | h
    · rw [max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (le_of_lt h)]; linarith
  set ρ : ℝ := Real.exp δ * ((1 - M.γ) * Δ / 2) with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  set B : ℝ := 2 * η / (1 - M.γ) ^ 2 with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  -- the hypotheses of `ratio_induction`
  have hbnd : ∀ t, T₁ ≤ t → (θ t) (s, a') - B ≤ (θ (t + 1)) (s, a') := by
    intro t _
    exact theta_step_bound M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep t s a'
  have hstepineq : ∀ t, T₁ ≤ t → (θ t) (s, a') ≤ L →
      ρ * ((θ t) (s, a') - (θ (t + 1)) (s, a'))
        ≤ (θ t) (s, a) - (θ (t + 1)) (s, a) := by
    intro t ht hle
    have hgap : (θ t) (s, a') + δ ≤ (θ t) (s, a) := by
      have := hfloor t ht
      rw [hLdef] at hle
      linarith
    exact ratio_step M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s a a' t Δ δ hΔ hδ
      (hadvle t ht) hgap
  have hkey := ratio_induction (u := fun t => (θ t) (s, a)) (v := fun t => (θ t) (s, a'))
    (T := T₁) hρ hB hanti hbnd hstart hstepineq
  -- contradiction: pick `t` with `θ^{(t)}(s,a')` very negative
  obtain ⟨t, ht, hlt⟩ := ha' (L - B - ((θ T₁) (s, a) - θ₀) / ρ - 1)
  have h1 := hkey t ht
  have h2 : (θ T₁) (s, a) - (θ t) (s, a) ≤ (θ T₁) (s, a) - θ₀ := by
    linarith [hfloor t ht]
  have h3 : ((θ T₁) (s, a) - θ₀) / ρ + 1 < L - B - (θ t) (s, a') := by linarith
  have h4 : ρ * (((θ T₁) (s, a) - θ₀) / ρ + 1) < ρ * (L - B - (θ t) (s, a')) :=
    mul_lt_mul_of_pos_left h3 hρ
  have h5 : ρ * (((θ T₁) (s, a) - θ₀) / ρ + 1) = ((θ T₁) (s, a) - θ₀) + ρ := by
    field_simp
  rw [h5] at h4
  simp only at h1
  linarith [h1, h2, h4, hρ]

end ResidC9

end Proofs
end PolicyGradient
