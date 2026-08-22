/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.ResidC8

/-!
# ResidAsm — assembly of AKM Appendix C.1 towards the residual goal
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section ResidAsm

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **The reduction.** Under the goal's hypotheses, if the goal fails at
`(s, ap)` then `min_a θ^{(t)}(s,a) → -∞` at that state. -/
theorem min_theta_atBot_of_counterexample (M : FiniteMDP S A)
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
    (s : S) (ap : A) (hzero : (πbar s) ap = 0) (hpos : 0 < advInf M πbar s ap) :
    Filter.Tendsto (fun t => (Finset.univ : Finset A).inf' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atBot := by
  obtain ⟨c, T, hc⟩ := not_theta_atBot_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ θ hstep
    πbar hlim s ap hpos
  -- shift the lower bound to hold for ALL `t` by taking the min over `[0,T]`
  have hlow : ∀ t, min c ((Finset.range (T + 1)).inf' (by simp)
      (fun k => (θ k) (s, ap))) ≤ (θ t) (s, ap) := by
    intro t
    rcases Nat.lt_or_ge t T with hlt | hge
    · refine le_trans (min_le_right _ _) ?_
      exact Finset.inf'_le (fun k => (θ k) (s, ap)) (by simp [Nat.lt_succ_of_lt hlt])
    · exact le_trans (min_le_left _ _) (hc t hge)
  have hpi0 : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) ap) Filter.atTop (nhds 0) := by
    have := tendsto_pi_coord F θ πbar hlim s ap
    rwa [hzero] at this
  have hmax := tendsto_max_theta_atTop M F hF θ s ap _ hlow hpi0
  exact tendsto_min_theta_atBot θ s
    (fun t => sum_theta_const M F hF hr hγ₀ hγ₁ μ η θ hstep s t) hmax

/-! ### Pigeonhole: some fixed action has `liminf θ^{(t)}(s,b) = -∞`

`min_a θ^{(t)}(s,a) → -∞` says the minimum over a **finite** set diverges. By
pigeonhole some fixed `b` attains the minimum infinitely often, so
`θ^{(t)}(s,b)` is unbounded below along a subsequence. -/

theorem exists_action_unbounded_below
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S)
    (hmin : Filter.Tendsto (fun t => (Finset.univ : Finset A).inf' Finset.univ_nonempty
        (fun b => (θ t) (s, b))) Filter.atTop Filter.atBot) :
    ∃ b : A, ∀ C : ℝ, ∀ N : ℕ, ∃ t, N ≤ t ∧ (θ t) (s, b) ≤ C := by
  classical
  by_contra hcon
  push_neg at hcon
  -- for each `b` there is a bound `C b` and time `N b` beyond which `θ(s,b) > C b`
  choose C N hCN using hcon
  -- take the max bound and the max time
  set Cmax : ℝ := (Finset.univ : Finset A).sup' Finset.univ_nonempty C with hCmax
  set Nmax : ℕ := (Finset.univ : Finset A).sup' Finset.univ_nonempty N with hNmax
  -- beyond `Nmax`, every coordinate exceeds its own bound, hence the min exceeds `min_b C b`
  set Cmin : ℝ := (Finset.univ : Finset A).inf' Finset.univ_nonempty C with hCmin
  have hbelow : ∀ t, Nmax ≤ t → Cmin <
      (Finset.univ : Finset A).inf' Finset.univ_nonempty (fun b => (θ t) (s, b)) := by
    intro t ht
    rw [Finset.lt_inf'_iff]
    intro b _
    have hNb : N b ≤ t := le_trans (Finset.le_sup' N (Finset.mem_univ b)) ht
    have := hCN b t hNb
    exact lt_of_le_of_lt (Finset.inf'_le C (Finset.mem_univ b)) this
  -- but the min tends to `-∞`
  obtain ⟨t, ht₁, ht₂⟩ := ((Filter.tendsto_atBot.mp hmin Cmin).and
    (Filter.eventually_ge_atTop Nmax)).exists
  exact absurd ht₁ (not_le.mpr (hbelow t ht₂))

/-! ### The unbounded-below action is off-support with non-positive advantage

Let `b` be the action from `exists_action_unbounded_below`. Then:

* `A^{π̄}(s,b) ≤ 0` — otherwise `not_theta_atBot_of_adv_pos` bounds `θ^{(t)}(s,b)`
  below for all large `t`, and the pigeonhole conclusion contradicts that;
* `π̄(b|s) = 0` — since `θ^{(t)}(s,b)` dips arbitrarily low while some coordinate
  stays bounded below, `π^{(t)}(b|s)` dips arbitrarily close to `0`, and the limit
  `π̄(b|s)` must then be `0`. -/

theorem adv_nonpos_of_unbounded_below (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (b : A)
    (hub : ∀ C : ℝ, ∀ N : ℕ, ∃ t, N ≤ t ∧ (θ t) (s, b) ≤ C) :
    advInf M πbar s b ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, T, hc⟩ := not_theta_atBot_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ θ hstep
    πbar hlim s b hcon
  obtain ⟨t, ht, hle⟩ := hub (c - 1) T
  exact absurd (hc t ht) (not_le.mpr (by linarith))

/-! ### The mass concentrates on `I^s_0`

Every action with `A^{π̄}(s,a) ≠ 0` has `π̄(a|s) = 0`: the positive case is
`tendsto_pi_zero_of_adv_pos`; the negative case follows because
`∑_a π̄(a|s) A^{π̄}(s,a) = 0` with all on-support terms zero
(`advInf_eq_zero_on_support`). So `π̄` is supported inside `I^s_0`. -/

theorem pibar_supported_in_I0 (M : FiniteMDP S A)
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
    (s : S) (a : A) (hne : advInf M πbar s a ≠ 0) :
    (πbar s) a = 0 := by
  by_contra hcon
  have hpos : 0 < (πbar s) a :=
    lt_of_le_of_ne ((πbar s).nonneg a) (Ne.symm hcon)
  exact hne (advInf_eq_zero_on_support M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
    πbar hlim s a hpos)

/-- The total limiting mass is `1`, so the on-support (hence `I^s_0`) actions
carry all of it. -/
theorem sum_pibar_eq_one (πbar : Policy S A) (s : S) :
    ∑ a, (πbar s) a = 1 := (πbar s).sum_eq_one

/-! ### AKM's bound (a): the `I^s_-` mass is negligible against `π^{(t)}(ap|s)`

For `a ∈ I^s_-`, `θ^{(t)}(s,a) → -∞` while `θ^{(t)}(s,ap) ≥ c`, so
`π^{(t)}(a|s)/π^{(t)}(ap|s) = exp(θ_a - θ_ap) ≤ exp(θ_a - c) → 0`. Hence for any
`ε > 0`, eventually `π^{(t)}(a|s) ≤ ε · π^{(t)}(ap|s)`. -/

theorem pi_ratio_small (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (s : S) (a ap : A) (c : ℝ) (T : ℕ)
    (hlow : ∀ t, T ≤ t → c ≤ (θ t) (s, ap))
    (hbot : Filter.Tendsto (fun t => (θ t) (s, a)) Filter.atTop Filter.atBot)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in Filter.atTop, (F.toPolicy (θ t) s) a ≤ ε * (F.toPolicy (θ t) s) ap := by
  -- eventually `θ_a ≤ c + log ε`
  have hev : ∀ᶠ t in Filter.atTop, (θ t) (s, a) ≤ c + Real.log ε :=
    Filter.tendsto_atBot.mp hbot (c + Real.log ε)
  filter_upwards [hev, Filter.eventually_ge_atTop T] with t ht htT
  -- `π(a|s) = exp(θ_a - θ_ap) π(ap|s)` and `exp(θ_a - θ_ap) ≤ exp(log ε) = ε`
  have hratio : (F.toPolicy (θ t) s) a
      = Real.exp ((θ t) (s, a) - (θ t) (s, ap)) * (F.toPolicy (θ t) s) ap := by
    rw [hF, hF]
    exact softmax_ratio (fun a' => (θ t) (s, a')) a ap
  have hexp : Real.exp ((θ t) (s, a) - (θ t) (s, ap)) ≤ ε := by
    have hle : (θ t) (s, a) - (θ t) (s, ap) ≤ Real.log ε := by
      have := hlow t htT; linarith
    calc Real.exp ((θ t) (s, a) - (θ t) (s, ap)) ≤ Real.exp (Real.log ε) :=
          Real.exp_le_exp.mpr hle
      _ = ε := Real.exp_log hε
  rw [hratio]
  exact mul_le_mul_of_nonneg_right hexp ((F.toPolicy (θ t) s).nonneg ap)

/-! ### AKM's bound (c): the `ap` term is bounded below by `π^{(t)}(ap|s)·Δ/2`

By continuity `A^{(t)}(s,ap) ≥ A^{π̄}(s,ap)/2` eventually, so the `ap` summand of
`∑_a π^{(t)}(a|s) A^{(t)}(s,a)` is at least `π^{(t)}(ap|s) · A^{π̄}(s,ap)/2`. -/

theorem ap_term_lower (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (ap : A) (hpos : 0 < advInf M πbar s ap) :
    ∀ᶠ t in Filter.atTop,
      (F.toPolicy (θ t) s) ap * (advInf M πbar s ap / 2)
        ≤ (F.toPolicy (θ t) s) ap * advInf M (F.toPolicy (θ t)) s ap := by
  filter_upwards [eventually_adv_pos M F hr hγ₀ hγ₁ θ πbar hlim s ap hpos] with t ht
  exact mul_le_mul_of_nonneg_left ht ((F.toPolicy (θ t) s).nonneg ap)

/-- **AKM's bound (b) ingredient**: on `I^s_0` the trajectory advantage vanishes,
so those summands are `o(1)` uniformly against any fixed positive scale. -/
theorem I0_adv_small (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) (hzero : advInf M πbar s a = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in Filter.atTop, |advInf M (F.toPolicy (θ t)) s a| ≤ ε := by
  have hA := tendsto_adv_traj M F hr hγ₀ hγ₁ θ πbar hlim s a
  rw [hzero] at hA
  have habs : Filter.Tendsto (fun t => |advInf M (F.toPolicy (θ t)) s a|)
      Filter.atTop (nhds 0) := by simpa using hA.abs
  exact habs.eventually_le_const hε

/-! ### The limiting mass sits on `I^s_0`, quantitatively

`∑_{a : A^{π̄}(s,a) = 0} π̄(a|s) = 1`, since every other action has `π̄(a|s) = 0`
(`pibar_supported_in_I0`). -/

theorem sum_I0_pibar_eq_one (M : FiniteMDP S A)
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
    (s : S) :
    ∑ a ∈ Finset.univ.filter (fun a => advInf M πbar s a = 0), (πbar s) a = 1 := by
  classical
  rw [← (πbar s).sum_eq_one]
  refine Finset.sum_subset (f := fun a : A => (πbar s) a)
    (Finset.filter_subset (fun a => advInf M πbar s a = 0) Finset.univ) ?_
  intro a _ hnot
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
  exact pibar_supported_in_I0 M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim s a hnot

end ResidAsm

end Proofs
end PolicyGradient
