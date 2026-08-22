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

end ResidAsm

end Proofs
end PolicyGradient
