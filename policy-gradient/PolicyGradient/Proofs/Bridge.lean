/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.ResidFinal
import PolicyGradient.Proofs.G9c

/-!
# Bridge — assembling AKM Theorem 5.1 and Mei Lemma 9

## What is proved here, and what is NOT

The task this file was opened for assumed the two frozen goals
(`softmax_ascent_converges`, `g9_c_positive`) were separated from their
ingredients by a **signature mismatch** only — `μ : Dist S` / `VinfDist` versus
`μ : S` / `Vinf`. That is **not** the case, and this file records the real gap.

### Proved (all axiom-clean)

* `vinf_pibar_eq_vstar` — composes `limit_adv_nonpos_offsupport_proof`
  (the residual, `ResidFinal.lean:812`), `full_adv_nonpos_of_offsupport`
  (`ResidAsm.lean:253`) and `vinf_eq_vstar_of_adv_nonpos` (`AKM51b.lean:241`)
  to get `∀ s, Vinf M πbar s = Vstar M s` at a limit policy. Note the `Dist`
  signature is *already* what the residual chain uses, so there was never a
  `Dist`/single-state bridge to build on this side.
* `tendsto_vstar_of_policy_limit` — **`softmax_ascent_converges` verbatim,
  except that it additionally assumes `hlim`**, the coordinatewise convergence
  of the FULL policy sequence. Everything else in the frozen statement is
  matched exactly (`hμ`, `η ≤ (1-γ)²/5`, the `VinfDist` step).
* `advInf_eq_zero_on_support_subseq` — the on-support half restated along a
  subsequence, demonstrating that half *is* subsequence-robust.
* `g9_of_eventual_lower_bound` — `g9_c_positive`'s conclusion from a uniform
  eventual lower bound at `astar`, with the finitely many early terms handled
  by softmax positivity. Generalizes `g9_of_policy_limit` (`G9b.lean:942`).
* `g9_of_policy_limit_bridge` — **`g9_c_positive` verbatim, except that it too
  additionally assumes `hlim`**. Worth recording: G9's step size `(1-γ)³/8`
  *does* satisfy the residual chain's `η ≤ (1-γ)²/5` for `0 ≤ γ < 1`, so the
  chain applies to G9 unchanged. Both frozen goals therefore reduce to the
  SAME single missing fact, stated below.

### The actual obstruction

Both goals now reduce to ONE missing statement:

  `∃ πbar, Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
      (nhds (fun s a => (πbar s) a))`  —  from `hstep` alone.

Compactness (`isCompact_PolySet`, `exists_subseq_tendsto_policy`,
`AKM51b.lean:384,414`) supplies only a **subsequential** limit. The residual
chain cannot consume one: its spine repeatedly turns a full-sequence `hlim`
into an `∀ᶠ t in atTop` sign fact, calls `.exists_forall_of_atTop` to get
`∀ t, T ≤ t → …`, and then **inducts on `t → t+1`** against `hstep`. The
step-inductions need the sign at *every* intermediate time, which a subsequence
(with unbounded gaps) does not provide. The three root break points are

* `eventually_adv_pos` (`Resid.lean:830`) → `theta_eventually_monotone`
  (`Resid.lean:1029`) → `not_theta_atBot_of_adv_pos` (`Resid.lean:1289`);
* `eventually_adv_neg` (`ResidC9.lean:25`) → `theta_tendsto_atBot_of_adv_neg`
  (`ResidC9.lean:493`), whose `ratio_induction` telescopes step by step;
* `exists_T0` (`ResidFinal.lean:114`), whose `hT0ord` output is baked into the
  *definition* of `B0` (`ResidFinal.lean:84`) as a `∀ t, T0 ≤ t` condition.

So closing these goals needs full-sequence policy convergence — a genuinely new
theorem that neither AKM's Appendix C.1 nor this repo proves, and one that is
delicate: under `Q*` ties the policy sequence need not converge at all (that is
exactly the phenomenon `g9_c_positive_frozen_is_false` exploits). It is NOT a
signature bridge.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Bridge

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- Scratch: the residual composed with the support upgrade and optimality. -/
theorem vinf_pibar_eq_vstar (M : FiniteMDP S A)
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
      (nhds (fun s a => (πbar s) a))) :
    ∀ s, Vinf M πbar s = Vstar M s := by
  have hadv : ∀ s a, advInf M πbar s a ≤ 0 :=
    full_adv_nonpos_of_offsupport M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim
      (limit_adv_nonpos_offsupport_proof M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim)
  exact fun s => vinf_eq_vstar_of_adv_nonpos M hr hγ₀ hγ₁ πbar hadv s

/-- Goal A given a full-sequence policy limit. -/
theorem tendsto_vstar_of_policy_limit (M : FiniteMDP S A)
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
    Filter.Tendsto (fun t => Vinf M (F.toPolicy (θ t)) s) Filter.atTop
      (nhds (Vstar M s)) := by
  have h := tendsto_Vinf_of_tendsto_policy M hr hγ₀ hγ₁
    (fun t => F.toPolicy (θ t)) πbar hlim s
  rwa [vinf_pibar_eq_vstar M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim s] at h

/-- On-support half, along a SUBSEQUENCE limit. -/
theorem advInf_eq_zero_on_support_subseq (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun k s a => (F.toPolicy (θ (φ k)) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) (hsupp : 0 < (πbar s) a) :
    advInf M πbar s a = 0 := by
  have hprod0 := tendsto_pi_adv_zero M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep s a
  have hprod := hprod0.comp hφ.tendsto_atTop
  have hpi : Filter.Tendsto (fun k => (F.toPolicy (θ (φ k)) s) a) Filter.atTop
      (nhds ((πbar s) a)) := by
    have h1 := (tendsto_pi_nhds.mp hlim) s
    exact (tendsto_pi_nhds.mp h1) a
  have hA := tendsto_adv_traj M F hr hγ₀ hγ₁ (fun k => θ (φ k)) πbar hlim s a
  have hlimprod : Filter.Tendsto
      (fun k => (F.toPolicy (θ (φ k)) s) a * advInf M (F.toPolicy (θ (φ k))) s a)
      Filter.atTop (nhds ((πbar s) a * advInf M πbar s a)) := hpi.mul hA
  have heq : (πbar s) a * advInf M πbar s a = 0 :=
    tendsto_nhds_unique hlimprod hprod
  rcases mul_eq_zero.mp heq with h | h
  · exact absurd h (ne_of_gt hsupp)
  · exact h

/-! ### G9 from a uniform eventual lower bound at `astar` -/

/-- If every coordinate `π^{(t)}(a*(s)|s)` is eventually bounded below by a
positive constant, the infimum over time is positive. The finitely many early
terms are positive by softmax positivity. -/
theorem g9_of_eventual_lower_bound (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (astar : S → A)
    (m : ℝ) (hm : 0 < m) (N : ℕ)
    (hN : ∀ t, N ≤ t → ∀ s, m ≤ (F.toPolicy (θ t) s) (astar s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := by
  classical
  set early : Finset ℕ := Finset.range N with hearly
  set c : ℝ := min m
    (if h : early.Nonempty then
      early.inf' h (fun t => ⨅ s : S, (F.toPolicy (θ t) s) (astar s)) else m) with hc
  refine ⟨c, ?_, ?_⟩
  · rw [hc]
    refine lt_min hm ?_
    by_cases h : early.Nonempty
    · rw [dif_pos h]
      exact (Finset.lt_inf'_iff h).2 fun t _ => iInf_pi_pos F hF (θ t) astar
    · rw [dif_neg h]; exact hm
  · intro t
    by_cases ht : N ≤ t
    · exact le_trans (min_le_left _ _) (le_ciInf fun s => hN t ht s)
    · push_neg at ht
      have hmem : t ∈ early := Finset.mem_range.mpr ht
      have hne : early.Nonempty := ⟨t, hmem⟩
      refine le_trans (min_le_right _ _) ?_
      rw [dif_pos hne]
      exact Finset.inf'_le _ hmem

/-- **`g9_c_positive` verbatim, except for the extra `hlim`.**

Given the full-sequence policy limit, Goal A's `vinf_pibar_eq_vstar` makes the
limit value-optimal at every state, `gap_concentrates` turns `hgap` into
`π̄(a*(s)|s) = 1`, and `g9_of_policy_limit` produces the constant. Note the
frozen G9 step size is `(1-γ)³/8`, which satisfies `η ≤ (1-γ)²/5` for
`0 ≤ γ < 1`, so the residual chain applies to it too — that inequality is
discharged here as `hηbound`. -/
theorem g9_of_policy_limit_bridge (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a))) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := by
  have hposγ : (0:ℝ) < 1 - M.γ := by linarith
  have hη₀ : (0:ℝ) < (1 - M.γ) ^ 3 / 8 := by positivity
  -- `(1-γ)³/8 ≤ (1-γ)²/5` since `(1-γ) ≤ 1`
  have hηbound : (1 - M.γ) ^ 3 / 8 ≤ (1 - M.γ) ^ 2 / 5 := by
    have h1 : 1 - M.γ ≤ 1 := by linarith
    nlinarith [sq_nonneg (1 - M.γ), hposγ]
  have hopt : ∀ s, Vinf M πbar s = Vstar M s :=
    vinf_pibar_eq_vstar M F hF hr hγ₀ hγ₁ μ hμ _ hη₀ hηbound θ hstep πbar hlim
  exact g9_of_optimal_policy_limit M F hF hr hγ₀ hγ₁ θ πstar hstar astar hastar hgap
    πbar hlim hopt

end Bridge

end Proofs
end PolicyGradient
