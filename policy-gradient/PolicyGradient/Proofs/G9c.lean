/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G9b

/-!
# G9c — Mei Lemma 9 with a strictly positive optimal value gap

Work file for the third frozen form of `Goal.g9_c_positive`.

**Status: BLOCKED, not refuted.** `hgap` repairs the defect that killed the
previous two versions, and no counterexample survives it. What remains
unproved is a single named external result — Mei's Claim III, which their paper
proves by *citing* Agarwal–Kakade–Lee–Mahajan Theorem 5.1 rather than
establishing it. Everything else in Mei's proof is discharged below.

## What `hgap` fixes

Read verbatim from Mei et al. (arXiv:2005.06392), Lemma 9's opening:

> Denote `Δ*(s) = Q*(s, a*(s)) − max_{a ≠ a*(s)} Q*(s,a) > 0` as the optimal
> value gap of state `s`, where `a*(s)` is the action that the optimal policy
> selects under state `s`.

`hgap` is exactly `Δ*(s) > 0`. Its force is recorded here in three steps:

* `gap_Qstar_astar` — `astar s` really attains `V*(s)` (from `hastar` and
  `optimal_support_greedy_proof`);
* `gap_pistar_det` — `πstar` is forced to be **deterministic** on `astar`;
* `gap_concentrates` — **the decisive one**: any policy attaining `V*(s)` must
  put mass `1` on `astar s`.

`gap_concentrates` is what the previous frozen version lacked. With a `Q*`
tie, two optimal actions can split the mass arbitrarily and the limit may put
`0` on `astar` — which is precisely how `g9_c_positive_frozen_is_false`
refuted it (`γ = 0`, `r = (1,1,0)`; `Q*(s,0) = Q*(s,1)` violates `hgap`).

## Mei's proof, formalized

Mei's Lemma 9 runs on four claims. Three are proved here in full, against the
frozen `hstep` recursion:

| Mei | here | content |
|---|---|---|
| Claim I(a) | `grad_dominant_of_Qmax` | `Q^π`- and mass-dominance at `a*(s)` make its gradient coordinate dominant |
| Claim I(ii) | `pi_mono_step` | a dominant gradient coordinate makes `π_t(a*(s)\|s)` nondecreasing |
| Claim II | `le_of_half_le`, `half_le_c_div` | above Mei's threshold `c(s)/(c(s)+1) ≥ 1/2`, `a*(s)` carries the largest mass |
| Claim IV | `g9_of_eventually_monotone` | eventual monotonicity at every state ⟹ the infimum is a minimum over a finite prefix, hence positive |

`g9_of_eventually_nice` assembles them: it is Mei's Lemma 9 with **only** Claim
III left as a hypothesis. `g9_of_eventually_dominant` is the same reduction
phrased directly on gradient coordinates.

## What is missing, exactly

Claim III says: there is a finite `t₀(s)` with `θ_{t₀(s)}` in the nice region.
Mei establish its first ingredient by citation —

> **Claim III.** (1) According to the asymptotic convergence results of
> \citet[Theorem 5.1]{AgKaLeMa19}, which we can use thanks to
> \cref{ass:posinit}, `π_{θ_t}(a*(s) | s) → 1`.

— and the other two ingredients (`Q^{π_t}(s,a*) → Q*(s,a*)` and
`V^{π_t}(s) → V*(s)`) likewise need per-state value convergence.

Two independent obstructions stand in the way here, both already recorded in
this repo:

1. **AKM Theorem 5.1 is not available.** It is the repo's own open goal
   `Goal.softmax_ascent_converges`; `Proofs.AKM51` proves the whole analytic
   half (`tendsto_norm_grad_zero`, `exists_limit_le_vstar`) and isolates the
   residue as `tendsto_vstar_of_limit_optimal`'s `hclosed`. `Proofs.AKM51b`
   then shows the natural route to `hclosed` cannot work:
   `greedy_support_vacuous_at_det` proves the greedy-support condition holds
   automatically at every deterministic policy, and softmax ascent's limits are
   deterministic because `‖θ t‖ → ∞`. Mei's Lemma 9 and AKM's Theorem 5.1 are
   **mutually reducing** — see the note at the end of `Proofs.AKM51`.

2. **Mei's Assumption 2 is absent from the frozen statement.** Their Lemma 9
   reads "Let Assumption 2 hold", i.e. `min_s μ(s) > 0`; the frozen goal starts
   from a single state `μ : S`, the maximally degenerate violation. Their
   Claim III uses Assumption 2 by name ("which we can use thanks to
   \cref{ass:posinit}"), and the paper's own Proposition immediately after the
   assumption exhibits an MDP with `μ(s) = 0` where ascent converges to a
   **non-optimal** attractor.

   This does **not** refute the goal. `policy_unchanged_of_dinf_zero` shows why:
   at a state of zero occupancy every gradient coordinate vanishes, so the
   logits never move and `π_t(a*(s)|s)` stays at its initial value, which is
   strictly positive by `softmax_pos`. A frozen coordinate is harmless to an
   existential `c`. The damage is only that Claim III's convergence input is
   unavailable at such states — a gap in the proof, not a counterexample.

## Numerical search

Roughly 5000 MDPs were swept (`S ≤ 5`, `A ≤ 3`, integer reward grids, γ ∈
{0, 0.3, 0.5, 0.7, 0.9, 0.95, 0.99}, integer initial logits in `[-10, 10]`,
up to 60000 ascent steps), keeping only MDPs with a strict `Q*` gap at every
state so that `hgap` holds. No trajectory drove `⨅ s, π_t(a*(s)|s)` toward
zero: the small values found were adverse *initializations* followed by
recovery, or frozen zero-occupancy states sitting at their initial value.
Monotonicity of `t ↦ ⨅ s, π_t(a*(s)|s)` does fail (25/288 strict-gap MDPs), so
Mei's "eventually enters a nice region" structure is genuinely needed — the
statement cannot be proved by a global monotonicity argument.

## Two sufficient conditions that do close it

* `g9_of_eventually_nice` — Mei's own route, needing Claim III.
* `g9_of_optimal_policy_limit` — coordinatewise policy convergence to a limit
  that is value-optimal at every state. `hgap` discharges the positivity side
  condition of `g9_of_policy_limit` via `gap_concentrates`. This is the shorter
  route, and it is the one that would follow immediately from AKM Theorem 5.1.
-/

open Finset Filter Topology

namespace PolicyGradient
namespace Proofs

noncomputable section

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

section Gap

/-- Under a strict optimal value gap, `astar s` attains `V*(s)`.

`πstar` is optimal at `s` and puts positive mass on `astar s`
(`hastar`), so `optimal_support_greedy_proof` gives `Q*(s, astar s) = V*(s)`. -/
theorem gap_Qstar_astar (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s)) (s : S) :
    Qstar M s (astar s) = Vstar M s :=
  optimal_support_greedy_proof M hr hγ₀ hγ₁ πstar s (hstar s) (astar s) (hastar s)

/-- Under `hgap`, every action other than `astar s` is **strictly** below `V*(s)`. -/
theorem gap_Qstar_lt (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s))
    (s : S) (a : A) (ha : a ≠ astar s) :
    Qstar M s a < Vstar M s := by
  rw [← gap_Qstar_astar M hr hγ₀ hγ₁ πstar hstar astar hastar s]
  exact hgap s a ha

/-- Under `hgap`, `πstar` is **deterministic**: it puts all its mass on `astar s`. -/
theorem gap_pistar_det (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s))
    (s : S) (a : A) (ha : a ≠ astar s) :
    (πstar s) a = 0 := by
  by_contra h
  have hpos : 0 < (πstar s) a := lt_of_le_of_ne ((πstar s).nonneg a) (Ne.symm h)
  have := optimal_support_greedy_proof M hr hγ₀ hγ₁ πstar s (hstar s) a hpos
  have hlt := gap_Qstar_lt M hr hγ₀ hγ₁ πstar hstar astar hastar hgap s a ha
  exact absurd (show Qstar M s a = Vstar M s from this) (ne_of_lt hlt)

end Gap

section MonotoneStep

/-- **Mei's Claim I(ii), in pure softmax form.**

If the increment `g a*` at the selected action dominates every other increment
`g a`, then the softmax probability of `a*` does not decrease after the update
`w ↦ w + g`.

`π_{new}(a*) = e^{w a* + g a*} / ∑_a e^{w a + g a}
             ≥ e^{w a* + g a*} / ∑_a e^{w a + g a*}
             = e^{w a*} / ∑_a e^{w a} = π_{old}(a*)`,

replacing every `g a` in the denominator by the larger `g a*`. -/
theorem softmax_mono_of_max_increment (w g : A → ℝ) (astar : A)
    (hmax : ∀ a, g a ≤ g astar) :
    (softmax w) astar ≤ (softmax (fun a => w a + g a)) astar := by
  have hden : (0:ℝ) < ∑ a', Real.exp (w a') := softmax_denom_pos w
  have hden' : (0:ℝ) < ∑ a', Real.exp (w a' + g a') :=
    softmax_denom_pos (fun a => w a + g a)
  rw [softmax_apply, softmax_apply, div_le_div_iff₀ hden hden']
  -- `e^{w a*} · ∑ e^{w a + g a} ≤ e^{w a* + g a*} · ∑ e^{w a}`
  have key : ∀ a : A,
      Real.exp (w astar) * Real.exp (w a + g a)
        ≤ Real.exp (w astar + g astar) * Real.exp (w a) := by
    intro a
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by have := hmax a; linarith)
  calc Real.exp (w astar) * ∑ a', Real.exp (w a' + g a')
      = ∑ a', Real.exp (w astar) * Real.exp (w a' + g a') := by rw [Finset.mul_sum]
    _ ≤ ∑ a', Real.exp (w astar + g astar) * Real.exp (w a') :=
        Finset.sum_le_sum fun a' _ => key a'
    _ = Real.exp (w astar + g astar) * ∑ a', Real.exp (w a') := by rw [Finset.mul_sum]

end MonotoneStep

section NiceRegion

/-- **Mei's Claim II, Case (b), in clean form.**

If `π(a*|s) ≥ 1/2` then `a*` carries at least as much mass as any other action.
Mei states this with the threshold `c(s)/(c(s)+1)` where
`c(s) = A/((1-γ)Δ*(s)) - 1`; since `Δ*(s) ≤ 1/(1-γ)` and `A ≥ 2` that threshold
is always `≥ 1/2`, and `1/2` is all the argument needs: two distinct actions
each carrying more than half the mass would exceed the total mass `1`. -/
theorem le_of_half_le (π : Dist A) (astar a : A) (ha : a ≠ astar)
    (h : (1:ℝ)/2 ≤ π astar) : π a ≤ π astar := by
  by_contra hlt
  push_neg at hlt
  -- `π a* + π a ≤ 1` because the two are distinct members of a probability vector
  have hpair : π astar + π a ≤ 1 := by
    have hsub : ({astar, a} : Finset A) ⊆ univ := subset_univ _
    have hne : astar ≠ a := Ne.symm ha
    have hsum : ∑ b ∈ ({astar, a} : Finset A), π b = π astar + π a := by
      rw [Finset.sum_pair hne]
    calc π astar + π a = ∑ b ∈ ({astar, a} : Finset A), π b := hsum.symm
      _ ≤ ∑ b, π b := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun b _ _ => π.nonneg b)
      _ = 1 := π.sum_eq_one
  linarith

/-- The `1/2` threshold is reached by Mei's `c(s)/(c(s)+1)` bound whenever
`Δ*(s) ≤ 1/(1-γ)` and there are at least two actions: then `c(s) ≥ 1`. -/
theorem half_le_c_div (c : ℝ) (hc : 1 ≤ c) : (1:ℝ)/2 ≤ c / (c + 1) := by
  have hpos : (0:ℝ) < c + 1 := by linarith
  rw [le_div_iff₀ hpos]
  linarith

end NiceRegion

section ClaimIV

/-- **Mei's Claims III + IV, as a reduction.**

If for every state `s` there is a finite time `t₀ s` past which
`t ↦ π_t(a*(s)|s)` never decreases, then the infimum over *all* `t` of
`⨅ s, π_t(a*(s)|s)` is attained on the finite prefix `t ≤ max_s t₀ s`, and is
therefore positive by `iInf_pi_pos`.

This is the part of Mei's argument that survives without Assumption 2, and it is
exactly Claims III and IV: Claim III produces the finite `t₀(s)` beyond which
`π_t(a*(s)|s)` is nondecreasing, and Claim IV takes the max over the finitely
many states.  The hypothesis `hmono` is what Claim III supplies and what this
repo cannot: see the module docstring. -/
theorem g9_of_eventually_monotone (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → E S A) (astar : S → A) (t₀ : S → ℕ)
    (hmono : ∀ s, ∀ t, t₀ s ≤ t →
      (F.toPolicy (θ t) s) (astar s) ≤ (F.toPolicy (θ (t+1)) s) (astar s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := by
  classical
  -- the uniform cut-off
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s, t₀ s ≤ N := by
    refine ⟨(univ : Finset S).sup t₀, fun s => Finset.le_sup (mem_univ s)⟩
  -- past `N` every coordinate is nondecreasing, hence `≥` its value at `N`
  have hge : ∀ s, ∀ t, N ≤ t →
      (F.toPolicy (θ N) s) (astar s) ≤ (F.toPolicy (θ t) s) (astar s) := by
    intro s t ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    clear ht
    induction k with
    | zero => simp
    | succ k ih =>
        refine le_trans ih ?_
        have : t₀ s ≤ N + k := le_trans (hN s) (Nat.le_add_right _ _)
        exact hmono s (N + k) this
  -- the candidate constant: the min over the finite prefix `t ≤ N`
  set c : ℝ := (Finset.range (N+1)).inf'
    ⟨N, by simp⟩ (fun t => ⨅ s : S, (F.toPolicy (θ t) s) (astar s)) with hc
  refine ⟨c, ?_, ?_⟩
  · rw [hc]
    exact (Finset.lt_inf'_iff _).2 fun t _ => iInf_pi_pos F hF (θ t) astar
  · intro t
    by_cases ht : t ≤ N
    · exact Finset.inf'_le _ (by simp [Nat.lt_succ_iff, ht])
    · push_neg at ht
      -- `c ≤ value at N ≤ value at t`
      refine le_trans (Finset.inf'_le _ (show N ∈ Finset.range (N+1) by simp)) ?_
      refine le_ciInf fun s => ?_
      refine le_trans ?_ (hge s t ht.le)
      refine ciInf_le ⟨0, ?_⟩ s
      rintro y ⟨x, rfl⟩
      exact (F.toPolicy (θ N) x).nonneg _

end ClaimIV

section ClaimI

/-- **Mei's Claim I, Case (a), in clean form.**

If `a*` already carries at least as much mass as `a`, and `a*`'s advantage
dominates `a`'s, then the gradient coordinate at `a*` dominates the one at `a`.

Both coordinates share the nonnegative occupancy factor `d`, so the comparison
reduces to `π(a*)·A(a*) ≥ π(a)·A(a)`.  Under `hA : A(a) ≤ A(a*)` and
`hAnn : 0 ≤ A(a*)` this follows from `mul_le_mul`. -/
theorem grad_le_of_mass_le (d : ℝ) (hd : 0 ≤ d) (pstar pa astar_adv a_adv : ℝ)
    (hp : 0 ≤ pa) (hmass : pa ≤ pstar)
    (hA : a_adv ≤ astar_adv) (hAnn : 0 ≤ astar_adv) :
    d * (pa * a_adv) ≤ d * (pstar * astar_adv) := by
  refine mul_le_mul_of_nonneg_left ?_ hd
  calc pa * a_adv ≤ pa * astar_adv := mul_le_mul_of_nonneg_left hA hp
    _ ≤ pstar * astar_adv := mul_le_mul_of_nonneg_right hmass hAnn

/-- **The advantage of `a*` is nonnegative when it dominates every action.**

`A^π(s,a*) = Q^π(s,a*) - V^π(s)` and `V^π(s) = ∑_a π(a|s) Q^π(s,a)` is a convex
combination of values all `≤ Q^π(s,a*)`, so the difference is `≥ 0`.  Stated
abstractly over a distribution so it can be reused. -/
theorem adv_nonneg_of_max (π : Dist A) (Q : A → ℝ) (astar : A)
    (hmax : ∀ a, Q a ≤ Q astar) :
    ∑ a, π a * Q a ≤ Q astar := by
  calc ∑ a, π a * Q a ≤ ∑ a, π a * Q astar :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmax a) (π.nonneg a)
    _ = (∑ a, π a) * Q astar := by rw [Finset.sum_mul]
    _ = Q astar := by rw [π.sum_eq_one, one_mul]

end ClaimI

section StepInvariance

/-- **The frozen `hstep` update, read in a single logit coordinate.**

`θ_{t+1}(s,a) = θ_t(s,a) + η · d^{π_t}(μ,s) · π_t(a|s) · A^{π_t}(s,a)`
with `η = (1-γ)³/8`.  This is `gradient_Vinf_coord` transported along `hstep`. -/
theorem step_coord (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A)
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (t : ℕ) (s : S) (a : A) :
    θ (t+1) (s, a)
      = θ t (s, a) + ((1 - M.γ) ^ 3 / 8)
        * (dinf M (F.toPolicy (θ t)) μ s
            * ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)) := by
  have h := congrArg (fun v : E S A => v (s, a)) (hstep t)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
  rw [h, gradient_Vinf_coord M F hF hr hγ₀ hγ₁ μ (θ t) s a]

/-- **Mei's Claim I(ii) along the frozen recursion.**

If at time `t` the gradient coordinate at `astar s` dominates every other
coordinate at state `s`, then `π_{t+1}(astar s | s) ≥ π_t(astar s | s)`.

This is `softmax_mono_of_max_increment` instantiated at the increments produced
by `step_coord`. -/
theorem pi_mono_step (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A)
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (astar : S → A) (t : ℕ) (s : S)
    (hdom : ∀ a, (gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) (s, a)
      ≤ (gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) (s, astar s)) :
    (F.toPolicy (θ t) s) (astar s) ≤ (F.toPolicy (θ (t+1)) s) (astar s) := by
  have hη : (0:ℝ) ≤ (1 - M.γ) ^ 3 / 8 := by
    have : (0:ℝ) ≤ 1 - M.γ := by linarith
    positivity
  -- the increment vector at state `s`
  set g : A → ℝ := fun a => ((1 - M.γ) ^ 3 / 8)
    * (gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) (s, a) with hg
  have hmax : ∀ a, g a ≤ g (astar s) := fun a =>
    mul_le_mul_of_nonneg_left (hdom a) hη
  have hlogit : ∀ a, θ (t+1) (s, a) = θ t (s, a) + g a := by
    intro a
    have h := congrArg (fun v : E S A => v (s, a)) (hstep t)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    rw [h, hg]
  rw [hF (θ t) s (astar s), hF (θ (t+1)) s (astar s)]
  have hrw : (fun a' => θ (t+1) (s, a')) = (fun a' => θ t (s, a') + g a') := by
    funext a'; exact hlogit a'
  rw [hrw]
  exact softmax_mono_of_max_increment (fun a' => θ t (s, a')) g (astar s) hmax

end StepInvariance

section Reduction

/-- **The full reduction of `Goal.g9_c_positive` to Mei's Claim III.**

Given, for each state `s`, a finite time `t₀ s` past which the gradient
coordinate at `astar s` dominates all others at `s` — Mei's "nice region"
`R₁(s) ∩ R₂(s) ∩ R₃(s)`, entered at `t₀(s)` by his Claim III and never left by
his Claim I(i) — the frozen goal follows.

Claims I(ii) (`pi_mono_step`) and IV (`g9_of_eventually_monotone`) are proved
here in full; this theorem is their composition.  The hypothesis `hnice` is
exactly what remains, and it is Claim III. -/
theorem g9_of_eventually_dominant (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A)
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (astar : S → A) (t₀ : S → ℕ)
    (hnice : ∀ s, ∀ t, t₀ s ≤ t → ∀ a,
      (gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) (s, a)
        ≤ (gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) (s, astar s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) :=
  g9_of_eventually_monotone F hF θ astar t₀ fun s t ht =>
    pi_mono_step M F hF hr hγ₀ hγ₁ μ θ hstep astar t s (hnice s t ht)

end Reduction

section Frozen

/-- **A state with zero occupancy has frozen logits.**

If `d^{π_t}(μ, s) = 0` then every gradient coordinate at `s` vanishes
(`gradient_Vinf_coord`), so the update leaves `θ(s, ·)` untouched and the policy
at `s` is unchanged.

This is why the absence of Mei's Assumption 2 (`min_s μ(s) > 0`) does **not**
by itself refute the goal: a state that gradient ascent never sees keeps its
initial softmax probabilities, which are strictly positive
(`softmax_pos`). The danger of a Dirac start state is therefore not that the
probability of `astar` collapses at unreachable states — it cannot move at all
— but that Claim III's convergence input is unavailable there. -/
theorem policy_unchanged_of_dinf_zero (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A)
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (t : ℕ) (s : S) (hd : dinf M (F.toPolicy (θ t)) μ s = 0) (a : A) :
    (F.toPolicy (θ (t+1)) s) a = (F.toPolicy (θ t) s) a := by
  have hcoord : ∀ b : A, θ (t+1) (s, b) = θ t (s, b) := by
    intro b
    rw [step_coord M F hF hr hγ₀ hγ₁ μ θ hstep t s b, hd]
    ring
  rw [hF (θ (t+1)) s a, hF (θ t) s a]
  have : (fun b => θ (t+1) (s, b)) = (fun b => θ t (s, b)) := by
    funext b; exact hcoord b
  rw [this]

end Frozen

section GapConcentration

/-- **The gap turns value-optimality of a limit policy into concentration.**

If `π̄` attains `V*(s)` at `s`, then under `hgap` every action other than
`astar s` has zero mass, so `π̄(astar s | s) = 1`.

This is the step where `hgap` earns its place: without it two tied optimal
actions could share the mass arbitrarily, and `π̄(astar s|s)` could be `0` —
which is exactly how `g9_c_positive_frozen_is_false` refuted the previous
version of the goal. -/
theorem gap_concentrates (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s))
    (πbar : Policy S A) (s : S) (hopt : Vinf M πbar s = Vstar M s) :
    (πbar s) (astar s) = 1 := by
  classical
  -- every action off `astar s` carries zero mass
  have hzero : ∀ a, a ≠ astar s → (πbar s) a = 0 := by
    intro a ha
    by_contra h
    have hpos : 0 < (πbar s) a := lt_of_le_of_ne ((πbar s).nonneg a) (Ne.symm h)
    have hQ := optimal_support_greedy_proof M hr hγ₀ hγ₁ πbar s hopt a hpos
    have hlt := gap_Qstar_lt M hr hγ₀ hγ₁ πstar hstar astar hastar hgap s a ha
    exact absurd (show Qstar M s a = Vstar M s from hQ) (ne_of_lt hlt)
  -- so the total mass sits on `astar s`
  have := (πbar s).sum_eq_one
  rw [← Finset.add_sum_erase Finset.univ (fun b => (πbar s) b)
      (Finset.mem_univ (astar s))] at this
  have hrest : ∑ b ∈ Finset.univ.erase (astar s), (πbar s) b = 0 :=
    Finset.sum_eq_zero fun b hb =>
      hzero b (Finset.mem_erase.mp hb).1
  rw [hrest, add_zero] at this
  exact this

end GapConcentration

section PolicyLimit

/-- **The cleanest sufficient condition, with `hgap` discharging the positivity.**

If the trajectory's policies converge coordinatewise to some `π̄` that is
value-optimal at **every** state, then `hgap` upgrades that to
`π̄(astar s | s) = 1 > 0` at every state (`gap_concentrates`), and
`g9_of_policy_limit` delivers the frozen conclusion.

Compare `g9_of_convergence_is_false`: convergence of the *value at `μ`* is not
enough. What is needed is convergence of the *policy*, plus per-state value
optimality of its limit. -/
theorem g9_of_optimal_policy_limit (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → E S A)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (hopt : ∀ s, Vinf M πbar s = Vstar M s) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := by
  refine g9_of_policy_limit F hF θ astar πbar hlim fun s => ?_
  rw [gap_concentrates M hr hγ₀ hγ₁ πstar hstar astar hastar hgap πbar s (hopt s)]
  norm_num

end PolicyLimit

section ClaimIa

/-- **The advantage of a `Q^π`-dominant action is nonnegative.**

If `Q^π(s,a) ≤ Q^π(s,a*)` for every `a`, then `A^π(s,a*) ≥ 0`, because
`V^π(s)` is the `π(·|s)`-average of the `Q^π(s,·)`. -/
theorem advInf_nonneg_of_Qmax (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) (astar : A)
    (hmax : ∀ a, Qinf M π s a ≤ Qinf M π s astar) :
    0 ≤ advInf M π s astar := by
  rw [advInf_eq]
  have hV : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  have := adv_nonneg_of_max (π s) (fun a => Qinf M π s a) astar hmax
  rw [← hV] at this
  linarith

/-- **Mei's Claim I, Case (a), along the frozen recursion.**

At a state `s` where

* `a*` dominates in `Q^π`  (`hQ`), and
* `a*` already carries at least as much mass as every other action (`hmass`),

the gradient coordinate at `a*` dominates every other coordinate at `s`.

Both coordinates carry the same nonnegative occupancy factor
(`gradient_Vinf_coord`), and `A^π(s,a*) ≥ 0` by `advInf_nonneg_of_Qmax`, so
`grad_le_of_mass_le` applies with `A^π(s,a) = Q^π(s,a) - V^π(s) ≤
Q^π(s,a*) - V^π(s) = A^π(s,a*)`. -/
theorem grad_dominant_of_Qmax (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (w : E S A) (s : S) (astar : A)
    (hQ : ∀ a, Qinf M (F.toPolicy w) s a ≤ Qinf M (F.toPolicy w) s astar)
    (hmass : ∀ a, (F.toPolicy w s) a ≤ (F.toPolicy w s) astar) (a : A) :
    (gradient (fun u => Vinf M (F.toPolicy u) μ) w) (s, a)
      ≤ (gradient (fun u => Vinf M (F.toPolicy u) μ) w) (s, astar) := by
  rw [gradient_Vinf_coord M F hF hr hγ₀ hγ₁ μ w s a,
      gradient_Vinf_coord M F hF hr hγ₀ hγ₁ μ w s astar]
  refine grad_le_of_mass_le _ (dinf_nonneg M hγ₀ _ _ _) _ _ _ _
    ((F.toPolicy w s).nonneg a) (hmass a) ?_ ?_
  · -- advantages compare because they differ from `Q` by the same `V`
    rw [advInf_eq, advInf_eq]
    have := hQ a
    linarith
  · exact advInf_nonneg_of_Qmax M hr hγ₀ hγ₁ (F.toPolicy w) s astar hQ

end ClaimIa

section Assembled

/-- **Mei's Lemma 9, assembled from Claims I(a), I(ii) and IV.**

Everything in Mei's proof except Claim III is discharged here.  The hypothesis
`hnice` is Claim III's output: for each state a finite entry time past which
`a*(s)` both dominates in `Q^{π_t}` and carries the largest mass — Mei's region
`R₁(s) ∩ R₂(s) ∩ R₃(s)`, whose forward invariance is Claim I(i).

From `hnice`, `grad_dominant_of_Qmax` (Claim I(a)) makes the gradient coordinate
at `a*(s)` dominant, `pi_mono_step` (Claim I(ii)) makes `π_t(a*(s)|s)`
nondecreasing from then on, and `g9_of_eventually_monotone` (Claim IV) turns
that into a single positive `c`. -/
theorem g9_of_eventually_nice (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A)
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (astar : S → A) (t₀ : S → ℕ)
    (hnice : ∀ s, ∀ t, t₀ s ≤ t →
      (∀ a, Qinf M (F.toPolicy (θ t)) s a ≤ Qinf M (F.toPolicy (θ t)) s (astar s)) ∧
      (∀ a, (F.toPolicy (θ t) s) a ≤ (F.toPolicy (θ t) s) (astar s))) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := by
  refine g9_of_eventually_dominant M F hF hr hγ₀ hγ₁ μ θ hstep astar t₀ ?_
  intro s t ht a
  obtain ⟨hQ, hmass⟩ := hnice s t ht
  exact grad_dominant_of_Qmax M F hF hr hγ₀ hγ₁ μ (θ t) s (astar s) hQ hmass a

end Assembled

end

end Proofs
end PolicyGradient
