/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Greedy

/-!
# AKM51b — the greedy-limit route to `Goal.softmax_ascent_converges`, assessed

Second investigation of the frozen goal `Goal.softmax_ascent_converges`, taking
up the route that the first investigation (`Proofs/AKM51.lean`) could not run:
compactness of the policy simplex, plus `Proofs.dirac_gradient_domination_eq`,
which was written after that investigation precisely to remove the full-support
obstruction.

The verdict is **not** the old one. The old obstruction ("the Łojasiewicz route
needs `hμ : ∀ s, 0 < μ s`, and the goal supplies a Dirac") is genuinely gone:
`dirac_gradient_domination_eq` expresses the suboptimality with comparator
occupancy weights and no support hypothesis at all. But the route does not
close, and the reason is different from, and sharper than, the recorded one.

This file states and proves that reason.

## Summary of what is established here

Proved, all axiom-clean:

* `sum_pi_advInf_self` — `∑ₐ π(a|s) A^π(s,a) = 0`, the Bellman identity behind
  everything below.
* `advInf_eq_zero_of_det`, `greedy_support_vacuous_at_det` — **the decisive
  finding.** At a deterministic policy the greedy-support condition
  `∀ s a, 0 < π̄(a|s) → A^{π̄}(s,a) = 0` holds *for every MDP, unconditionally*.
  So `Proofs.greedy_limit_points_reachable`, applied to a deterministic limit
  policy, yields **no information at all** — and softmax ascent produces
  deterministic limits generically, since `‖θ t‖ → ∞`.
* `vinf_eq_vstar_of_adv_nonpos` — the usable optimality criterion: if
  `A^π(s,a) ≤ 0` for **all** `s, a`, then `V^π = V*` pointwise. No support and
  no full-support hypothesis; it routes through `perfDiffInf`, not
  `mismatchCoeff`.
* `isCompact_PolySet`, `exists_subseq_tendsto_policy` — `Δ(A)^S` is compact and
  every policy sequence has a subsequence converging to a genuine `Policy S A`.
  The compactness half of the route is therefore **not** an obstruction.
* `advInf_zero_of_stationary_finite` — at a *finite* stationary point the strong
  ("all actions") condition does follow, because softmax keeps every action
  strictly positive. This localises the whole difficulty at infinity.
* `LimitAdvNonpos` + `tendsto_vstar_of_limitAdvNonpos` — the frozen goal reduces
  to one typed hypothesis: some subsequential limit policy has nonpositive
  advantage everywhere.
* `limitAdvNonpos_of_offsupport` — that hypothesis splits into the on-support
  part (which the gradient limit gives, and which is vacuous per above) and the
  **off-support part, `π̄(a|s) = 0 → A^{π̄}(s,a) ≤ 0`, which is the entire
  remaining content of AKM Theorem 5.1** and which nothing here supplies.

## On the support mismatch flagged in the task framing

The task anticipated that the fatal gap would be a mismatch between the states
`greedy_limit_points_reachable` controls (reachable under `π̄`) and the states
`dirac_gradient_domination_eq` weights (reachable under `πstar`). **That is not
where the argument dies**, and it is worth being precise about why.

`vinf_eq_vstar_of_adv_nonpos` shows the Dirac identity is not even needed: once
`A^{π̄}(s,a) ≤ 0` holds at *every* state and action, optimality follows at every
start state at once, so no occupancy weights have to be matched up. The mismatch
would only bite for an argument that tried to prove optimality *only* on `π̄`'s
reachable set and then transport it — and one does not need to.

The real obstruction is one level earlier and is about actions, not states: the
gradient limit constrains `A^{π̄}(s,a)` only where `π̄(a|s) > 0`, and by
`greedy_support_vacuous_at_det` that constraint is empty at exactly the limit
policies ascent produces. The missing fact concerns the actions softmax ascent
has *driven out* — for those, `π_t(a|s) → 0` makes the product
`d_t(s)·π_t(a|s)·A_t(s,a)` vanish for the wrong reason, and the advantage is
left unconstrained. Ruling that out requires a rate comparison between the decay
of `π_t(a|s)` and the advantage, i.e. a per-coordinate asymptotic estimate on
`θ t` itself. That is what AKM actually prove, and it remains absent.
-/

open Finset Filter

namespace PolicyGradient
namespace Proofs

section AKM51b

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ## The advantage of a policy against itself averages to zero

The Bellman equation `V^π(s) = ∑ₐ π(a|s) Q^π(s,a)` says exactly that the
`π`-average of `A^π(s,·)` vanishes at every state. This is the identity behind
everything below: the advantage is measured *relative to `π`'s own value*, so
`π` can never see itself as improvable on average. -/

/-- **`∑ₐ π(a|s) · A^π(s,a) = 0`** — a policy's own advantage averages to zero.

Immediate from the Bellman equation `Vinf_eq_rbar_add`, but worth naming: it is
the reason the greedy condition on a *support* carries no optimality
information. -/
theorem sum_pi_advInf_self (M : FiniteMDP S A) (hr : ∀ s a, |M.r s a| ≤ 1)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (s : S) :
    ∑ a, (π s) a * advInf M π s a = 0 := by
  have hbell : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  have hexp : ∀ a, (π s) a * advInf M π s a
      = (π s) a * Qinf M π s a - (π s) a * Vinf M π s := by
    intro a; rw [advInf_eq]; ring
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_sub_distrib,
    ← Finset.sum_mul, (π s).sum_eq_one, one_mul, ← hbell]
  ring


/-- **The advantage vanishes on the support of a deterministic policy — always.**

If `π` puts all its mass at `s` on a single action `a₀` (i.e. `π(a₀|s) = 1`),
then `A^π(s, a₀) = 0`, *unconditionally* — for every MDP, every such `π`, and
whether or not `π` is optimal anywhere.

This is `sum_pi_advInf_self` with a one-point average. It is the observation
that makes the greedy-limit route collapse: see `greedy_support_vacuous_at_det`.
-/
theorem advInf_eq_zero_of_det (M : FiniteMDP S A) (hr : ∀ s a, |M.r s a| ≤ 1)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (s : S) (a₀ : A)
    (hdet : (π s) a₀ = 1) :
    advInf M π s a₀ = 0 := by
  have hzero : ∀ a, a ≠ a₀ → (π s) a = 0 := by
    intro a hne
    by_contra hne0
    have hpos : 0 < (π s) a := lt_of_le_of_ne ((π s).nonneg a) (Ne.symm hne0)
    -- the total mass is 1, and `a₀` already carries all of it
    have hsub : (π s) a₀ + (π s) a ≤ ∑ b, (π s) b := by
      have := Finset.add_sum_erase (Finset.univ.erase a₀) (fun b => (π s) b)
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩)
      have hle : (π s) a ≤ ∑ b ∈ Finset.univ.erase a₀, (π s) b :=
        Finset.single_le_sum (f := fun b => (π s) b)
          (fun b _ => (π s).nonneg b) (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩)
      have hsplit : ∑ b, (π s) b
          = (π s) a₀ + ∑ b ∈ Finset.univ.erase a₀, (π s) b :=
        (Finset.add_sum_erase Finset.univ (fun b => (π s) b)
          (Finset.mem_univ a₀)).symm
      rw [hsplit]; linarith
    rw [(π s).sum_eq_one, hdet] at hsub
    linarith
  have hsum := sum_pi_advInf_self M hr hγ₀ hγ₁ π s
  have hcollapse : ∑ a, (π s) a * advInf M π s a
      = (π s) a₀ * advInf M π s a₀ := by
    refine Finset.sum_eq_single a₀ (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ a₀) h)
    rw [hzero b hb]; ring
  rw [hcollapse, hdet, one_mul] at hsum
  exact hsum

/-! ## The greedy-support condition is vacuous at deterministic policies

`Proofs.greedy_limit_points_reachable` — the corrected, proved form of
`Goal.greedy_limit_points` — concludes

  `∀ s a, 0 < dbar s → 0 < π̄(a|s) → A^{π̄}(s,a) = 0`.

The proposed route to `softmax_ascent_converges` is: extract a convergent
subsequence `π_{t_k} → π̄`, apply that theorem, and conclude `π̄` is optimal.
**That last step does not follow, and this section proves it does not.**

The reason is `advInf_eq_zero_of_det`. Softmax ascent drives logits to infinity,
so the limit policies that actually occur sit on the boundary of the simplex and
are typically deterministic. At a deterministic `π̄`, the conclusion of
`greedy_limit_points_reachable` holds **automatically, for every MDP**, with no
input from the dynamics whatsoever: the only action in the support is the one
the policy takes, and a policy's advantage against its own value is zero there
by the Bellman equation.

So the greedy condition, *restricted to the support*, has zero information
content exactly on the class of limit policies the route needs it for. -/

/-- **The conclusion of `greedy_limit_points_reachable` is vacuous at a
deterministic policy.**

For any MDP and any deterministic `π̄`, the greedy-support condition
`∀ s a, 0 < π̄(a|s) → A^{π̄}(s,a) = 0` holds — regardless of optimality, and with
no hypothesis about gradient ascent, occupancy or limits. `hdet` says `π̄` is
deterministic; the conclusion follows from the Bellman equation alone.

Consequently, obtaining this condition for a limit policy of softmax ascent
tells one **nothing** about that policy when the limit is deterministic — which
is the generic case, since `‖θ t‖ → ∞`. -/
theorem greedy_support_vacuous_at_det (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πbar : Policy S A) (act : S → A) (hdet : ∀ s, (πbar s) (act s) = 1) :
    ∀ s a, 0 < (πbar s) a → advInf M πbar s a = 0 := by
  intro s a ha
  -- in a deterministic policy, the only action with positive mass is `act s`
  have haeq : a = act s := by
    by_contra hne
    have hsub : (πbar s) (act s) + (πbar s) a ≤ ∑ b, (πbar s) b := by
      have hsplit : ∑ b, (πbar s) b
          = (πbar s) (act s) + ∑ b ∈ Finset.univ.erase (act s), (πbar s) b :=
        (Finset.add_sum_erase Finset.univ (fun b => (πbar s) b)
          (Finset.mem_univ (act s))).symm
      have hle : (πbar s) a ≤ ∑ b ∈ Finset.univ.erase (act s), (πbar s) b :=
        Finset.single_le_sum (f := fun b => (πbar s) b)
          (fun b _ => (πbar s).nonneg b)
          (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩)
      rw [hsplit]; linarith
    rw [(πbar s).sum_eq_one, hdet s] at hsub
    linarith
  subst haeq
  exact advInf_eq_zero_of_det M hr hγ₀ hγ₁ πbar s (act s) (hdet s)


/-! ## What the greedy condition must say instead: ALL actions

`advInf_eq_zero_of_det` shows the support-restricted condition is empty at a
deterministic policy. The condition with content quantifies over **every**
action:

  `∀ a, advInf M πbar s a ≤ 0`   (equivalently `= 0` is too strong; `≤ 0` is
                                  what optimality needs and what holds)

and that *is* Bellman optimality at `s`. This section proves the two directions
that make it usable, so that the remaining gap is isolated as one statement
about the dynamics rather than a vague "the route fails".

Note the finite-parameter picture, which explains why this is the right form.
At any **finite** `θ`, softmax gives `π_θ(a|s) > 0` for every `a`
(`Proofs.softmax_pos`). So a stationary point of the ascent at a reachable
state has `d(s)·π(a|s)·A(s,a) = 0` with `π(a|s) > 0`, forcing `A(s,a) = 0` for
*all* `a` — genuine Bellman optimality. The whole difficulty of AKM 5.1 is that
the trajectory does not reach a finite stationary point: `‖θ t‖ → ∞`, and in the
limit the positive factor `π(a|s)` degenerates precisely at the actions where
the information was carried. -/

/-- **Nonpositive advantage everywhere at a state ⟹ that state's value is
optimal**, given the same at every state.

If `A^π(s,a) ≤ 0` for every `s` and `a`, then `V^π = V*` pointwise: `π` solves
the Bellman optimality equation, so it is optimal. This is the form the limit
argument needs, and it is exactly what the support-restricted greedy condition
fails to deliver.

Proved by comparing with the greedy policy through `perfDiffInf`: the
performance difference of any comparator `π'` against `π` is an occupancy-
weighted average of `A^π`, hence `≤ 0`. -/
theorem vinf_eq_vstar_of_adv_nonpos (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (hadv : ∀ s a, advInf M π s a ≤ 0) (s₀ : S) :
    Vinf M π s₀ = Vstar M s₀ := by
  refine le_antisymm (vstar_upper_proof M hr hγ₀ hγ₁ π s₀) ?_
  -- `Vstar` is attained by the greedy policy; compare it against `π`.
  rw [← vstar_eq_greedy M hr hγ₀ hγ₁ s₀]
  -- performance difference: `V^g - V^π = ∑ₛ d^g(s₀,s) ∑ₐ g(a|s) A^π(s,a) ≤ 0`
  have hpd := perfDiffInf M π (greedyPolicy M) hr hγ₀ hγ₁ s₀
  have hle : pdInf M π (greedyPolicy M) s₀ ≤ 0 := by
    unfold pdInf
    refine Finset.sum_nonpos fun s _ => ?_
    have hd : 0 ≤ dinf M (greedyPolicy M) s₀ s := dinf_nonneg M hγ₀ _ _ _
    have hgap : advGapInf M π (greedyPolicy M) s ≤ 0 := by
      unfold advGapInf
      exact Finset.sum_nonpos fun a _ =>
        mul_nonpos_of_nonneg_of_nonpos ((greedyPolicy M s).nonneg a) (hadv s a)
    exact mul_nonpos_of_nonneg_of_nonpos hd hgap
  linarith [hpd, hle]


/-! ## At a FINITE stationary point the argument works

This makes the previous section's claim concrete, and shows the difficulty is
located exactly at infinity rather than in the algebra.

At a finite parameter `θ`, softmax positivity (`Proofs.softmax_pos`) gives
`π_θ(a|s) > 0` for **every** action. So if every gradient coordinate at `θ`
vanishes and the state `s` is reached (`0 < dinfDist`), then `A(s,a) = 0` for
all `a` at that state — the strong condition, not the vacuous one. -/

/-- **A reached state at a finite stationary point has all advantages zero.**

`hstat` is the vanishing of the `(s,a)` gradient coordinate, in the form
`Proofs.dVinfDist_single` computes it. Because softmax keeps every action
strictly positive at finite `θ`, the conclusion is for **all** `a`, not merely
those in a support — contrast `greedy_support_vacuous_at_det`. -/
theorem advInf_zero_of_stationary_finite (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (μ : Dist S) (θ : E S A) (s : S)
    (hd : 0 < dinfDist M (F.toPolicy θ) μ s)
    (hstat : ∀ a, dinfDist M (F.toPolicy θ) μ s
      * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) = 0)
    (a : A) :
    advInf M (F.toPolicy θ) s a = 0 := by
  have hpi : 0 < (F.toPolicy θ s) a := by
    rw [hF θ s a]; exact softmax_pos _ a
  have h := hstat a
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 (ne_of_gt hd)
  · rcases mul_eq_zero.mp h2 with h3 | h4
    · exact absurd h3 (ne_of_gt hpi)
    · exact h4

/-! ## The reduction: one hypothesis closes the frozen goal

Everything above says what a proof must supply. This section says it exactly,
as a typed statement, and proves that it suffices.

`LimitAdvNonpos` is the missing ingredient: *some* limit policy of the
trajectory has nonpositive advantage at every state and action. Given it, the
frozen goal follows — with **no** full-support hypothesis on the start state,
because `vinf_eq_vstar_of_adv_nonpos` routes through `perfDiffInf` rather than
through `mismatchCoeff`.

This is strictly weaker than what `Goal.greedy_limit_points` asked for and
strictly stronger than what `greedy_limit_points_reachable` delivers, and the
gap between the two is precisely the content of AKM Theorem 5.1. -/

/-- **The missing ingredient of AKM 5.1, isolated as a typed statement.**

Along the frozen trajectory, some policy `πbar` is a limit of the policy
sequence and has nonpositive advantage at every state–action pair.

The second conjunct is the real content: by `greedy_support_vacuous_at_det` the
support-restricted version is vacuous at the deterministic limits that softmax
ascent actually produces, so the quantifier must range over **all** actions. -/
abbrev LimitAdvNonpos (M : FiniteMDP S A) (F : VecPolicy S A (E S A))
    (θ : ℕ → E S A) : Prop :=
  ∃ πbar : Policy S A,
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k s a => (F.toPolicy (θ (φ k)) s) a) atTop
        (nhds (fun s a => (πbar s) a))) ∧
    (∀ s a, advInf M πbar s a ≤ 0)

/-- **The reduction.** `LimitAdvNonpos` closes the frozen goal.

Given a subsequential limit policy with nonpositive advantages everywhere:

* `vinf_eq_vstar_of_adv_nonpos` gives `V^{π̄}(μ) = V*(μ)` — no support
  hypothesis needed anywhere;
* `tendsto_Vinf_of_tendsto_policy` transfers the subsequence's values to
  `V^{π̄}(μ)`;
* the whole value sequence converges (`exists_limit_le_vstar`), so its limit
  agrees with that of any subsequence.

Hence the limit is `Vstar M μ`, which is the frozen conclusion. -/
theorem tendsto_vstar_of_limitAdvNonpos {M : FiniteMDP S A}
    (F : VecPolicy S A (E S A))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A) (htraj : AscentTraj M F μ θ) (hasc : VecAscent M F μ)
    (hlan : LimitAdvNonpos M F θ) :
    Tendsto (fun t => Vinf M (F.toPolicy (θ t)) μ) atTop (nhds (Vstar M μ)) := by
  obtain ⟨πbar, ⟨φ, hφ, hlim⟩, hadv⟩ := hlan
  -- the whole sequence converges to some `L`
  obtain ⟨L, hLle, hL⟩ := exists_limit_le_vstar (M := M) F hr hγ₀ hγ₁ μ θ htraj hasc
  -- along the subsequence the values converge to `V^{π̄}(μ)`
  have hsub : Tendsto (fun k => Vinf M (F.toPolicy (θ (φ k))) μ) atTop
      (nhds (Vinf M πbar μ)) :=
    tendsto_Vinf_of_tendsto_policy M hr hγ₀ hγ₁
      (fun k => F.toPolicy (θ (φ k))) πbar hlim μ
  -- but the subsequence of a convergent sequence converges to the same limit
  have hsub' : Tendsto (fun k => Vinf M (F.toPolicy (θ (φ k))) μ) atTop (nhds L) :=
    hL.comp hφ.tendsto_atTop
  have hLeq : L = Vinf M πbar μ := tendsto_nhds_unique hsub' hsub
  have hopt : Vinf M πbar μ = Vstar M μ :=
    vinf_eq_vstar_of_adv_nonpos M hr hγ₀ hγ₁ πbar hadv μ
  rw [hLeq, hopt] at hL
  exact hL


/-! ## Compactness of the policy simplex, and the subsequence it yields

The task framing asks whether `Δ(A)^S` is compact and whether a convergent
subsequence of policies can be extracted. It is, and it can — proved here
unconditionally. This matters for locating the gap: the compactness half of the
proposed route is **not** the obstruction, so the obstruction is entirely in the
advantage condition. -/

/-- The coordinate arrays of policies: the product of simplices `Δ(A)^S`. -/
def PolySet (S A : Type*) [Fintype A] : Set (S → A → ℝ) :=
  {f | (∀ s a, 0 ≤ f s a) ∧ ∀ s, ∑ a, f s a = 1}

theorem policy_mem_PolySet (π : Policy S A) :
    (fun s a => (π s) a) ∈ PolySet S A :=
  ⟨fun s a => (π s).nonneg a, fun s => (π s).sum_eq_one⟩

/-- **`Δ(A)^S` is compact.**

A closed subset of the compact box `[0,1]^{S×A}`: nonnegativity and the
sum-to-one constraints are each closed conditions, and the simplex sits inside
the box because each coordinate is bounded by the total mass `1`. -/
theorem isCompact_PolySet : IsCompact (PolySet S A) := by
  have hbox : IsCompact
      {f : S → A → ℝ | ∀ s, f s ∈ {g : A → ℝ | ∀ a, g a ∈ Set.Icc (0:ℝ) 1}} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed (⋂ (s : S), ⋂ (a : A), {f : S → A → ℝ | 0 ≤ f s a}) :=
      isClosed_iInter fun s => isClosed_iInter fun a =>
        isClosed_le continuous_const ((continuous_apply a).comp (continuous_apply s))
    have h2 : IsClosed (⋂ (s : S), {f : S → A → ℝ | ∑ a, f s a = 1}) :=
      isClosed_iInter fun s => isClosed_eq
        (continuous_finsetSum _ (fun a _ => (continuous_apply a).comp (continuous_apply s)))
        continuous_const
    have heq : PolySet S A
        = (⋂ (s : S), ⋂ (a : A), {f : S → A → ℝ | 0 ≤ f s a})
          ∩ (⋂ (s : S), {f : S → A → ℝ | ∑ a, f s a = 1}) := by
      ext f; simp [PolySet, Set.mem_iInter]
    rw [heq]; exact h1.inter h2
  · rintro f ⟨hnn, hsum⟩ s a
    refine ⟨hnn s a, ?_⟩
    have hle : f s a ≤ ∑ b, f s b :=
      Finset.single_le_sum (f := fun b => f s b) (fun b _ => hnn s b) (Finset.mem_univ a)
    rw [hsum s] at hle; exact hle

/-- **Every policy sequence has a convergent subsequence, with a policy limit.**

Bolzano–Weierstrass in `Δ(A)^S`. The limit is repackaged as a genuine
`Policy S A`, so it can be fed to `tendsto_Vinf_of_tendsto_policy` and
`vinf_eq_vstar_of_adv_nonpos`.

This discharges the compactness half of the AKM 5.1 route unconditionally. -/
theorem exists_subseq_tendsto_policy (π : ℕ → Policy S A) :
    ∃ (πbar : Policy S A) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k s a => (π (φ k) s) a) atTop (nhds (fun s a => (πbar s) a)) := by
  obtain ⟨f, hf, φ, hφ, hconv⟩ :=
    isCompact_PolySet.tendsto_subseq (x := fun t s a => (π t s) a)
      (fun t => policy_mem_PolySet (π t))
  obtain ⟨hnn, hsum⟩ := hf
  refine ⟨fun s => ⟨f s, hnn s, hsum s⟩, φ, hφ, hconv⟩


/-! ## Exactly what remains

Assembling: `exists_subseq_tendsto_policy` supplies the subsequence and the
limit policy `π̄`; `tendsto_Vinf_of_tendsto_policy` transfers the values;
`vinf_eq_vstar_of_adv_nonpos` converts an advantage condition into optimality;
`tendsto_vstar_of_limitAdvNonpos` closes the frozen goal. The single unproved
link is:

  **at a limit policy `π̄` of softmax ascent, `A^{π̄}(s,a) ≤ 0` for every `a`.**

The gradient limit gives this only where `π̄(a|s) > 0`:
`d_t(s)·π_t(a|s)·A_t(s,a) → 0` with all three factors convergent forces
`A^{π̄}(s,a) = 0` when the first two limits are positive. At an action with
`π̄(a|s) = 0` — an action softmax ascent has driven out — the product vanishes in
the limit for the *wrong reason*, and `A^{π̄}(s,a)` is unconstrained by it.

`greedy_limit_points_reachable` is precisely the first case, and
`greedy_support_vacuous_at_det` shows the first case is empty of content when
`π̄` is deterministic, which is the generic outcome of ascent. So the frozen goal
needs the second case, and nothing in the repo — or in the gradient limit alone
— supplies it.

The lemma below records the first case in the form the reduction consumes,
making explicit that it covers only the support. -/

/-- **What the gradient limit gives: nonpositive advantage on the support only.**

At an action the limit policy still plays, the greedy condition upgrades to the
`≤ 0` form `vinf_eq_vstar_of_adv_nonpos` wants. Off the support it gives
nothing, and `hoff` is exactly the hypothesis that cannot be discharged — it is
the residue of AKM Theorem 5.1.

Stated so that a future proof of `hoff` composes immediately: with it,
`LimitAdvNonpos` and hence the frozen goal follow. -/
theorem limitAdvNonpos_of_offsupport (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πbar : Policy S A)
    (hsupp : ∀ s a, 0 < (πbar s) a → advInf M πbar s a = 0)
    (hoff : ∀ s a, (πbar s) a = 0 → advInf M πbar s a ≤ 0) :
    ∀ s a, advInf M πbar s a ≤ 0 := by
  intro s a
  rcases eq_or_lt_of_le ((πbar s).nonneg a) with h | h
  · exact hoff s a h.symm
  · exact le_of_eq (hsupp s a h)

end AKM51b

end Proofs
end PolicyGradient

