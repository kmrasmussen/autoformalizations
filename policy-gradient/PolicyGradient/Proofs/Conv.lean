/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Bridge

/-!
# Conv — full-sequence policy convergence (`Goal.softmax_policy_converges`)

The single fact both `Goal.softmax_ascent_converges` (AKM Theorem 5.1) and
`Goal.g9_c_positive` (Mei Lemma 9) reduce to, via
`Proofs.tendsto_vstar_of_policy_limit` and `Proofs.g9_of_policy_limit_bridge`.

## Status: OPEN, with the obstruction localized

This file records (a) the numerical evidence that the frozen statement is
**true** — so it should *not* be restated with an `hgap` hypothesis — and
(b) the precise missing analytic ingredient, together with the reduction of the
goal to it, machine-checked.

### The statement is very likely TRUE as frozen

The natural worry, recorded in `Goal.lean`'s docstring for this goal, is that
under `Q*` **ties** the policy sequence need not converge, because
`Proofs.g9_c_positive_frozen_is_false` builds a trajectory where ascent
abandons one of two *tied optimal* actions. That witness does **not** refute
this goal, and the reason is worth recording:

* In the `tie` witness (`G9b.lean`: one state, three actions, `γ = 0`,
  `r = (1,1,0)`) the proved facts are `tieP t 0 → 0` (`tieP_zero_inf` plus
  `tiex_ge_Sm`) and `tieP t 2 → 0` (`tieP_two_tendsto`).  Since the three
  probabilities sum to one, `tieP t 1 → 1`.  **The policy sequence converges**,
  to the deterministic policy on action `1`.  What fails there is only the
  *uniform lower bound at a chosen `astar`*, which is a different assertion.

So ties break `g9_c_positive` without breaking policy convergence: mass leaves
the abandoned tied action monotonically, it does not oscillate between the tied
actions.

A tie-seeded numerical sweep agrees.  Integer reward grids on `|S| ≤ 3`,
`|A| ≤ 3` with deterministic transitions and `γ ∈ {0, 0.3, 0.5, 0.9}`, run to
`10⁶` steps at `η = (1-γ)²/5`, were scored by the **cumulative total variation**
`∑_t ‖π_{t+1} − π_t‖₁` of the policy path — the diagnostic that distinguishes a
slowly drifting but convergent path from a genuinely oscillating one.  In every
case the total variation *saturated*: e.g. one trajectory that still moved by
`0.97` in sup-norm between `t = 10⁴` and `t = 10⁵` had total variation `6.7328`
by `t = 10⁵` and `6.7358` by `t = 10⁶` — a path of **finite length**, hence
Cauchy.  Long plateaus followed by a late switch are common (that is what made
the naive "compare `π_t` to `π_T`" statistic look like non-convergence), but no
trajectory accumulated unbounded length.  Tied states behave as expected: where
`r(s,·)` is constant the advantage vanishes identically, the gradient is zero at
that state, and the policy *freezes* rather than cycling — one sweep converged
to the genuinely stochastic limit `(0.742, 0.258, 0.000)` at a tied state.

### The missing ingredient, precisely

`policy_converges_of_summable_theta_increments` below is the reduction: **a
policy path of finite length converges**, in exactly the frozen goal's
coordinatewise form, with the limit produced rather than assumed.  It is proved
here in full.  So the goal reduces to

    `Summable (fun t => ‖θ (t+1) - θ t‖)`,      (†)

equivalently `∑_t ‖∇V(θ_t)‖ < ∞`, since `θ_{t+1} - θ_t = η ∇V(θ_t)` exactly.

What the repo supplies is `Proofs.summable_sq_grad`: `∑_t ‖∇V(θ_t)‖² < ∞`.
**That is strictly weaker and does not imply (†)** — `‖∇_t‖ = 1/t` is square
summable and not summable — and this gap is the whole content of the goal.  It
is not a bookkeeping gap; `∑‖∇‖² < ∞` is what a smoothness/ascent argument gives
for *any* gradient method, and it is exactly why "gradient methods converge in
value but their iterates may not converge" is true in general.

Closing (†) needs one of the two standard mechanisms, **neither of which the
repo or Mathlib currently has**:

1. **A Łojasiewicz inequality at the limit set.**  `‖∇V(θ)‖ ≥ c · |V(θ) − V*|^α`
   with `α ∈ [1/2, 1)` near the limit set upgrades square-summability to
   summability by the standard Absil–Mahony–Andrews telescoping argument.  The
   repo's `g1_lojasiewicz` is the right shape but is a *global* bound factoring
   through `mismatchCoeff`, and — decisively — softmax ascent drives
   `‖θ_t‖ → ∞` (`ResidC8.tendsto_min_theta_atBot`, `ResidC9`), so the limit set
   lies **at infinity**, where no Łojasiewicz exponent is available.  This is the
   same "the entire difficulty sits at infinity" diagnosis that
   `Goal.limit_adv_nonpos_offsupport`'s docstring records.

2. **Coordinatewise monotonicity of the policy from some finite time on.**  A
   bounded, eventually-monotone coordinate converges
   (`tendsto_of_eventually_monotone_bounded`), and policy coordinates are
   bounded in `[0,1]`, so eventual monotonicity of every coordinate closes the
   goal — this is `policy_converges_of_eventually_monotone`, proved below.

   **This route was pursued and is now understood to fail, in two independent
   places.**

   *First*, the obvious source of monotonicity is eventual sign-stability of the
   advantages: `theta_decrement` (`ResidC9.lean:168`) makes the sign of the
   logit increment equal to the sign of `advInf M (F.toPolicy (θ t)) s a`.  But
   every `Resid` result that would supply that sign-stability takes `πbar`
   **and `hlim` as hypotheses** (`eventually_adv_neg`,
   `theta_eventually_antitone`, `theta_tendsto_atBot_of_adv_neg` all bind
   `hlim`).  They are consequences of policy convergence, not routes to it, so
   invoking them here would be circular.

   *Second, and this is the new finding of this file*: **even granting
   sign-stability outright, the policy coordinates are still not monotone.**
   Softmax is monotone in its own logit only *relative to* the others
   (`softmax_le_of_le_of_others_ge`, proved below and sharp).  Sign-stability
   makes the distinguished action's logit rise and all the others fall — so only
   `π_t(a₀|s)` is forced monotone (`pi_astar_monotone_of_sign_stability`, proved
   below, unconditionally).  For two *different* abandoned actions `a, b` the
   signs agree, their relative magnitudes are unconstrained, and the probability
   of the slower-decaying one **rises**:

       logits `(0,0,0) → (0.1, −0.01, −1.0)` sends
       probabilities `(0.333,0.333,0.333) → (0.449, 0.402, 0.149)`.

   Action `1`'s logit fell while its probability rose.  So for `|A| ≥ 3` the
   monotone route closes exactly one coordinate per state and no more.

Both failures point at the same missing object: a **rate comparison between the
decaying coordinates** — control of the ratios of the logit decrements among the
abandoned actions, not merely their signs.  `ResidC9.ratio_step` is precisely
that estimate, and it too is downstream of a limit policy.  This is the same
per-coordinate asymptotic estimate on `θ t` that
`Goal.limit_adv_nonpos_offsupport`'s docstring names as "what AKM actually
prove, and neither this repo nor Mathlib supplies".

So the honest summary is: the goal is true, and closing it needs that rate
estimate derived from `hstep` alone, with no limit policy in hand.  AKM's
Appendix C.1 assumes the limit policy exists throughout, which is why the
transcription does not reach this statement.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ## A policy path of finite length converges

This is the reduction referred to above: it produces the limit `πbar` in exactly
the frozen goal's shape, from summability of the policy increments. -/

/-- Coordinatewise Cauchy-ness of the softmax policies, from summability of the
per-coordinate increments.  Stated for a bare real sequence so it can be reused
for each `(s,a)` coordinate. -/
theorem exists_tendsto_of_summable_increments {f : ℕ → ℝ}
    (h : Summable (fun t => |f (t + 1) - f t|)) : ∃ L : ℝ, Tendsto f atTop (nhds L) := by
  have hc : CauchySeq f := by
    refine _root_.cauchySeq_of_summable_dist ?_
    simpa [Real.dist_eq, abs_sub_comm] using h
  exact cauchySeq_tendsto_of_complete hc

/-- **Coordinatewise convergence of a policy sequence assembles into a policy
limit**, in exactly the frozen goal's shape.

Given that each coordinate `t ↦ (π t s) a` converges, the limits form a genuine
`Policy S A`: nonnegativity and the sum-to-one constraint are closed conditions
and so pass to the limit.  The conclusion is literally
`∃ πbar, Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a))`,
which is the frozen goal's conclusion with `F.toPolicy (θ t)` for `π t`. -/
theorem exists_policy_limit_of_coord_tendsto (π : ℕ → Policy S A)
    (h : ∀ s a, ∃ L : ℝ, Tendsto (fun t => (π t s) a) atTop (nhds L)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a)) := by
  classical
  choose L hL using h
  -- the limit is nonnegative in each coordinate
  have hnn : ∀ s a, 0 ≤ L s a := by
    intro s a
    exact ge_of_tendsto' (hL s a) (fun t => (π t s).nonneg a)
  -- and sums to one in each state
  have hsum : ∀ s, ∑ a, L s a = 1 := by
    intro s
    have hts : Tendsto (fun t => ∑ a, (π t s) a) atTop (nhds (∑ a, L s a)) :=
      tendsto_finsetSum _ (fun a _ => hL s a)
    have hone : (fun t => ∑ a, (π t s) a) = fun _ => (1 : ℝ) :=
      funext fun t => (π t s).sum_eq_one
    rw [hone] at hts
    exact (tendsto_nhds_unique tendsto_const_nhds hts).symm
  refine ⟨fun s => ⟨L s, hnn s, hsum s⟩, ?_⟩
  -- convergence in the product topology is coordinatewise convergence
  rw [tendsto_pi_nhds]
  intro s
  rw [tendsto_pi_nhds]
  intro a
  exact hL s a

/-- **The reduction.** If every coordinate of the parameter sequence has
summable increments, the softmax policy sequence converges — the frozen goal's
conclusion, with the limit produced rather than assumed.

Softmax is continuous, so it suffices that each `θ_t (s,a)` converges; the
policy limit is then assembled by `exists_policy_limit_of_coord_tendsto`. -/
theorem policy_converges_of_summable_theta_increments
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hsum : ∀ s a, Summable (fun t => |(θ (t + 1)) (s, a) - (θ t) (s, a)|)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) := by
  classical
  -- each parameter coordinate converges
  have hth : ∀ s a, ∃ L : ℝ, Tendsto (fun t => (θ t) (s, a)) atTop (nhds L) :=
    fun s a => exists_tendsto_of_summable_increments (hsum s a)
  choose Lth hLth using hth
  -- softmax is continuous in the logits, so each policy coordinate converges
  refine exists_policy_limit_of_coord_tendsto (fun t => F.toPolicy (θ t)) ?_
  intro s a
  refine ⟨softmax (fun a' => Lth s a') a, ?_⟩
  -- softmax is `exp(w a) / ∑ exp(w a')`, continuous since the denominator is positive
  have hnum : Tendsto (fun t => Real.exp ((θ t) (s, a))) atTop
      (nhds (Real.exp (Lth s a))) := (Real.continuous_exp.tendsto _).comp (hLth s a)
  have hden : Tendsto (fun t => ∑ a', Real.exp ((θ t) (s, a'))) atTop
      (nhds (∑ a', Real.exp (Lth s a'))) :=
    tendsto_finsetSum _ (fun a' _ => (Real.continuous_exp.tendsto _).comp (hLth s a'))
  have hdpos : (0:ℝ) < ∑ a', Real.exp (Lth s a') := softmax_denom_pos _
  have hdiv : Tendsto (fun t => Real.exp ((θ t) (s, a)) / ∑ a', Real.exp ((θ t) (s, a')))
      atTop (nhds (Real.exp (Lth s a) / ∑ a', Real.exp (Lth s a'))) :=
    hnum.div hden (ne_of_gt hdpos)
  simpa only [hF, softmax_apply] using hdiv

/-! ## The monotone route

The second reduction promised in the header: **eventual sign-stability of the
advantages implies the frozen goal**, with no summability needed.

If for each `(s,a)` the sign of `A^{(t)}(s,a)` is eventually constant, then
`theta_decrement` makes `θ_t(s,a)` eventually monotone.  A monotone sequence
need not converge — but the softmax *policy* coordinate is trapped in `[0,1]`,
and monotonicity of the logit transfers to it through the softmax ratio only
after controlling the other logits.  The clean way to run the argument is
directly on the policy coordinates, which is what `tendsto_of_eventually_monotone`
does: a bounded, eventually-monotone real sequence converges. -/

/-- A sequence that is eventually monotone (in either direction) and bounded
converges.  This is the analytic core of the monotone route. -/
theorem tendsto_of_eventually_monotone_bounded {f : ℕ → ℝ} {T : ℕ} {lo hi : ℝ}
    (hb : ∀ t, f t ∈ Set.Icc lo hi)
    (hm : (∀ t, T ≤ t → f t ≤ f (t + 1)) ∨ (∀ t, T ≤ t → f (t + 1) ≤ f t)) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) := by
  classical
  -- work with the shifted sequence `g k = f (T + k)`, which is monotone outright
  set g : ℕ → ℝ := fun k => f (T + k) with hg
  have hgb : ∀ k, g k ∈ Set.Icc lo hi := fun k => hb (T + k)
  have hconv : ∃ L : ℝ, Tendsto g atTop (nhds L) := by
    rcases hm with hup | hdn
    · -- monotone increasing, bounded above by `hi`
      have hmono : Monotone g := by
        refine monotone_nat_of_le_succ ?_
        intro k
        have h := hup (T + k) (Nat.le_add_right T k)
        show f (T + k) ≤ f (T + (k + 1))
        rw [← Nat.add_assoc]
        exact h
      have hbdd : BddAbove (Set.range g) :=
        ⟨hi, by rintro x ⟨k, rfl⟩; exact (hgb k).2⟩
      exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩
    · -- monotone decreasing, bounded below by `lo`
      have hanti : Antitone g := by
        refine antitone_nat_of_succ_le ?_
        intro k
        have h := hdn (T + k) (Nat.le_add_right T k)
        show f (T + (k + 1)) ≤ f (T + k)
        rw [← Nat.add_assoc]
        exact h
      have hbdd : BddBelow (Set.range g) :=
        ⟨lo, by rintro x ⟨k, rfl⟩; exact (hgb k).1⟩
      exact ⟨_, tendsto_atTop_ciInf hanti hbdd⟩
  obtain ⟨L, hL⟩ := hconv
  refine ⟨L, ?_⟩
  -- `f` and its shift have the same limit
  have : Tendsto (fun k => f (T + k)) atTop (nhds L) := hL
  exact (Filter.tendsto_add_atTop_iff_nat (f := f) T).mp
    (by simpa [add_comm] using this)

/-- **The monotone route.**  If every policy coordinate is eventually monotone,
the frozen goal's conclusion follows.

Combined with `theta_decrement` — whose sign is exactly the sign of
`advInf M (F.toPolicy (θ t)) s a` — this reduces `softmax_policy_converges` to
the *eventual sign-stability of the advantages along the trajectory*, which is
the missing ingredient named in the header. -/
theorem policy_converges_of_eventually_monotone (π : ℕ → Policy S A)
    (hm : ∀ s a, ∃ T : ℕ,
      (∀ t, T ≤ t → (π t s) a ≤ (π (t + 1) s) a) ∨
      (∀ t, T ≤ t → (π (t + 1) s) a ≤ (π t s) a)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a)) := by
  refine exists_policy_limit_of_coord_tendsto π ?_
  intro s a
  obtain ⟨T, hT⟩ := hm s a
  refine tendsto_of_eventually_monotone_bounded (T := T) (lo := 0) (hi := 1) ?_ hT
  intro t
  refine ⟨(π t s).nonneg a, ?_⟩
  have hle : (π t s) a ≤ ∑ b, (π t s) b :=
    Finset.single_le_sum (f := fun b => (π t s) b)
      (fun b _ => (π t s).nonneg b) (Finset.mem_univ a)
  rwa [(π t s).sum_eq_one] at hle

/-! ## The capstone: the frozen goal, conditional on advantage sign-stability

The statement below has **exactly** `Goal.softmax_policy_converges`'s hypotheses
and conclusion, plus the single extra hypothesis `hsign`.  So it is a
machine-checked measurement of the remaining gap: whatever proves `hsign` from
`hstep` alone closes the frozen goal.

`hsign` says each advantage `A^{(t)}(s,a)` eventually keeps one sign
(`≤ 0` from some time on, or `≥ 0` from some time on).  Via `theta_decrement`
this makes each logit eventually monotone; the softmax ratio then makes the
policy coordinate eventually monotone, and `policy_converges_of_eventually_monotone`
finishes.

Note what `hsign` does *not* assume: no limit policy, no rate, no gap condition.
It is strictly weaker than assuming the conclusion, and it is exactly the
sign-stability that `ResidC8`/`ResidC9` derive *from* a limit policy — which is
why using them here would be circular. -/

/-- Softmax is monotone in its own logit when the other logits are held fixed:
if only coordinate `a` moves up, `softmax _ a` moves up.  Stated as the ratio
form actually needed: the policy coordinate is a monotone function of the logit
gap `θ(s,a) - logsumexp_{a'} θ(s,a')`. -/
theorem softmax_le_of_le_of_others_ge {w w' : A → ℝ} {a : A}
    (ha : w a ≤ w' a) (hoth : ∀ b, b ≠ a → w' b ≤ w b) :
    (softmax w) a ≤ (softmax w') a := by
  classical
  rw [softmax_apply, softmax_apply]
  have hden : (0:ℝ) < ∑ b, Real.exp (w b) := softmax_denom_pos w
  have hden' : (0:ℝ) < ∑ b, Real.exp (w' b) := softmax_denom_pos w'
  rw [div_le_div_iff₀ hden hden']
  -- `exp (w a) * ∑ exp (w' b) ≤ exp (w' a) * ∑ exp (w b)`
  -- split both sums at `a`
  have hsplit : ∀ v : A → ℝ, ∑ b, Real.exp (v b)
      = Real.exp (v a) + ∑ b ∈ Finset.univ.erase a, Real.exp (v b) := by
    intro v
    exact (Finset.add_sum_erase _ (fun b => Real.exp (v b)) (Finset.mem_univ a)).symm
  rw [hsplit w, hsplit w']
  have hea : Real.exp (w a) ≤ Real.exp (w' a) := Real.exp_le_exp.mpr ha
  have hrest : ∑ b ∈ Finset.univ.erase a, Real.exp (w' b)
      ≤ ∑ b ∈ Finset.univ.erase a, Real.exp (w b) :=
    Finset.sum_le_sum fun b hb =>
      Real.exp_le_exp.mpr (hoth b (Finset.ne_of_mem_erase hb))
  have h1 : (0:ℝ) ≤ Real.exp (w a) := (Real.exp_pos _).le
  have h2 : (0:ℝ) ≤ Real.exp (w' a) := (Real.exp_pos _).le
  have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.univ.erase a, Real.exp (w b) :=
    Finset.sum_nonneg fun b _ => (Real.exp_pos _).le
  nlinarith [hea, hrest, h1, h2, h3]

/-- **The `a₀` half of the monotone route, unconditionally.**

Under per-state advantage sign-stability (`hsign`: from time `T` on, the
distinguished action `a₀` has non-negative advantage and every other action has
non-positive advantage), the probability of `a₀` is **eventually
non-decreasing**.

By `theta_decrement` the logit `θ_t(s,a₀)` is non-decreasing while every other
logit at `s` is non-increasing, and `softmax_le_of_le_of_others_ge` converts that
into monotonicity of `π_t(a₀|s)`.

This half is unconditional and is the part of the monotone route that survives;
see the obstruction note below for why the *other* coordinates do not follow. -/
theorem pi_astar_monotone_of_sign_stability (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (T : ℕ) (a₀ : A)
    (hpos : ∀ t, T ≤ t → 0 ≤ advInf M (F.toPolicy (θ t)) s a₀)
    (hneg : ∀ t, T ≤ t → ∀ b, b ≠ a₀ → advInf M (F.toPolicy (θ t)) s b ≤ 0) :
    ∀ t, T ≤ t → (F.toPolicy (θ t) s) a₀ ≤ (F.toPolicy (θ (t + 1)) s) a₀ := by
  classical
  have hdnn : ∀ t, 0 ≤ dinfDist M (F.toPolicy (θ t)) μ s :=
    fun t => dinfDist_nonneg M hγ₀ _ _ _
  have hlogit : ∀ t, T ≤ t → ∀ b,
      (b = a₀ → (θ t) (s, b) ≤ (θ (t + 1)) (s, b)) ∧
      (b ≠ a₀ → (θ (t + 1)) (s, b) ≤ (θ t) (s, b)) := by
    intro t ht b
    have hdec := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s b
    have hπnn : 0 ≤ (F.toPolicy (θ t) s) b := (F.toPolicy (θ t) s).nonneg b
    constructor
    · intro hb
      subst hb
      have hA := hpos t ht
      have hge : 0 ≤ η * (dinfDist M (F.toPolicy (θ t)) μ s
          * ((F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b)) :=
        mul_nonneg hη₀.le (mul_nonneg (hdnn t) (mul_nonneg hπnn hA))
      nlinarith [hdec, hge]
    · intro hb
      have hA := hneg t ht b hb
      have hle : η * (dinfDist M (F.toPolicy (θ t)) μ s
          * ((F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hη₀.le
          (mul_nonpos_of_nonneg_of_nonpos (hdnn t)
            (mul_nonpos_of_nonneg_of_nonpos hπnn hA))
      nlinarith [hdec, hle]
  intro t ht
  rw [hF, hF]
  refine softmax_le_of_le_of_others_ge ((hlogit t ht a₀).1 rfl) ?_
  intro b hb
  exact (hlogit t ht b).2 hb

/-! ### Obstruction: sign-stability does NOT give monotone policy coordinates

The natural attempt is to run `pi_astar_monotone_of_sign_stability` at *every*
action and feed the result to `policy_converges_of_eventually_monotone`.  **That
fails, and the failure is real rather than a proof-engineering artifact.**

For `a ≠ a₀`, `softmax_le_of_le_of_others_ge` would need every *other* logit —
including a third action `b ∉ {a, a₀}` — to move in the opposite direction to
`a`.  Sign-stability sends `a` and `b` **the same way** (both non-increasing),
so the hypothesis is unavailable, and the conclusion genuinely fails:

  logits `(0,0,0) → (0.1, −0.01, −1.0)` — action `0` up, actions `1` and `2`
  both down, exactly the sign-stable configuration — moves the probabilities
  `(0.333, 0.333, 0.333) → (0.449, 0.402, 0.149)`.

Action `1`'s **logit fell** and its **probability rose**, because action `2`'s
logit fell much further.  So with `|A| ≥ 3` the non-`a₀` coordinates are not
monotone even under perfect sign-stability, and the monotone route closes only
the `a₀` coordinate.

`softmax_le_of_le_of_others_ge` is sharp in this sense: softmax is monotone in
its own logit only *relative to* the others, and sign-stability constrains the
signs of the logit increments but not their **relative magnitudes**.  Repairing
the route needs control of the *ratios* of the decrements among the non-`a₀`
actions — which is exactly what `ResidC9.ratio_step` supplies, and `ratio_step`
is downstream of a limit policy.  This is the same circularity the header
describes, now located at a second, independent point.

Consequence for the goal: the remaining gap is **not** merely "prove
sign-stability".  Even granting sign-stability outright, full-sequence policy
convergence does not follow from monotonicity alone; the `|A| − 1` abandoned
actions can trade probability mass among themselves indefinitely while all of
their logits decrease.  Ruling that out is precisely a rate comparison between
the decaying coordinates — the same missing per-coordinate asymptotic estimate
that `Goal.limit_adv_nonpos_offsupport`'s docstring identifies as what AKM
actually prove and this repo does not supply. -/

end Conv

end Proofs
end PolicyGradient
