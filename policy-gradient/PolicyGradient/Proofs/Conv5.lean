/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv3

/-!
# AKM Theorem 5.1 / Mei Lemma 9 for general `γ` — the argmax-state advantage

## The shape of `hlead` (settled here)

`Proofs.Conv3.softmax_policy_converges_of_leader` reduces the frozen goal
`Goal.softmax_policy_converges` to `hlead`.  Its quantifier order is

```
hlead : ∀ (s : S) (Z : Finset A), (Z is the zero-advantage set at s) →
          ∃ a₀ ∈ Z, ∃ T : ℕ, (leader at T) ∧ (gaps never shrink from T on)
```

so the time `T` and the leader `a₀` are **per-state**: both existentials sit
*inside* the `∀ s`.  A route may therefore hand every state its own leader and
its own starting time.  That is strictly more room than a uniform `T` would
give, and it is what makes the pigeonhole idea below worth stating at all.

## What this file proves

Write `δ_t s := Vbar s - V^{(t)}(s) ≥ 0`, decreasing to `0`
(`Conv2.exists_Vinf_tendsto` + `Resid.exists_Vinf_limit`).  The proved identity
`(‡)` (`Proofs.adv_eq_value_gap_of_zero_limit`) reads, for any action whose
limiting advantage vanishes,

```
A^{(t)}(s,a) = δ_t s - γ · ∑_{s'} P(s'|s,a) · δ_t s'.
```

`adv_ge_one_sub_gamma_mul_gap` below is the sharp consequence: **at a state
maximising `δ_t`, every tied action has advantage at least `(1-γ) δ_t s`, hence
`≥ 0`**, and moreover all tied advantages there are squeezed into the band
`[(1-γ) δ_t s, δ_t s]`.  Both facts are unconditional and `πbar`-free.

`adv_dominates_at_argmax_of_gap_zero` records the exact degenerate case in which
the band collapses and `gap_monotone_of_adv_dominates` applies outright.

## Why this does not yet close `hlead` (the obstruction, stated exactly)

`Conv3.gap_monotone_of_adv_dominates` needs, at a **fixed** state `s`, for a
leader `a₀` and every `b ∈ Z s`, the pair of inequalities
`0 ≤ A^{(t)}(s,b) ≤ A^{(t)}(s,a₀)` at **every** `t ≥ T` — because
`Conv3.gap_nonneg_of_step` inducts over all `t ≥ T`, and one step at which the
gap shrinks destroys the antitone ratio that `Conv3.exists_ratio_limit` needs.

The argmax bound supplies `0 ≤ A^{(t)}(s,·)` only at the times when `s` *is* the
`δ_t`-maximiser.  Since `S` is finite, some `s₀` is the maximiser for infinitely
many `t` (`exists_frequently_argmax`, proved below), so the sign is available
**cofinally** at `s₀` — but *not* cofinitely, and the gap can shrink at the
intervening times.  Infinitely-often is therefore genuinely insufficient for
`hlead` as stated: the two hypotheses of `coord_tendsto_of_leader` that consume
`T` (`gap_nonneg_of_step`, `exists_ratio_limit`) are both `∀ t ≥ T` inductions.

Closing the remaining gap needs the `δ_t`-argmax **order** to be eventually
constant.  That does **not** follow from the available facts: `δ_t` is only known
to be componentwise nonnegative, antitone and null, and two antitone null
sequences can cross infinitely often (interleaved staircases), so nothing in the
present hypothesis set forbids the maximiser from oscillating forever.  Ruling
that out needs a rate comparison between the coordinates of `δ_t` — the same
missing ingredient `Conv3`'s header names as "a signed rate comparison of
`π_t(a|s) A^{(t)}(s,a)` against `π_t(b|s) A^{(t)}(s,b)`", and the same one that
`ResidC9.ratio_step` supplies only after a limit policy has been assumed.

`softmax_policy_converges_of_argmax_stable` below is the honest reduction: it
closes the frozen goal for general `γ` from exactly that eventual-stability
hypothesis, with everything else discharged.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv5

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ## The argmax-state advantage bound -/

/-- **At a `δ_t`-maximising state every tied action has advantage `≥ (1-γ) δ_t s`.**

`hVbar` is the Bellman identity that `(‡)` needs (available from
`vbar_bellman_of_adv_limit_zero` whenever `a`'s limiting advantage vanishes);
`hmax` says `s` maximises the value gap `δ_t = Vbar - V^{(t)}`; `hnn` says the
gap is nonnegative, which `exists_Vinf_limit`'s monotonicity supplies. -/
theorem adv_ge_one_sub_gamma_mul_gap (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a : A) (t : ℕ)
    (hγ₀ : 0 ≤ M.γ)
    (hVbar : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hmax : ∀ s', Vbar s' - Vinf M (π t) s' ≤ Vbar s - Vinf M (π t) s) :
    (1 - M.γ) * (Vbar s - Vinf M (π t) s) ≤ advInf M (π t) s a := by
  classical
  set δ : S → ℝ := fun s' => Vbar s' - Vinf M (π t) s' with hδ
  rw [adv_eq_value_gap_of_zero_limit M π Vbar s a hVbar t]
  -- `∑ P(s'|s,a) δ s' ≤ δ s`, since `P(·|s,a)` is a distribution and `δ ≤ δ s`.
  have hsum : ∑ s', (M.P s a) s' * δ s' ≤ δ s := by
    have hle : ∑ s', (M.P s a) s' * δ s' ≤ ∑ s', (M.P s a) s' * δ s :=
      Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (hmax s') ((M.P s a).nonneg s')
    calc ∑ s', (M.P s a) s' * δ s' ≤ ∑ s', (M.P s a) s' * δ s := hle
      _ = δ s := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
  nlinarith [hsum]

/-- The companion upper bound: at any state, an action with vanishing limiting
advantage has `A^{(t)}(s,a) ≤ δ_t s` as soon as the gap vector is nonnegative. -/
theorem adv_le_gap (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a : A) (t : ℕ)
    (hγ₀ : 0 ≤ M.γ)
    (hVbar : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hnn : ∀ s', 0 ≤ Vbar s' - Vinf M (π t) s') :
    advInf M (π t) s a ≤ Vbar s - Vinf M (π t) s := by
  classical
  rw [adv_eq_value_gap_of_zero_limit M π Vbar s a hVbar t]
  have hsum : 0 ≤ ∑ s', (M.P s a) s' * (Vbar s' - Vinf M (π t) s') :=
    Finset.sum_nonneg fun s' _ => mul_nonneg ((M.P s a).nonneg s') (hnn s')
  nlinarith [hsum]

/-- **The tied advantages at a `δ_t`-maximising state all lie in the band
`[(1-γ) δ_t s, δ_t s]`.** -/
theorem adv_mem_band_at_argmax (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a : A) (t : ℕ)
    (hγ₀ : 0 ≤ M.γ)
    (hVbar : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hnn : ∀ s', 0 ≤ Vbar s' - Vinf M (π t) s')
    (hmax : ∀ s', Vbar s' - Vinf M (π t) s' ≤ Vbar s - Vinf M (π t) s) :
    (1 - M.γ) * (Vbar s - Vinf M (π t) s) ≤ advInf M (π t) s a ∧
      advInf M (π t) s a ≤ Vbar s - Vinf M (π t) s :=
  ⟨adv_ge_one_sub_gamma_mul_gap M π Vbar s a t hγ₀ hVbar hmax,
   adv_le_gap M π Vbar s a t hγ₀ hVbar hnn⟩

/-- **The advantage at a `δ_t`-maximising state is nonnegative**, for every
action whose limiting advantage vanishes.  This is the hypothesis
`gap_monotone_of_adv_dominates` calls `hBnn`. -/
theorem adv_nonneg_at_argmax (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a : A) (t : ℕ)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (hVbar : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hnn : ∀ s', 0 ≤ Vbar s' - Vinf M (π t) s')
    (hmax : ∀ s', Vbar s' - Vinf M (π t) s' ≤ Vbar s - Vinf M (π t) s) :
    0 ≤ advInf M (π t) s a := by
  have h := adv_ge_one_sub_gamma_mul_gap M π Vbar s a t hγ₀ hVbar hmax
  nlinarith [hnn s]

/-- **The degenerate case in which the band collapses.**  If two tied actions at
a `δ_t`-maximising state have the *same* transition row against the gap vector,
their advantages coincide, and `gap_monotone_of_adv_dominates` applies to the
pair with no further input. -/
theorem adv_dominates_at_argmax_of_gap_zero (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a b : A) (t : ℕ)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (hVa : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s'))
    (hVb : Vbar s = M.r s b + M.γ * (∑ s', (M.P s b) s' * Vbar s'))
    (hnn : ∀ s', 0 ≤ Vbar s' - Vinf M (π t) s')
    (hmax : ∀ s', Vbar s' - Vinf M (π t) s' ≤ Vbar s - Vinf M (π t) s)
    (hrow : ∑ s', (M.P s a) s' * (Vbar s' - Vinf M (π t) s')
      = ∑ s', (M.P s b) s' * (Vbar s' - Vinf M (π t) s')) :
    0 ≤ advInf M (π t) s b ∧
      advInf M (π t) s b ≤ advInf M (π t) s a := by
  refine ⟨adv_nonneg_at_argmax M π Vbar s b t hγ₀ hγ₁ hVb hnn hmax, ?_⟩
  rw [adv_eq_value_gap_of_zero_limit M π Vbar s a hVa t,
    adv_eq_value_gap_of_zero_limit M π Vbar s b hVb t, hrow]

/-! ## Pigeonhole: some state is the `δ_t`-maximiser infinitely often -/

omit [DecidableEq S] [DecidableEq A] [Nonempty A] in
/-- For each `t` there is a state maximising `f t`. -/
theorem exists_argmax_pointwise (f : ℕ → S → ℝ) (t : ℕ) :
    ∃ s : S, ∀ s', f t s' ≤ f t s := by
  obtain ⟨s, _, hs⟩ :=
    Finset.exists_max_image (Finset.univ : Finset S) (f t) Finset.univ_nonempty
  exact ⟨s, fun s' => hs s' (Finset.mem_univ s')⟩

omit [DecidableEq S] [DecidableEq A] [Nonempty A] in
/-- **Pigeonhole on a finite state space.**  Some state maximises `f t`
for infinitely many `t`. -/
theorem exists_frequently_argmax (f : ℕ → S → ℝ) :
    ∃ s : S, ∃ᶠ t in atTop, ∀ s', f t s' ≤ f t s := by
  classical
  by_contra hcon
  push Not at hcon
  -- for each `s` the maximiser property holds only up to some time `T s`
  have hev : ∀ s : S, ∀ᶠ t in atTop, ¬ (∀ s', f t s' ≤ f t s) := by
    intro s
    simpa using hcon s
  have hall : ∀ᶠ t in atTop, ∀ s : S, ¬ (∀ s', f t s' ≤ f t s) :=
    (Filter.eventually_all (p := fun s t => ¬ (∀ s', f t s' ≤ f t s))).2 hev
  obtain ⟨t, ht⟩ := hall.exists
  obtain ⟨s, hs⟩ := exists_argmax_pointwise f t
  exact ht s hs

/-! ## The reduction to eventual stability of the `δ_t`-argmax

This is the honest statement of what remains.  Given a state `s₀` that is the
`δ_t`-maximiser from some time `T₀` on — *cofinitely*, not merely cofinally —
every hypothesis of `hlead` is discharged **at that state**.  The residual
content is that such an `s₀` exists at all. -/

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- **`hlead` is free at a state with no genuine tie.**  If the zero-advantage
set `Z` is a subsingleton, its unique element leads vacuously and every gap
condition is trivial: there is no second action to shrink a gap against.  So a
route need only supply the leader hypothesis at states where `Z` has at least
two elements. -/
theorem lead_of_subsingleton (θ : ℕ → EuclideanSpace ℝ (S × A))
    (s : S) (Z : Finset A) (hZ : Z.Nonempty) (hcard : Z.card ≤ 1) :
    ∃ a₀ ∈ Z, ∃ T : ℕ, (∀ b ∈ Z, (θ T) (s, b) ≤ (θ T) (s, a₀)) ∧
      (∀ b ∈ Z, ∀ t, T ≤ t → (θ t) (s, b) ≤ (θ t) (s, a₀) →
        (θ t) (s, a₀) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a₀) - (θ (t + 1)) (s, b)) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hZ
  have huniq : ∀ b ∈ Z, b = a₀ := by
    intro b hb
    exact Finset.card_le_one.mp hcard b hb a₀ ha₀
  refine ⟨a₀, ha₀, 0, ?_, ?_⟩
  · intro b hb; rw [huniq b hb]
  · intro b hb t _ _; rw [huniq b hb]; simp

/-- **At an eventually-maximising state, `hlead` holds.**  If `s` maximises the
value gap for every `t ≥ T₀`, then any leader chosen at time `T₀` from the tied
set has never-shrinking gaps to every other tied action, provided the tied
advantages are comparable — which the band of `adv_mem_band_at_argmax` gives
whenever the rows agree against `δ_t`. -/
theorem lead_at_eventual_argmax (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (Z : Finset A) (hZ : Z.Nonempty) (T₀ : ℕ)
    (hdom : ∀ a ∈ Z, ∀ b ∈ Z, ∀ t, T₀ ≤ t →
      0 ≤ advInf M (F.toPolicy (θ t)) s b →
      (θ t) (s, b) ≤ (θ t) (s, a) →
      advInf M (F.toPolicy (θ t)) s b ≤ advInf M (F.toPolicy (θ t)) s a)
    (hnn : ∀ b ∈ Z, ∀ t, T₀ ≤ t → 0 ≤ advInf M (F.toPolicy (θ t)) s b) :
    ∃ a₀ ∈ Z, ∃ T : ℕ, (∀ b ∈ Z, (θ T) (s, b) ≤ (θ T) (s, a₀)) ∧
      (∀ b ∈ Z, ∀ t, T ≤ t → (θ t) (s, b) ≤ (θ t) (s, a₀) →
        (θ t) (s, a₀) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a₀) - (θ (t + 1)) (s, b)) := by
  classical
  obtain ⟨a₀, ha₀, hmax⟩ := exists_leader Z hZ (fun a => (θ T₀) (s, a))
  refine ⟨a₀, ha₀, T₀, hmax, ?_⟩
  intro b hb t ht hle
  exact gap_monotone_of_adv_dominates M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s a₀ b t
    (hdom a₀ ha₀ b hb t ht (hnn b hb t ht) hle) (hnn b hb t ht) hle

/-- **The frozen goal for general `γ`, from eventual stability of the tied
advantage order.**  This is `softmax_policy_converges_of_leader` with `hlead`
repackaged into the per-state form that the argmax analysis produces: at each
state, from some time on, the tied advantages are nonnegative and admit a
maximum consistent with the logit order.

`hstable` is demanded **only at states whose zero-advantage set has at least two
elements** — `lead_of_subsingleton` discharges the rest outright — so the
residual content is confined to genuine ties. -/
theorem softmax_policy_converges_of_argmax_stable (M : FiniteMDP S A)
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
      2 ≤ Z.card →
      ∃ T₀ : ℕ,
        (∀ b ∈ Z, ∀ t, T₀ ≤ t → 0 ≤ advInf M (F.toPolicy (θ t)) s b) ∧
        (∀ a ∈ Z, ∀ b ∈ Z, ∀ t, T₀ ≤ t →
          0 ≤ advInf M (F.toPolicy (θ t)) s b →
          (θ t) (s, b) ≤ (θ t) (s, a) →
          advInf M (F.toPolicy (θ t)) s b ≤ advInf M (F.toPolicy (θ t)) s a)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) := by
  classical
  refine softmax_policy_converges_of_leader M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep ?_
  intro s Z hchar
  -- `Z` is nonempty: otherwise every coordinate at `s` dies, contradicting the
  -- mass identity `tendsto_mass_on_zero_set`.
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
  -- a state with no genuine tie needs no hypothesis at all
  by_cases hcard : 2 ≤ Z.card
  · obtain ⟨T₀, hnn, hdom⟩ := hstable s Z hchar hcard
    exact lead_at_eventual_argmax M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s Z hZ T₀ hdom hnn
  · exact lead_of_subsingleton θ s Z hZ (by omega)

/-! ## Why the argmax route cannot be closed from the available facts

Everything the repo knows about the gap vector `δ_t = Vbar - V^{(t)}` is that,
componentwise, it is **nonnegative**, **antitone** and **null**
(`Resid.exists_Vinf_limit` for monotonicity of `V^{(t)}`, `Conv2.exists_Vinf_tendsto`
for the limit).  The lemmas below show that this hypothesis set is *strictly too
weak* to force the `δ_t`-maximiser to stabilise: there are two sequences with all
three properties whose maximiser alternates forever.

Consequently `exists_frequently_argmax`'s *infinitely often* cannot be upgraded
to *eventually* by any argument that sees only nonnegativity, antitonicity and
nullity of `δ_t`.  A proof of `hstable` must use something else — a rate. -/

/-- The leading staircase: `4 ^ -⌈t/2⌉`.  It steps down on odd `t`. -/
noncomputable def stairA (t : ℕ) : ℝ := (1 / 4 : ℝ) ^ ((t + 1) / 2)

/-- The partner staircase: `(3/4) · 4 ^ -⌊t/2⌋`.  It steps down on even `t`,
so the two swap the lead at **every** step. -/
noncomputable def stairB (t : ℕ) : ℝ := (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ (t / 2)

theorem stairA_pos (t : ℕ) : 0 < stairA t := by
  unfold stairA; positivity

theorem stairB_pos (t : ℕ) : 0 < stairB t := by
  unfold stairB; positivity

theorem stairA_antitone : Antitone stairA := by
  refine antitone_nat_of_succ_le fun t => ?_
  unfold stairA
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem stairB_antitone : Antitone stairB := by
  refine antitone_nat_of_succ_le fun t => ?_
  unfold stairB
  have := pow_le_pow_of_le_one (a := (1/4 : ℝ)) (by norm_num) (by norm_num)
    (show t / 2 ≤ (t + 1) / 2 by omega)
  linarith

/-- Both half-index maps tend to infinity. -/
theorem tendsto_half_atTop (c : ℕ) :
    Tendsto (fun t : ℕ => (t + c) / 2) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun n => ⟨2 * n, fun t ht => by omega⟩

theorem stairA_tendsto_zero : Tendsto stairA atTop (nhds 0) := by
  have hb : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact hb.comp (tendsto_half_atTop 1)

theorem stairB_tendsto_zero : Tendsto stairB atTop (nhds 0) := by
  have hb : Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h0 := (hb.comp (tendsto_half_atTop 0)).const_mul (3 / 4 : ℝ)
  rw [mul_zero] at h0
  exact h0.congr (fun t => by simp [stairB, Function.comp])

/-- **At even times `stairA` strictly leads**: `4^-k` against `(3/4)·4^-k`. -/
theorem stairB_lt_stairA_even (k : ℕ) : stairB (2 * k) < stairA (2 * k) := by
  unfold stairA stairB
  have h1 : (2 * k + 1) / 2 = k := by omega
  have h2 : (2 * k) / 2 = k := by omega
  rw [h1, h2]
  have hp : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
  linarith

/-- **At odd times `stairB` strictly leads**: `(3/4)·4^-k` against `4^-(k+1)`. -/
theorem stairA_lt_stairB_odd (k : ℕ) : stairA (2 * k + 1) < stairB (2 * k + 1) := by
  unfold stairA stairB
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2]
  have hp : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
  have hstep : (1 / 4 : ℝ) ^ (k + 1) = (1 / 4 : ℝ) ^ k * (1 / 4) := by ring
  rw [hstep]
  linarith

/-- **The maximiser of an antitone null nonnegative pair need not stabilise.**

There is a family `δ : ℕ → Fin 2 → ℝ` that is componentwise nonnegative,
antitone and null — every property the repo can prove of `Vbar - V^{(t)}` — for
which **no** index is the maximiser from any time on.  So `hstable` (equivalently,
eventual stability of the `δ_t`-argmax) is **not** a consequence of those three
properties; deriving it requires a rate comparison between coordinates. -/
theorem argmax_not_eventually_stable :
    ∃ δ : ℕ → Fin 2 → ℝ,
      (∀ i t, 0 ≤ δ t i) ∧
      (∀ i, Antitone (fun t => δ t i)) ∧
      (∀ i, Tendsto (fun t => δ t i) atTop (nhds 0)) ∧
      (∀ i : Fin 2, ∀ T : ℕ, ∃ t, T ≤ t ∧ ¬ (∀ j, δ t j ≤ δ t i)) := by
  classical
  refine ⟨fun t i => if i = 0 then stairA t else stairB t, ?_, ?_, ?_, ?_⟩
  · intro i t
    by_cases h : i = 0
    · simp [h, (stairA_pos t).le]
    · simp [h, (stairB_pos t).le]
  · intro i
    by_cases h : i = 0
    · simpa [h] using stairA_antitone
    · simpa [h] using stairB_antitone
  · intro i
    by_cases h : i = 0
    · simpa [h] using stairA_tendsto_zero
    · simpa [h] using stairB_tendsto_zero
  · intro i T
    by_cases h : i = 0
    · -- `stairA` is strictly beaten at the odd time `2T+1`
      refine ⟨2 * T + 1, by omega, ?_⟩
      intro hmax
      have h1 := hmax 1
      simp only [h] at h1
      rw [if_neg (by decide : ¬((1 : Fin 2) = 0))] at h1
      exact absurd h1 (not_le.mpr (stairA_lt_stairB_odd T))
    · -- `stairB` is strictly beaten at the even time `2(T+1)`
      refine ⟨2 * (T + 1), by omega, ?_⟩
      intro hmax
      have h0 := hmax 0
      simp only [if_neg h] at h0
      exact absurd h0 (not_le.mpr (stairB_lt_stairA_even (T + 1)))

/-! ## Axiom / type audit -/

section Audit

#print axioms adv_ge_one_sub_gamma_mul_gap
#print axioms adv_le_gap
#print axioms adv_nonneg_at_argmax
#print axioms adv_dominates_at_argmax_of_gap_zero
#print axioms exists_frequently_argmax
#print axioms lead_of_subsingleton
#print axioms lead_at_eventual_argmax
#print axioms softmax_policy_converges_of_argmax_stable
#print axioms argmax_not_eventually_stable

end Audit

end Conv5

end Proofs
end PolicyGradient
