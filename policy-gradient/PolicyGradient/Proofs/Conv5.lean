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

/-- For each `t` there is a state maximising `f t`. -/
theorem exists_argmax_pointwise (f : ℕ → S → ℝ) (t : ℕ) :
    ∃ s : S, ∀ s', f t s' ≤ f t s := by
  obtain ⟨s, _, hs⟩ :=
    Finset.exists_max_image (Finset.univ : Finset S) (f t) Finset.univ_nonempty
  exact ⟨s, fun s' => hs s' (Finset.mem_univ s')⟩

/-- **Pigeonhole on a finite state space.**  Some state maximises `f t`
for infinitely many `t`. -/
theorem exists_frequently_argmax (f : ℕ → S → ℝ) :
    ∃ s : S, ∃ᶠ t in atTop, ∀ s', f t s' ≤ f t s := by
  classical
  by_contra hcon
  push_neg at hcon
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
maximum consistent with the logit order. -/
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
  obtain ⟨T₀, hnn, hdom⟩ := hstable s Z hchar
  exact lead_at_eventual_argmax M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s Z hZ T₀ hdom hnn

end Conv5

end Proofs
end PolicyGradient
