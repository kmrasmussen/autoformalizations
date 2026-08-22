/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.ResidAsm
import PolicyGradient.Proofs.ResidC9

/-!
# ResidFinal — the final contradiction of AKM Appendix C.1
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section ResidFinal

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- A finite sum of sequences each tending to `0` tends to `0`. -/
theorem tendsto_finset_sum_zero {ι : Type*} (T : Finset ι) (f : ι → ℕ → ℝ)
    (h : ∀ i ∈ T, Filter.Tendsto (f i) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => ∑ i ∈ T, f i t) Filter.atTop (nhds 0) := by
  have := tendsto_finsetSum T (fun i hi => h i hi)
  simpa using this

/-! ## The sign classification of actions at a state -/

variable (M : FiniteMDP S A) (πbar : Policy S A) (s : S)

/-- `I⁰_s`: actions with zero limiting advantage. -/
noncomputable def I0 : Finset A := {a | advInf M πbar s a = 0}

/-- `I⁺_s`: actions with positive limiting advantage. -/
noncomputable def Iplus : Finset A := {a | 0 < advInf M πbar s a}

/-- `I⁻_s`: actions with negative limiting advantage. -/
noncomputable def Iminus : Finset A := {a | advInf M πbar s a < 0}

variable {M πbar s}

@[simp] theorem mem_I0 {a : A} : a ∈ I0 M πbar s ↔ advInf M πbar s a = 0 := by
  simp [I0]

@[simp] theorem mem_Iplus {a : A} : a ∈ Iplus M πbar s ↔ 0 < advInf M πbar s a := by
  simp [Iplus]

@[simp] theorem mem_Iminus {a : A} : a ∈ Iminus M πbar s ↔ advInf M πbar s a < 0 := by
  simp [Iminus]

/-- The three classes partition `univ`. -/
theorem sum_split_three (f : A → ℝ) :
    ∑ a, f a = (∑ a ∈ I0 M πbar s, f a) + (∑ a ∈ Iplus M πbar s, f a)
      + (∑ a ∈ Iminus M πbar s, f a) := by
  classical
  have hdisj1 : Disjoint (I0 M πbar s) (Iplus M πbar s) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [mem_I0] at ha; rw [mem_Iplus] at hb; rw [ha] at hb; exact lt_irrefl _ hb
  have hunion : (I0 M πbar s ∪ Iplus M πbar s) ∪ Iminus M πbar s = Finset.univ := by
    ext a; simp only [Finset.mem_union, Finset.mem_univ, iff_true, mem_I0, mem_Iplus, mem_Iminus]
    rcases lt_trichotomy (advInf M πbar s a) 0 with h | h | h
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  have hdisj2 : Disjoint (I0 M πbar s ∪ Iplus M πbar s) (Iminus M πbar s) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [mem_Iminus] at hb
    rcases Finset.mem_union.mp ha with h | h
    · rw [mem_I0] at h; rw [h] at hb; exact lt_irrefl _ hb
    · rw [mem_Iplus] at h; linarith
  rw [← hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1]

/-! ## The `B0` set and the endgame

Fix the counterexample state `s` and action `ap` (`π̄(ap|s) = 0`,
`A^{π̄}(s,ap) > 0`). AKM partition `I^s_0` at a threshold time `T0` into

* `B0 = {a ∈ I0 | ∀ t ≥ T0, π^{(t)}(ap|s) < π^{(t)}(a|s)}`,
* `B0bar = I0 \ B0`.
-/

/-- `B^s_0(ap)` at threshold `T0`. -/
noncomputable def B0 (M : FiniteMDP S A) (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A) (s : S) (ap : A) (T0 : ℕ) :
    Finset A := by
  classical
  exact (I0 M πbar s).filter
    (fun a => ∀ t, T0 ≤ t → (F.toPolicy (θ t) s) ap < (F.toPolicy (θ t) s) a)

theorem mem_B0 {M : FiniteMDP S A} {F : VecPolicy S A (EuclideanSpace ℝ (S × A))}
    {θ : ℕ → EuclideanSpace ℝ (S × A)} {πbar : Policy S A} {s : S} {ap : A} {T0 : ℕ}
    {a : A} :
    a ∈ B0 M F θ πbar s ap T0 ↔ advInf M πbar s a = 0 ∧
      ∀ t, T0 ≤ t → (F.toPolicy (θ t) s) ap < (F.toPolicy (θ t) s) a := by
  classical
  simp [B0, I0]

theorem B0_subset_I0 {M : FiniteMDP S A} {F : VecPolicy S A (EuclideanSpace ℝ (S × A))}
    {θ : ℕ → EuclideanSpace ℝ (S × A)} {πbar : Policy S A} {s : S} {ap : A} {T0 : ℕ} :
    B0 M F θ πbar s ap T0 ⊆ I0 M πbar s := by
  intro a ha; exact (mem_I0).mpr (mem_B0.mp ha).1

/-! ### The threshold time `T0`

`T0` is chosen so that for all `t ≥ T0` and every action `a`:

* `A^{(t)}(s,ap) ≥ Δ/2` where `Δ := A^{π̄}(s,ap) > 0` (continuity at `ap`);
* `|A^{(t)}(s,a) - A^{π̄}(s,a)| ≤ Δ/8` (continuity at each `a`, finitely many).

Then for `a ∈ I0 ∪ I-` we get `A^{(t)}(s,a) ≤ Δ/8 < Δ/2 ≤ A^{(t)}(s,ap)`, which
is the advantage ordering `stable_forward` needs. -/

theorem exists_T0 (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (ap : A) (hpos : 0 < advInf M πbar s ap) :
    ∃ T0 : ℕ, (∀ t, T0 ≤ t → advInf M πbar s ap / 2 ≤ advInf M (F.toPolicy (θ t)) s ap) ∧
      (∀ a, advInf M πbar s a ≤ 0 → ∀ t, T0 ≤ t →
        advInf M (F.toPolicy (θ t)) s a ≤ advInf M (F.toPolicy (θ t)) s ap) := by
  classical
  set Δ : ℝ := advInf M πbar s ap with hΔ
  -- continuity at `ap`
  have hev0 : ∀ᶠ t in Filter.atTop, Δ / 2 ≤ advInf M (F.toPolicy (θ t)) s ap :=
    eventually_adv_pos M F hr hγ₀ hγ₁ θ πbar hlim s ap hpos
  -- continuity at each `a`: `A^{(t)}(s,a) ≤ A^{π̄}(s,a) + Δ/4`
  have hevA : ∀ a : A, ∀ᶠ t in Filter.atTop,
      advInf M (F.toPolicy (θ t)) s a ≤ advInf M πbar s a + Δ / 4 := by
    intro a
    have hA := tendsto_adv_traj M F hr hγ₀ hγ₁ θ πbar hlim s a
    have hlt : advInf M πbar s a < advInf M πbar s a + Δ / 4 := by linarith
    exact (hA.eventually (eventually_lt_nhds hlt)).mono fun t ht => le_of_lt ht
  -- combine over the finitely many actions
  have hall : ∀ᶠ t in Filter.atTop, (Δ / 2 ≤ advInf M (F.toPolicy (θ t)) s ap) ∧
      ∀ a : A, advInf M (F.toPolicy (θ t)) s a ≤ advInf M πbar s a + Δ / 4 := by
    refine hev0.and ?_
    exact (Filter.eventually_all (p := fun (a : A) t =>
      advInf M (F.toPolicy (θ t)) s a ≤ advInf M πbar s a + Δ / 4)).mpr hevA
  obtain ⟨T0, hT0⟩ := hall.exists_forall_of_atTop
  refine ⟨T0, fun t ht => (hT0 t ht).1, fun a ha t ht => ?_⟩
  have h1 := (hT0 t ht).2 a
  have h2 := (hT0 t ht).1
  linarith


/-! ### AKM Lemma `lemma:small`: `B0bar` actions are dominated by `ap`

If `a ∈ I0 \ B0` then by definition of `B0` there is some `t_a ≥ T0` with
`π^{(t_a)}(a|s) ≤ π^{(t_a)}(ap|s)`. From `T0` on the advantage ordering
`A^{(t)}(s,a) ≤ A^{(t)}(s,ap)` holds (`hT0ord`) with `A^{(t)}(s,ap) ≥ Δ/2 > 0`,
so `stable_forward` propagates the probability ordering from `t_a` onwards. -/

theorem B0bar_dominated (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A) (s : S) (ap : A) (T0 : ℕ)
    (hΔ : 0 < advInf M πbar s ap)
    (hT0ap : ∀ t, T0 ≤ t → advInf M πbar s ap / 2 ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hT0ord : ∀ a, advInf M πbar s a ≤ 0 → ∀ t, T0 ≤ t →
      advInf M (F.toPolicy (θ t)) s a ≤ advInf M (F.toPolicy (θ t)) s ap)
    (a : A) (ha0 : advInf M πbar s a = 0) (haB : a ∉ B0 M F θ πbar s ap T0) :
    ∃ Ta : ℕ, ∀ t, Ta ≤ t → (F.toPolicy (θ t) s) a ≤ (F.toPolicy (θ t) s) ap := by
  classical
  -- `a ∉ B0` while `a ∈ I0`, so the defining condition fails
  have hfail : ¬ (∀ t, T0 ≤ t → (F.toPolicy (θ t) s) ap < (F.toPolicy (θ t) s) a) := by
    intro hcon
    exact haB (mem_B0.mpr ⟨ha0, hcon⟩)
  push_neg at hfail
  obtain ⟨ta, hta0, hta⟩ := hfail
  refine ⟨ta, ?_⟩
  refine stable_forward M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s a ap ta ?_ ?_ hta
  · intro t ht
    exact hT0ord a (le_of_eq ha0) t (le_trans hta0 ht)
  · intro t ht
    have := hT0ap t (le_trans hta0 ht)
    linarith


/-! ### Mass concentration: `∑_{a ∈ B0} π^{(t)}(a|s) → 1`

Every action **outside** `B0` has `π^{(t)}(a|s) → 0`:

* `a ∈ I+`: `tendsto_pi_zero_of_adv_pos` gives `π̄(a|s) = 0`;
* `a ∈ I-`: `theta_tendsto_atBot_of_adv_neg` + `pi_tendsto_zero_of_theta_atBot`;
* `a ∈ B0bar`: dominated by `π^{(t)}(ap|s) → 0` (`B0bar_dominated`).

Since the total mass is `1`, the `B0` mass tends to `1`. -/

theorem pi_tendsto_zero_outside_B0 (M : FiniteMDP S A)
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
    (s : S) (ap : A) (T0 : ℕ)
    (hΔ : 0 < advInf M πbar s ap)
    (hT0ap : ∀ t, T0 ≤ t → advInf M πbar s ap / 2 ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hT0ord : ∀ a, advInf M πbar s a ≤ 0 → ∀ t, T0 ≤ t →
      advInf M (F.toPolicy (θ t)) s a ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hap0 : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) ap) Filter.atTop (nhds 0))
    (a : A) (haB : a ∉ B0 M F θ πbar s ap T0) :
    Filter.Tendsto (fun t => (F.toPolicy (θ t) s) a) Filter.atTop (nhds 0) := by
  classical
  rcases lt_trichotomy (advInf M πbar s a) 0 with hneg | hzero | hpos
  · -- `a ∈ I⁻`: `θ^{(t)}(s,a) → -∞`
    have hbot := theta_tendsto_atBot_of_adv_neg M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
      πbar hlim s a hneg ⟨ap, hΔ⟩
    obtain ⟨c, T, hc⟩ := not_theta_atBot_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ θ hstep
      πbar hlim s ap hΔ
    exact pi_tendsto_zero_of_theta_atBot M F hF θ s a c ap T hc hbot
  · -- `a ∈ I⁰ \ B0` = `B0bar`: dominated by `π^{(t)}(ap|s) → 0`
    obtain ⟨Ta, hTa⟩ := B0bar_dominated M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep πbar s ap T0
      hΔ hT0ap hT0ord a hzero haB
    refine squeeze_zero' ?_ ?_ hap0
    · exact Filter.Eventually.of_forall fun t => (F.toPolicy (θ t) s).nonneg a
    · exact Filter.eventually_atTop.mpr ⟨Ta, hTa⟩
  · -- `a ∈ I⁺`: `π̄(a|s) = 0`
    have hbar : (πbar s) a =
        0 := tendsto_pi_zero_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
      πbar hlim s a hpos
    have := tendsto_pi_coord F θ πbar hlim s a
    rwa [hbar] at this

/-- **AKM Lemma C.11, first claim.** `∑_{a ∈ B0} π^{(t)}(a|s) → 1`. -/
theorem sum_B0_pi_tendsto_one (M : FiniteMDP S A)
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
    (s : S) (ap : A) (T0 : ℕ)
    (hΔ : 0 < advInf M πbar s ap)
    (hT0ap : ∀ t, T0 ≤ t → advInf M πbar s ap / 2 ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hT0ord : ∀ a, advInf M πbar s a ≤ 0 → ∀ t, T0 ≤ t →
      advInf M (F.toPolicy (θ t)) s a ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hap0 : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) ap) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => ∑ a ∈ B0 M F θ πbar s ap T0, (F.toPolicy (θ t) s) a)
      Filter.atTop (nhds 1) := by
  classical
  set B : Finset A := B0 M F θ πbar s ap T0 with hB
  -- the complement's mass tends to `0`
  have hcompl : Filter.Tendsto
      (fun t => ∑ a ∈ (Finset.univ : Finset A) \ B, (F.toPolicy (θ t) s) a)
      Filter.atTop (nhds 0) := by
    refine tendsto_finset_sum_zero _ _ fun a ha => ?_
    have : a ∉ B := (Finset.mem_sdiff.mp ha).2
    exact pi_tendsto_zero_outside_B0 M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim
      s ap T0 hΔ hT0ap hT0ord hap0 a this
  -- total mass is `1`
  have htot : ∀ t, ∑ a ∈ B, (F.toPolicy (θ t) s) a
      = 1 - ∑ a ∈ (Finset.univ : Finset A) \ B, (F.toPolicy (θ t) s) a := by
    intro t
    have hsub : B ⊆ (Finset.univ : Finset A) := Finset.subset_univ B
    have := Finset.sum_sdiff (f := fun a => (F.toPolicy (θ t) s) a) hsub
    rw [(F.toPolicy (θ t) s).sum_eq_one] at this
    linarith
  have := (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop (α := ℕ))).sub hcompl
  simp only [sub_zero] at this
  exact this.congr (fun t => (htot t).symm)


/-! ### `B0 ≠ ∅` and `max_{a ∈ B0} θ^{(t)}(s,a) → ∞`

`B0 ≠ ∅` is immediate from `∑_{B0} π^{(t)} → 1` (an empty sum is `0`).

For the max: `π^{(t)}(a|s) ≤ exp(θ^{(t)}(s,a) - Mx_B) · |A| · π^{(t)}(a|s)`… more
directly, writing `Mx_B t = max_{a ∈ B0} θ^{(t)}(s,a)`, the softmax ratio against
`ap` gives, for each `a ∈ B0`,
`π^{(t)}(a|s) = exp(θ_a - θ_ap) π^{(t)}(ap|s) ≤ exp(Mx_B t - c) π^{(t)}(ap|s)`,
so `1/2 ≤ ∑_{B0} π^{(t)}(a|s) ≤ |A| exp(Mx_B t - c) π^{(t)}(ap|s)`. Since
`π^{(t)}(ap|s) → 0`, `exp(Mx_B t - c) → ∞`, i.e. `Mx_B t → ∞`. -/

theorem B0_nonempty (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (s : S) (ap : A) (T0 : ℕ)
    (hsum : Filter.Tendsto (fun t => ∑ a ∈ B0 M F θ πbar s ap T0, (F.toPolicy (θ t) s) a)
      Filter.atTop (nhds 1)) :
    (B0 M F θ πbar s ap T0).Nonempty := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  rw [hempty] at hsum
  simp only [Finset.sum_empty] at hsum
  have := tendsto_nhds_unique hsum (tendsto_const_nhds (x := (0:ℝ)))
  norm_num at this

/-- **AKM Lemma C.11, second claim.** `max_{a ∈ B0} θ^{(t)}(s,a) → ∞`. -/
theorem tendsto_max_B0_theta_atTop (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (s : S) (ap : A) (T0 : ℕ) (c : ℝ) (T : ℕ)
    (hne : (B0 M F θ πbar s ap T0).Nonempty)
    (hlow : ∀ t, T ≤ t → c ≤ (θ t) (s, ap))
    (hsum : Filter.Tendsto (fun t => ∑ a ∈ B0 M F θ πbar s ap T0, (F.toPolicy (θ t) s) a)
      Filter.atTop (nhds 1))
    (hap0 : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) ap) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => (B0 M F θ πbar s ap T0).sup' hne (fun b => (θ t) (s, b)))
      Filter.atTop Filter.atTop := by
  classical
  set B : Finset A := B0 M F θ πbar s ap T0 with hB
  set MxB : ℕ → ℝ := fun t => B.sup' hne (fun b => (θ t) (s, b)) with hMxB
  have hcard : (0:ℝ) < (Fintype.card A) := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this
  -- for `t ≥ T`: `∑_{B0} π^{(t)}(a|s) ≤ |A| exp(MxB t - c) π^{(t)}(ap|s)`
  have hbound : ∀ t, T ≤ t →
      ∑ a ∈ B, (F.toPolicy (θ t) s) a
        ≤ (Fintype.card A) * (Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap) := by
    intro t ht
    have hterm : ∀ a ∈ B, (F.toPolicy (θ t) s) a
        ≤ Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap := by
      intro a ha
      have hratio : (F.toPolicy (θ t) s) a
          = Real.exp ((θ t) (s, a) - (θ t) (s, ap)) * (F.toPolicy (θ t) s) ap := by
        rw [hF, hF]; exact softmax_ratio (fun a' => (θ t) (s, a')) a ap
      have hle : (θ t) (s, a) - (θ t) (s, ap) ≤ MxB t - c := by
        have h1 : (θ t) (s, a) ≤ MxB t := Finset.le_sup' (fun b => (θ t) (s, b)) ha
        have h2 := hlow t ht
        linarith
      rw [hratio]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hle)
        ((F.toPolicy (θ t) s).nonneg ap)
    calc ∑ a ∈ B, (F.toPolicy (θ t) s) a
        ≤ ∑ _a ∈ B, Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap :=
          Finset.sum_le_sum hterm
      _ = (B.card : ℝ) * (Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card A) * (Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap) := by
          have hcle : (B.card : ℝ) ≤ (Fintype.card A : ℝ) := by
            exact_mod_cast Finset.card_le_univ B
          have hnn : (0:ℝ) ≤ Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap :=
            mul_nonneg (le_of_lt (Real.exp_pos _)) ((F.toPolicy (θ t) s).nonneg ap)
          exact mul_le_mul_of_nonneg_right hcle hnn
  -- eventually `∑_{B0} π^{(t)} ≥ 1/2`
  have hhalf : ∀ᶠ t in Filter.atTop, (1:ℝ)/2 ≤ ∑ a ∈ B, (F.toPolicy (θ t) s) a := by
    have : ((1:ℝ)/2) < 1 := by norm_num
    exact (hsum.eventually (eventually_gt_nhds this)).mono fun t ht => le_of_lt ht
  -- hence eventually `exp(MxB t - c) ≥ 1 / (2 |A| π^{(t)}(ap|s))`, which → ∞
  refine Filter.tendsto_atTop.mpr fun b => ?_
  -- pick `ε` so that `π^{(t)}(ap|s) ≤ ε` forces `MxB t ≥ b`
  set ε : ℝ := 1 / (2 * (Fintype.card A) * Real.exp (b - c)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεhalf : 0 < ε / 2 := by linarith
  have hevε : ∀ᶠ t in Filter.atTop, (F.toPolicy (θ t) s) ap < ε / 2 :=
    hap0.eventually (eventually_lt_nhds hεhalf)
  filter_upwards [hhalf, hevε, Filter.eventually_ge_atTop T] with t h1 h2 h3
  by_contra hcon
  push_neg at hcon
  -- `MxB t < b` gives `exp(MxB t - c) < exp(b - c)`
  have hexp : Real.exp (MxB t - c) ≤ Real.exp (b - c) :=
    Real.exp_le_exp.mpr (by linarith)
  have hb := hbound t h3
  have hπnn : (0:ℝ) ≤ (F.toPolicy (θ t) s) ap := (F.toPolicy (θ t) s).nonneg ap
  have hchain : (Fintype.card A : ℝ) * (Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap)
      ≤ (Fintype.card A : ℝ) * (Real.exp (b - c) * (ε / 2)) := by
    have hi : Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap
        ≤ Real.exp (b - c) * (ε / 2) := by
      calc Real.exp (MxB t - c) * (F.toPolicy (θ t) s) ap
          ≤ Real.exp (b - c) * (F.toPolicy (θ t) s) ap :=
            mul_le_mul_of_nonneg_right hexp hπnn
        _ ≤ Real.exp (b - c) * (ε / 2) :=
            mul_le_mul_of_nonneg_left (le_of_lt h2) (le_of_lt (Real.exp_pos _))

    exact mul_le_mul_of_nonneg_left hi (le_of_lt hcard)
  have hval : (Fintype.card A : ℝ) * (Real.exp (b - c) * (ε / 2)) = 1/4 := by
    have hexpne : Real.exp (b - c) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hcne : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt hcard
    have hkey : (2 * (Fintype.card A : ℝ) * Real.exp (b - c)) ≠ 0 := by positivity
    rw [hε]
    field_simp
    ring
  rw [hval] at hchain
  linarith


/-! ### AKM Lemma C.12 (`lemma:sum-bs-theta-1`): `∑_{a ∈ B0} θ^{(t)}(s,a) → ∞`

Each `a ∈ B0` satisfies `π^{(t)}(ap|s) < π^{(t)}(a|s)` for `t ≥ T0`, hence
`θ^{(t)}(s,ap) ≤ θ^{(t)}(s,a)` (`pi_le_iff_theta_le`), so `θ^{(t)}(s,a) ≥ c`.
The sum is therefore at least `max_{B0} θ + (|B0| - 1) c → ∞`. -/

theorem B0_theta_bounded_below (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (s : S) (ap : A) (T0 : ℕ) (c : ℝ) (T : ℕ)
    (hlow : ∀ t, T ≤ t → c ≤ (θ t) (s, ap))
    (a : A) (ha : a ∈ B0 M F θ πbar s ap T0) :
    ∀ t, max T T0 ≤ t → c ≤ (θ t) (s, a) := by
  intro t ht
  have hT : T ≤ t := le_trans (le_max_left _ _) ht
  have hT0 : T0 ≤ t := le_trans (le_max_right _ _) ht
  have hlt := (mem_B0.mp ha).2 t hT0
  have hθ : (θ t) (s, ap) ≤ (θ t) (s, a) :=
    (pi_le_iff_theta_le F hF (θ t) s ap a).mp (le_of_lt hlt)
  exact le_trans (hlow t hT) hθ

/-- **AKM Lemma C.12.** -/
theorem tendsto_sum_B0_theta_atTop (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (s : S) (ap : A) (T0 : ℕ) (c : ℝ) (T : ℕ)
    (hne : (B0 M F θ πbar s ap T0).Nonempty)
    (hlow : ∀ t, T ≤ t → c ≤ (θ t) (s, ap))
    (hmax : Filter.Tendsto
      (fun t => (B0 M F θ πbar s ap T0).sup' hne (fun b => (θ t) (s, b)))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun t => ∑ a ∈ B0 M F θ πbar s ap T0, (θ t) (s, a))
      Filter.atTop Filter.atTop := by
  classical
  set B : Finset A := B0 M F θ πbar s ap T0 with hB
  set MxB : ℕ → ℝ := fun t => B.sup' hne (fun b => (θ t) (s, b)) with hMxB
  -- for `t ≥ max T T0`: `∑_{B} θ ≥ MxB t + (|B| - 1) c`
  have hkey : ∀ t, max T T0 ≤ t →
      MxB t + ((B.card : ℝ) - 1) * c ≤ ∑ a ∈ B, (θ t) (s, a) := by
    intro t ht
    obtain ⟨b₀, hb₀mem, hb₀⟩ := Finset.exists_mem_eq_sup' hne (fun b => (θ t) (s, b))
    have hsplit : ∑ a ∈ B, (θ t) (s, a)
        = (θ t) (s, b₀) + ∑ a ∈ B.erase b₀, (θ t) (s, a) := by
      rw [← Finset.add_sum_erase _ (fun a => (θ t) (s, a)) hb₀mem]
    have hlowall : ∀ a ∈ B.erase b₀, c ≤ (θ t) (s, a) := by
      intro a ha
      exact B0_theta_bounded_below M F hF θ πbar s ap T0 c T hlow a
        (Finset.mem_of_mem_erase ha) t ht
    have hsum : ((B.card : ℝ) - 1) * c ≤ ∑ a ∈ B.erase b₀, (θ t) (s, a) := by
      have h1 : ∑ _a ∈ B.erase b₀, c ≤ ∑ a ∈ B.erase b₀, (θ t) (s, a) :=
        Finset.sum_le_sum hlowall
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hb₀mem] at h1
      have hc1 : 1 ≤ B.card := Finset.card_pos.mpr hne
      have hcast : ((B.card - 1 : ℕ) : ℝ) = (B.card : ℝ) - 1 := by
        push_cast [Nat.cast_sub hc1]; ring
      rwa [hcast] at h1
    rw [hsplit, hMxB]
    simp only [← hb₀]
    linarith
  refine Filter.tendsto_atTop.mpr fun b => ?_
  have hev := Filter.tendsto_atTop.mp hmax (b - ((B.card : ℝ) - 1) * c)
  filter_upwards [hev, Filter.eventually_ge_atTop (max T T0)] with t h1 h2
  have := hkey t h2
  linarith


/-! ### The final contradiction

`∑_a π^{(t)}(a|s) A^{(t)}(s,a) = 0` (`sum_pi_advInf_self`). Split `univ` as
`B0 ⊎ (I0 \ B0) ⊎ I+ ⊎ I-` and bound, with `Δ := A^{π̄}(s,ap) > 0`:

* every `a ∈ I+` has `A^{(t)}(s,a) > 0` eventually, so those terms are `≥ 0`;
* the `ap` term (`ap ∈ I+`) is `≥ π^{(t)}(ap|s) Δ/2`;
* `|∑_{I-} π^{(t)}(a|s) A^{(t)}(s,a)| ≤ π^{(t)}(ap|s) Δ/8` (bound (a));
* `|∑_{I0\B0} π^{(t)}(a|s) A^{(t)}(s,a)| ≤ π^{(t)}(ap|s) Δ/8` (bound (b)).

Hence `∑_{B0} π^{(t)}(a|s) A^{(t)}(s,a) ≤ -π^{(t)}(ap|s) Δ/4 < 0`. -/

/-- Split a sum over `univ` into `B0`, `I0 \ B0`, `I+`, `I-`. -/
theorem sum_split_B0 (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (s : S) (ap : A) (T0 : ℕ) (f : A → ℝ) :
    ∑ a, f a = (∑ a ∈ B0 M F θ πbar s ap T0, f a)
      + (∑ a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0, f a)
      + (∑ a ∈ Iplus M πbar s, f a) + (∑ a ∈ Iminus M πbar s, f a) := by
  classical
  have hI0 : ∑ a ∈ I0 M πbar s, f a
      = (∑ a ∈ B0 M F θ πbar s ap T0, f a)
        + (∑ a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0, f a) := by
    rw [add_comm]
    exact (Finset.sum_sdiff (B0_subset_I0)).symm
  rw [sum_split_three (M := M) (πbar := πbar) (s := s) f, hI0]

/-- The `I+` terms are eventually nonnegative, and the `ap` term dominates. -/
theorem Iplus_terms_lower (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (ap : A) (hap : 0 < advInf M πbar s ap) :
    ∀ᶠ t in Filter.atTop,
      (F.toPolicy (θ t) s) ap * (advInf M πbar s ap / 2)
        ≤ ∑ a ∈ Iplus M πbar s,
            (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a := by
  classical
  -- every `a ∈ I+` eventually has `A^{(t)}(s,a) ≥ A^{π̄}(s,a)/2 > 0`
  have hall : ∀ᶠ t in Filter.atTop, ∀ a : A, 0 < advInf M πbar s a →
      advInf M πbar s a / 2 ≤ advInf M (F.toPolicy (θ t)) s a := by
    refine (Filter.eventually_all (p := fun (a : A) t => 0 < advInf M πbar s a →
      advInf M πbar s a / 2 ≤ advInf M (F.toPolicy (θ t)) s a)).mpr ?_
    intro a
    by_cases hpos : 0 < advInf M πbar s a
    · exact (eventually_adv_pos M F hr hγ₀ hγ₁ θ πbar hlim s a hpos).mono
        fun t ht => fun _ => ht
    · exact Filter.Eventually.of_forall fun t hc => absurd hc hpos
  filter_upwards [hall] with t ht
  have hapmem : ap ∈ Iplus M πbar s := mem_Iplus.mpr hap
  have hnn : ∀ a ∈ Iplus M πbar s, (0:ℝ) ≤
      (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a := by
    intro a ha
    have hpos := mem_Iplus.mp ha
    have := ht a hpos
    exact mul_nonneg ((F.toPolicy (θ t) s).nonneg a) (by linarith)
  have hsingle : (F.toPolicy (θ t) s) ap * advInf M (F.toPolicy (θ t)) s ap
      ≤ ∑ a ∈ Iplus M πbar s,
          (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a :=
    Finset.single_le_sum hnn hapmem
  have hap' : (F.toPolicy (θ t) s) ap * (advInf M πbar s ap / 2)
      ≤ (F.toPolicy (θ t) s) ap * advInf M (F.toPolicy (θ t)) s ap :=
    mul_le_mul_of_nonneg_left (ht ap hap) ((F.toPolicy (θ t) s).nonneg ap)
  linarith


/-- **AKM's bound (a).** The `I⁻` contribution is negligible against
`π^{(t)}(ap|s)`: for `a ∈ I⁻`, `π^{(t)}(a|s)/π^{(t)}(ap|s) → 0`, and the
advantages are uniformly bounded by `2/(1-γ)`. -/
theorem Iminus_sum_small (M : FiniteMDP S A)
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
    (s : S) (ap : A) (hap : 0 < advInf M πbar s ap) (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ t in Filter.atTop,
      |∑ a ∈ Iminus M πbar s,
        (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a|
        ≤ (F.toPolicy (θ t) s) ap * κ := by
  classical
  have hposγ : 0 < 1 - M.γ := by linarith
  obtain ⟨c, T, hc⟩ := not_theta_atBot_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ θ hstep
    πbar hlim s ap hap
  set n : ℝ := (Fintype.card A : ℝ) with hn
  have hnpos : (0:ℝ) < n := by
    rw [hn]; have : 0 < Fintype.card A := Fintype.card_pos; exact_mod_cast this
  -- the per-action ratio target
  set ε : ℝ := κ * (1 - M.γ) / (2 * n) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- for each `a ∈ I-`: eventually `π^{(t)}(a|s) ≤ ε π^{(t)}(ap|s)`
  have hall : ∀ᶠ t in Filter.atTop, ∀ a : A, advInf M πbar s a < 0 →
      (F.toPolicy (θ t) s) a ≤ ε * (F.toPolicy (θ t) s) ap := by
    refine (Filter.eventually_all (p := fun (a : A) t => advInf M πbar s a < 0 →
      (F.toPolicy (θ t) s) a ≤ ε * (F.toPolicy (θ t) s) ap)).mpr ?_
    intro a
    by_cases hneg : advInf M πbar s a < 0
    · have hbot := theta_tendsto_atBot_of_adv_neg M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
        πbar hlim s a hneg ⟨ap, hap⟩
      exact (pi_ratio_small F hF θ s a ap c T hc hbot ε hεpos).mono fun t ht => fun _ => ht
    · exact Filter.Eventually.of_forall fun t hcon => absurd hcon hneg
  filter_upwards [hall] with t ht
  have hπnn : (0:ℝ) ≤ (F.toPolicy (θ t) s) ap := (F.toPolicy (θ t) s).nonneg ap
  -- bound each term by `ε π_ap · 2/(1-γ)`
  have hterm : ∀ a ∈ Iminus M πbar s,
      |(F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a|
        ≤ ε * (F.toPolicy (θ t) s) ap * (2 / (1 - M.γ)) := by
    intro a ha
    have hneg := mem_Iminus.mp ha
    have hπ := ht a hneg
    have hA : |advInf M (F.toPolicy (θ t)) s a| ≤ 2 / (1 - M.γ) :=
      abs_advInf_le M (F.toPolicy (θ t)) hr hγ₀ hγ₁ s a
    rw [abs_mul, abs_of_nonneg ((F.toPolicy (θ t) s).nonneg a)]
    have hεπ : (0:ℝ) ≤ ε * (F.toPolicy (θ t) s) ap := mul_nonneg (le_of_lt hεpos) hπnn
    calc (F.toPolicy (θ t) s) a * |advInf M (F.toPolicy (θ t)) s a|
        ≤ (ε * (F.toPolicy (θ t) s) ap) * |advInf M (F.toPolicy (θ t)) s a| :=
          mul_le_mul_of_nonneg_right hπ (abs_nonneg _)
      _ ≤ (ε * (F.toPolicy (θ t) s) ap) * (2 / (1 - M.γ)) :=
          mul_le_mul_of_nonneg_left hA hεπ
  have habs : |∑ a ∈ Iminus M πbar s,
      (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a|
      ≤ ∑ a ∈ Iminus M πbar s, (ε * (F.toPolicy (θ t) s) ap * (2 / (1 - M.γ))) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, nsmul_eq_mul] at habs
  refine le_trans habs ?_
  -- `|I-| ≤ n` and `n · ε · 2/(1-γ) = κ`
  have hcle : ((Iminus M πbar s).card : ℝ) ≤ n := by
    rw [hn]; exact_mod_cast Finset.card_le_univ _
  have hnn2 : (0:ℝ) ≤ ε * (F.toPolicy (θ t) s) ap * (2 / (1 - M.γ)) := by
    have : (0:ℝ) ≤ ε * (F.toPolicy (θ t) s) ap := mul_nonneg (le_of_lt hεpos) hπnn
    positivity
  calc ((Iminus M πbar s).card : ℝ) * (ε * (F.toPolicy (θ t) s) ap * (2 / (1 - M.γ)))
      ≤ n * (ε * (F.toPolicy (θ t) s) ap * (2 / (1 - M.γ))) :=
        mul_le_mul_of_nonneg_right hcle hnn2
    _ ≤ (F.toPolicy (θ t) s) ap * κ := by
        rw [hε]
        have hne : (2 * n) ≠ 0 := by positivity
        have hγne : (1 - M.γ) ≠ 0 := ne_of_gt hposγ
        have heq : n * (κ * (1 - M.γ) / (2 * n) * (F.toPolicy (θ t) s) ap
            * (2 / (1 - M.γ))) = (F.toPolicy (θ t) s) ap * κ := by
          field_simp
        rw [heq]


/-- **AKM's bound (b).** The `I⁰ \ B0` contribution is negligible: those actions
are eventually dominated by `ap` in probability (`B0bar_dominated`) while their
trajectory advantages vanish (`I0_adv_small`). -/
theorem B0bar_sum_small (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (s : S) (ap : A) (T0 : ℕ)
    (hΔ : 0 < advInf M πbar s ap)
    (hT0ap : ∀ t, T0 ≤ t → advInf M πbar s ap / 2 ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hT0ord : ∀ a, advInf M πbar s a ≤ 0 → ∀ t, T0 ≤ t →
      advInf M (F.toPolicy (θ t)) s a ≤ advInf M (F.toPolicy (θ t)) s ap)
    (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ t in Filter.atTop,
      |∑ a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0,
        (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a|
        ≤ (F.toPolicy (θ t) s) ap * κ := by
  classical
  set n : ℝ := (Fintype.card A : ℝ) with hn
  have hnpos : (0:ℝ) < n := by
    rw [hn]; have : 0 < Fintype.card A := Fintype.card_pos; exact_mod_cast this
  set ε : ℝ := κ / n with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- for each `a ∈ I0 \ B0`: eventually `π^{(t)}(a|s) ≤ π^{(t)}(ap|s)` and `|A^{(t)}| ≤ ε`
  have hall : ∀ᶠ t in Filter.atTop, ∀ a : A,
      a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0 →
      (F.toPolicy (θ t) s) a ≤ (F.toPolicy (θ t) s) ap ∧
      |advInf M (F.toPolicy (θ t)) s a| ≤ ε := by
    refine (Filter.eventually_all (p := fun (a : A) t =>
      a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0 →
      (F.toPolicy (θ t) s) a ≤ (F.toPolicy (θ t) s) ap ∧
      |advInf M (F.toPolicy (θ t)) s a| ≤ ε)).mpr ?_
    intro a
    by_cases hmem : a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0
    · have ha0 : advInf M πbar s a = 0 := mem_I0.mp (Finset.mem_sdiff.mp hmem).1
      have haB : a ∉ B0 M F θ πbar s ap T0 := (Finset.mem_sdiff.mp hmem).2
      obtain ⟨Ta, hTa⟩ := B0bar_dominated M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep πbar s ap T0
        hΔ hT0ap hT0ord a ha0 haB
      have hadv := I0_adv_small M F hr hγ₀ hγ₁ θ πbar hlim s a ha0 ε hεpos
      filter_upwards [hadv, Filter.eventually_ge_atTop Ta] with t h1 h2
      exact fun _ => ⟨hTa t h2, h1⟩
    · exact Filter.Eventually.of_forall fun t hcon => absurd hcon hmem
  filter_upwards [hall] with t ht
  have hπnn : (0:ℝ) ≤ (F.toPolicy (θ t) s) ap := (F.toPolicy (θ t) s).nonneg ap
  have hterm : ∀ a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0,
      |(F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a|
        ≤ (F.toPolicy (θ t) s) ap * ε := by
    intro a ha
    obtain ⟨hπ, hA⟩ := ht a ha
    rw [abs_mul, abs_of_nonneg ((F.toPolicy (θ t) s).nonneg a)]
    calc (F.toPolicy (θ t) s) a * |advInf M (F.toPolicy (θ t)) s a|
        ≤ (F.toPolicy (θ t) s) ap * |advInf M (F.toPolicy (θ t)) s a| :=
          mul_le_mul_of_nonneg_right hπ (abs_nonneg _)
      _ ≤ (F.toPolicy (θ t) s) ap * ε := mul_le_mul_of_nonneg_left hA hπnn
  have habs := le_trans (Finset.abs_sum_le_sum_abs
    (fun a => (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)
    (I0 M πbar s \ B0 M F θ πbar s ap T0)) (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, nsmul_eq_mul] at habs
  refine le_trans habs ?_
  have hcle : (((I0 M πbar s \ B0 M F θ πbar s ap T0).card : ℝ)) ≤ n := by
    rw [hn]; exact_mod_cast Finset.card_le_univ _
  have hnn2 : (0:ℝ) ≤ (F.toPolicy (θ t) s) ap * ε := mul_nonneg hπnn (le_of_lt hεpos)
  calc (((I0 M πbar s \ B0 M F θ πbar s ap T0).card : ℝ)) * ((F.toPolicy (θ t) s) ap * ε)
      ≤ n * ((F.toPolicy (θ t) s) ap * ε) := mul_le_mul_of_nonneg_right hcle hnn2
    _ = (F.toPolicy (θ t) s) ap * κ := by
        rw [hε]
        field_simp


/-- **The final inequality.** Combining bounds (a), (b), (c) with
`∑_a π^{(t)}(a|s) A^{(t)}(s,a) = 0` gives
`∑_{a ∈ B0} π^{(t)}(a|s) A^{(t)}(s,a) ≤ -π^{(t)}(ap|s) · Δ/4 < 0` eventually. -/
theorem sum_B0_pi_adv_neg (M : FiniteMDP S A)
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
    (s : S) (ap : A) (T0 : ℕ)
    (hΔ : 0 < advInf M πbar s ap)
    (hT0ap : ∀ t, T0 ≤ t → advInf M πbar s ap / 2 ≤ advInf M (F.toPolicy (θ t)) s ap)
    (hT0ord : ∀ a, advInf M πbar s a ≤ 0 → ∀ t, T0 ≤ t →
      advInf M (F.toPolicy (θ t)) s a ≤ advInf M (F.toPolicy (θ t)) s ap) :
    ∀ᶠ t in Filter.atTop,
      ∑ a ∈ B0 M F θ πbar s ap T0,
        (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a
        ≤ - ((F.toPolicy (θ t) s) ap * (advInf M πbar s ap / 8)) := by
  classical
  set Δ : ℝ := advInf M πbar s ap with hΔdef
  have hκ : (0:ℝ) < Δ / 8 := by rw [hΔdef]; linarith
  have hminus := Iminus_sum_small M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim
    s ap hΔ (Δ / 8) hκ
  have hbar := B0bar_sum_small M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep πbar hlim s ap T0
    hΔ hT0ap hT0ord (Δ / 8) hκ
  have hplus := Iplus_terms_lower M F hr hγ₀ hγ₁ θ πbar hlim s ap hΔ
  filter_upwards [hminus, hbar, hplus] with t h1 h2 h3
  -- the total is zero
  have htot : ∑ a, (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a = 0 := by
    have := sum_pi_advInf_self M hr hγ₀ hγ₁ (F.toPolicy (θ t)) s
    exact this
  rw [sum_split_B0 M F θ πbar s ap T0
    (fun a => (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)] at htot
  have hb1 := (abs_le.mp h1).1
  have hb2 := (abs_le.mp h2).1
  -- name the four blocks and the scale
  set P : ℝ := (F.toPolicy (θ t) s) ap with hP
  set SB : ℝ := ∑ a ∈ B0 M F θ πbar s ap T0,
    (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a with hSB
  set SR : ℝ := ∑ a ∈ I0 M πbar s \ B0 M F θ πbar s ap T0,
    (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a with hSR
  set SP : ℝ := ∑ a ∈ Iplus M πbar s,
    (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a with hSP
  set SM : ℝ := ∑ a ∈ Iminus M πbar s,
    (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a with hSM
  -- `hb1 : -(P * (Δ/8)) ≤ SM`, `hb2 : -(P * (Δ/8)) ≤ SR`, `h3 : P * (Δ/2) ≤ SP`
  -- `htot : SB + SR + SP + SM = 0`
  have h3' : P * (Δ / 2) ≤ SP := by rw [hΔdef]; exact h3
  have hPnn : (0:ℝ) ≤ P := (F.toPolicy (θ t) s).nonneg ap
  have hPΔ : (0:ℝ) ≤ P * Δ := mul_nonneg hPnn (le_of_lt (by rw [hΔdef]; exact hΔ))
  have e2 : P * (Δ / 2) = (P * Δ) / 2 := by ring
  have e8 : P * (Δ / 8) = (P * Δ) / 8 := by ring
  rw [e2] at h3'
  rw [e8] at hb1 hb2 ⊢
  linarith [hb1, hb2, h3', htot, hPΔ]

/-- The trajectory `∑_{a ∈ B0} θ^{(t)}(s,a)` is eventually strictly decreasing
when the `B0` gradient block sums negative. -/
theorem sum_B0_theta_antitone (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (B : Finset A) (T : ℕ)
    (hneg : ∀ t, T ≤ t → ∑ a ∈ B,
      (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a ≤ 0) :
    ∀ t, T ≤ t → ∑ a ∈ B, (θ t) (s, a) ≤ ∑ a ∈ B, (θ T) (s, a) := by
  classical
  have hsteple : ∀ t, T ≤ t →
      ∑ a ∈ B, (θ (t + 1)) (s, a) ≤ ∑ a ∈ B, (θ t) (s, a) := by
    intro t ht
    have hco : ∀ a ∈ B, (θ (t + 1)) (s, a)
        = (θ t) (s, a) + η * (dinfDist M (F.toPolicy (θ t)) μ s
            * ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)) := by
      intro a _
      rw [hstep t]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [gradient_VinfDist_apply M F hF hr hγ₀ hγ₁ μ (θ t) s a]
    rw [Finset.sum_congr rfl hco, Finset.sum_add_distrib]
    have hfac : ∑ a ∈ B, η * (dinfDist M (F.toPolicy (θ t)) μ s
        * ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a))
        = (η * dinfDist M (F.toPolicy (θ t)) μ s)
          * ∑ a ∈ B, (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [hfac]
    have hdnn : 0 ≤ dinfDist M (F.toPolicy (θ t)) μ s := dinfDist_nonneg M hγ₀ _ _ _
    have hcnn : (0:ℝ) ≤ η * dinfDist M (F.toPolicy (θ t)) μ s :=
      mul_nonneg (le_of_lt hη₀) hdnn
    have := mul_nonpos_of_nonneg_of_nonpos hcnn (hneg t ht)
    linarith
  exact antitone_from (u := fun t => ∑ a ∈ B, (θ t) (s, a)) hsteple


/-! ## The residual goal

Assembling: assume the goal fails at `(s, ap)`. Then `A^{π̄}(s,ap) > 0` and
`π̄(ap|s) = 0`, so:

* `θ^{(t)}(s,ap) ≥ c` for `t ≥ T` (`not_theta_atBot_of_adv_pos`);
* `π^{(t)}(ap|s) → 0` (`tendsto_pi_coord` with `π̄(ap|s) = 0`);
* choose `T0` (`exists_T0`), form `B0`, get `∑_{B0} π^{(t)} → 1`
  (`sum_B0_pi_tendsto_one`), `B0 ≠ ∅`, `max_{B0} θ → ∞`
  (`tendsto_max_B0_theta_atTop`) and `∑_{B0} θ^{(t)}(s,·) → ∞`
  (`tendsto_sum_B0_theta_atTop`);
* but `∑_{B0} π^{(t)} A^{(t)} < 0` eventually (`sum_B0_pi_adv_neg`), so
  `∑_{B0} θ^{(t)}(s,·)` is eventually **bounded above** by its value at that
  time (`sum_B0_theta_antitone`) — contradiction. -/

theorem limit_adv_nonpos_offsupport_proof (M : FiniteMDP S A)
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
    ∀ s a, (πbar s) a = 0 → advInf M πbar s a ≤ 0 := by
  classical
  intro s ap _hzero
  by_contra hcon
  push_neg at hcon
  -- `hcon : 0 < advInf M πbar s ap`
  -- `θ^{(t)}(s,ap)` is bounded below from some `T` on
  obtain ⟨c, T, hc⟩ := not_theta_atBot_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ θ hstep
    πbar hlim s ap hcon
  -- `π^{(t)}(ap|s) → 0`
  have hbar : (πbar s) ap =
      0 := tendsto_pi_zero_of_adv_pos M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
    πbar hlim s ap hcon
  have hap0 : Filter.Tendsto (fun t => (F.toPolicy (θ t) s) ap) Filter.atTop (nhds 0) := by
    have := tendsto_pi_coord F θ πbar hlim s ap
    rwa [hbar] at this
  -- the threshold time
  obtain ⟨T0, hT0ap, hT0ord⟩ :=
    exists_T0 M F hr hγ₀ hγ₁ θ πbar hlim s ap hcon
  -- mass concentrates on `B0`
  have hsum := sum_B0_pi_tendsto_one M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim
    s ap T0 hcon hT0ap hT0ord hap0
  have hne := B0_nonempty M F θ πbar s ap T0 hsum
  have hmax := tendsto_max_B0_theta_atTop M F hF θ πbar s ap T0 c T hne hc hsum hap0
  have hdiv := tendsto_sum_B0_theta_atTop M F hF θ πbar s ap T0 c T hne hc hmax
  -- but the `B0` block of the gradient is eventually negative
  have hneg := sum_B0_pi_adv_neg M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep πbar hlim
    s ap T0 hcon hT0ap hT0ord
  obtain ⟨T2, hT2⟩ := hneg.exists_forall_of_atTop
  have hnonpos : ∀ t, T2 ≤ t → ∑ a ∈ B0 M F θ πbar s ap T0,
      (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a ≤ 0 := by
    intro t ht
    have h := hT2 t ht
    have hnn : (0:ℝ) ≤ (F.toPolicy (θ t) s) ap * (advInf M πbar s ap / 8) :=
      mul_nonneg ((F.toPolicy (θ t) s).nonneg ap) (by linarith)
    linarith
  -- so `∑_{B0} θ^{(t)}(s,·)` is bounded above from `T2` on
  have hbdd := sum_B0_theta_antitone M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s
    (B0 M F θ πbar s ap T0) T2 hnonpos
  -- contradiction with divergence
  obtain ⟨t, ht1, ht2⟩ := ((Filter.tendsto_atTop.mp hdiv
    (∑ a ∈ B0 M F θ πbar s ap T0, (θ T2) (s, a) + 1)).and
    (Filter.eventually_ge_atTop T2)).exists
  have := hbdd t ht2
  linarith


end ResidFinal

end Proofs
end PolicyGradient
