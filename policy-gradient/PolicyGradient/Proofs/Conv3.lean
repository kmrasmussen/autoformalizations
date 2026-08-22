/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv2

/-!
# Conv3 — `Goal.softmax_policy_converges`: the tie split, closed for `γ = 0`

Work in progress header; see the end of the file for the obstruction note.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv3

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **A relaxation of `tie_gap_monotone`.**  The exact-tie hypothesis is not
needed: it suffices that the *ahead* action's advantage dominates the *behind*
action's, and that the behind action's advantage is nonnegative. -/
theorem gap_monotone_of_adv_dominates (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a b : A) (t : ℕ)
    (hdom : advInf M (F.toPolicy (θ t)) s b ≤ advInf M (F.toPolicy (θ t)) s a)
    (hBnn : 0 ≤ advInf M (F.toPolicy (θ t)) s b)
    (hge : (θ t) (s, b) ≤ (θ t) (s, a)) :
    (θ t) (s, a) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a) - (θ (t + 1)) (s, b) := by
  have hda := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a
  have hdb := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s b
  have hdnn : 0 ≤ dinfDist M (F.toPolicy (θ t)) μ s := dinfDist_nonneg M hγ₀ _ _ _
  have hpi : (F.toPolicy (θ t) s) b ≤ (F.toPolicy (θ t) s) a := by
    rw [hF, hF]; exact softmax_mono _ a b hge
  have hpb : 0 ≤ (F.toPolicy (θ t) s) b := (F.toPolicy (θ t) s).nonneg b
  -- `π a * A a ≥ π a * A b ≥ π b * A b`
  have hkey : (F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b
      ≤ (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a := by
    have h1 : (F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b
        ≤ (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s b :=
      mul_le_mul_of_nonneg_right hpi hBnn
    have h2 : (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s b
        ≤ (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a :=
      mul_le_mul_of_nonneg_left hdom ((F.toPolicy (θ t) s).nonneg a)
    linarith
  have hprod : 0 ≤ η * (dinfDist M (F.toPolicy (θ t)) μ s
      * ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a
          - (F.toPolicy (θ t) s) b * advInf M (F.toPolicy (θ t)) s b)) :=
    mul_nonneg hη₀.le (mul_nonneg hdnn (by linarith))
  nlinarith [hda, hdb, hprod]

/-! ## `γ = 0`: the tie split closes

At `γ = 0` the advantage is `A^{(t)}(s,a) = r(s,a) - V^{(t)}(s)`, so **the
difference of two advantages at a state is the fixed reward difference**,
independent of `t`.  Two actions whose limiting advantages both vanish therefore
have *equal* rewards, hence *equal* advantages at every finite time — the exact
tie `tie_gap_monotone` needs, with no reward-tie hypothesis on `M`.  And that
common advantage is `≥ 0` because `V^{(t)}(s)` increases to its limit. -/

/-- At `γ = 0`, `advInf M π s a = r(s,a) - Vinf M π s`. -/
theorem advInf_gamma_zero (M : FiniteMDP S A) (hγ : M.γ = 0) (π : Policy S A)
    (s : S) (a : A) : advInf M π s a = M.r s a - Vinf M π s := by
  simp [advInf, hγ]

/-- At `γ = 0` the advantage difference is the reward difference, at every `t`. -/
theorem advInf_sub_gamma_zero (M : FiniteMDP S A) (hγ : M.γ = 0) (π : Policy S A)
    (s : S) (a b : A) :
    advInf M π s a - advInf M π s b = M.r s a - M.r s b := by
  rw [advInf_gamma_zero M hγ, advInf_gamma_zero M hγ]; ring

/-- **At `γ = 0`, two actions with vanishing limiting advantage are exactly tied
at every finite time.** -/
theorem adv_eq_of_both_zero_limit_gamma_zero (M : FiniteMDP S A) (hγ : M.γ = 0)
    (π : ℕ → Policy S A) (s : S) (a b : A)
    (ha : Tendsto (fun t => advInf M (π t) s a) atTop (nhds 0))
    (hb : Tendsto (fun t => advInf M (π t) s b) atTop (nhds 0)) :
    ∀ t, advInf M (π t) s a = advInf M (π t) s b := by
  have hconst : ∀ t, advInf M (π t) s a - advInf M (π t) s b = M.r s a - M.r s b :=
    fun t => advInf_sub_gamma_zero M hγ (π t) s a b
  have hlim : Tendsto (fun t => advInf M (π t) s a - advInf M (π t) s b) atTop
      (nhds (0 - 0)) := ha.sub hb
  rw [sub_zero] at hlim
  have hcst : Tendsto (fun _ : ℕ => M.r s a - M.r s b) atTop (nhds 0) :=
    hlim.congr hconst
  have : M.r s a - M.r s b = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hcst
  intro t
  have := hconst t
  linarith

/-- **At `γ = 0`, an action with vanishing limiting advantage has nonnegative
advantage at every time**: `A^{(t)}(s,a) = r(s,a) - V^{(t)}(s)` and `V^{(t)}(s)`
is monotone increasing, so `A^{(t)}(s,a)` is antitone with limit `0`. -/
theorem adv_nonneg_of_zero_limit_gamma_zero (M : FiniteMDP S A) (hγ : M.γ = 0)
    (π : ℕ → Policy S A) (s : S) (a : A)
    (hmono : Monotone (fun t => Vinf M (π t) s))
    (ha : Tendsto (fun t => advInf M (π t) s a) atTop (nhds 0)) :
    ∀ t, 0 ≤ advInf M (π t) s a := by
  intro t
  have hanti : Antitone (fun t => advInf M (π t) s a) := by
    intro i j hij
    simp only [advInf_gamma_zero M hγ]
    have := hmono hij
    simp only at this ⊢
    linarith
  -- an antitone sequence with limit `0` is `≥ 0`
  exact le_of_tendsto ha (Filter.eventually_atTop.mpr ⟨t, fun n hn => hanti hn⟩)

/-! ## Assembling a state from a monotone top action

The abstract engine: at a state `s`, suppose the actions in a set `Z` are led by
`a₀ ∈ Z` at time `T`, that each gap `θ(s,a₀) - θ(s,b)` (`b ∈ Z`) never shrinks
while it is nonnegative, and that every action outside `Z` loses all its mass.
Then **every** coordinate at `s` converges.

The mechanism is `softmax_ratio`: `π_t(b|s) = exp(θ_t(s,b) - θ_t(s,a₀)) π_t(a₀|s)`,
and the exponential factor is a nonincreasing sequence in `(0,1]`, hence
convergent.  Summing over `Z` and using `∑_{b ∈ Z} π_t(b|s) → 1` pins
`π_t(a₀|s)` down, and every other coordinate follows. -/

/-- The gaps to a leading action are nonnegative and nondecreasing from `T` on. -/
theorem gap_nonneg_of_step (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S) (a₀ b : A)
    (T : ℕ) (hT : (θ T) (s, b) ≤ (θ T) (s, a₀))
    (hstepgap : ∀ t, T ≤ t → (θ t) (s, b) ≤ (θ t) (s, a₀) →
      (θ t) (s, a₀) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a₀) - (θ (t + 1)) (s, b)) :
    ∀ t, T ≤ t → (θ t) (s, b) ≤ (θ t) (s, a₀) ∧
      (θ T) (s, a₀) - (θ T) (s, b) ≤ (θ t) (s, a₀) - (θ t) (s, b) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨hT, le_refl _⟩
  | succ n hn ih =>
      obtain ⟨hle, hgap⟩ := ih
      have h := hstepgap n hn hle
      exact ⟨by linarith, by linarith⟩

/-- The gap sequence is monotone from `T` on, hence the ratio
`exp(θ_t(s,b) - θ_t(s,a₀))` is antitone in `(0,1]` and converges. -/
theorem exists_ratio_limit (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S) (a₀ b : A)
    (T : ℕ) (hT : (θ T) (s, b) ≤ (θ T) (s, a₀))
    (hstepgap : ∀ t, T ≤ t → (θ t) (s, b) ≤ (θ t) (s, a₀) →
      (θ t) (s, a₀) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a₀) - (θ (t + 1)) (s, b)) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ 1 ∧
      Tendsto (fun t => Real.exp ((θ t) (s, b) - (θ t) (s, a₀))) atTop (nhds ρ) := by
  have hord := gap_nonneg_of_step θ s a₀ b T hT hstepgap
  -- the exponential is bounded in `(0, 1]` from `T` on, and antitone there
  set f : ℕ → ℝ := fun t => Real.exp ((θ t) (s, b) - (θ t) (s, a₀)) with hf
  have hpos : ∀ t, 0 < f t := fun t => Real.exp_pos _
  have hanti : ∀ t, T ≤ t → f (t + 1) ≤ f t := by
    intro t ht
    have hle := (hord t ht).1
    have h := hstepgap t ht hle
    exact Real.exp_le_exp.mpr (by linarith)
  -- shift to `T` so the sequence is antitone outright
  set g : ℕ → ℝ := fun k => f (T + k) with hg
  have hganti : Antitone g := by
    refine antitone_nat_of_succ_le fun k => ?_
    have := hanti (T + k) (Nat.le_add_right T k)
    simpa [hg, ← Nat.add_assoc] using this
  have hgbdd : BddBelow (Set.range g) := ⟨0, by rintro x ⟨k, rfl⟩; exact (hpos _).le⟩
  obtain ⟨ρ, hρg⟩ : ∃ ρ : ℝ, Tendsto g atTop (nhds ρ) :=
    ⟨_, tendsto_atTop_ciInf hganti hgbdd⟩
  have hρ : Tendsto f atTop (nhds ρ) :=
    (Filter.tendsto_add_atTop_iff_nat (f := f) T).mp (by simpa [hg, add_comm] using hρg)
  refine ⟨ρ, ge_of_tendsto hρ (Filter.Eventually.of_forall (fun t => (hpos t).le)), ?_, hρ⟩
  have hb1 : ∀ t, T ≤ t → f t ≤ 1 := by
    intro t ht
    exact Real.exp_le_one_iff.mpr (by linarith [(hord t ht).1])
  exact le_of_tendsto hρ (Filter.eventually_atTop.mpr ⟨T, hb1⟩)


/-- **The state assembly.**  If every action in `Z` trails a fixed leader `a₀ ∈ Z`
with a never-shrinking gap from time `T` on, and every action outside `Z` loses
its mass, then every policy coordinate at `s` converges. -/
theorem coord_tendsto_of_leader
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → EuclideanSpace ℝ (S × A)) (s : S) (Z : Finset A) (a₀ : A)
    (ha₀ : a₀ ∈ Z) (T : ℕ)
    (hT : ∀ b ∈ Z, (θ T) (s, b) ≤ (θ T) (s, a₀))
    (hstepgap : ∀ b ∈ Z, ∀ t, T ≤ t → (θ t) (s, b) ≤ (θ t) (s, a₀) →
      (θ t) (s, a₀) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a₀) - (θ (t + 1)) (s, b))
    (hout : ∀ b ∉ Z, Tendsto (fun t => (F.toPolicy (θ t) s) b) atTop (nhds 0)) :
    ∀ a, ∃ L : ℝ, Tendsto (fun t => (F.toPolicy (θ t) s) a) atTop (nhds L) := by
  classical
  -- ratio limits
  have hratio : ∀ b ∈ Z, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ 1 ∧
      Tendsto (fun t => Real.exp ((θ t) (s, b) - (θ t) (s, a₀))) atTop (nhds ρ) :=
    fun b hb => exists_ratio_limit θ s a₀ b T (hT b hb) (hstepgap b hb)
  choose ρ hρ0 hρ1 hρlim using hratio
  -- the softmax ratio identity
  have hid : ∀ (t : ℕ) (b : A), (F.toPolicy (θ t) s) b
      = Real.exp ((θ t) (s, b) - (θ t) (s, a₀)) * (F.toPolicy (θ t) s) a₀ := by
    intro t b
    rw [hF, hF]
    exact softmax_ratio (fun a' => (θ t) (s, a')) b a₀
  -- `R := ∑_{b ∈ Z} ρ b ≥ 1 > 0`, since the `a₀` term is `1`
  set R : ℝ := ∑ b ∈ Z.attach, ρ b.1 b.2 with hR
  have hRlim : Tendsto (fun t => ∑ b ∈ Z.attach,
      Real.exp ((θ t) (s, b.1) - (θ t) (s, a₀))) atTop (nhds R) :=
    tendsto_finsetSum _ (fun b _ => hρlim b.1 b.2)
  have hρa₀ : ρ a₀ ha₀ = 1 := by
    have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds (ρ a₀ ha₀)) := by
      refine (hρlim a₀ ha₀).congr (fun t => ?_)
      simp
    exact (tendsto_nhds_unique tendsto_const_nhds hc).symm
  have hRpos : 0 < R := by
    have hmem : (⟨a₀, ha₀⟩ : {x // x ∈ Z}) ∈ Z.attach := Finset.mem_attach _ _
    have hle : ρ a₀ ha₀ ≤ R := by
      refine Finset.single_le_sum (f := fun b : {x // x ∈ Z} => ρ b.1 b.2) ?_ hmem
      intro b _; exact hρ0 b.1 b.2
    rw [hρa₀] at hle; linarith
  -- mass on `Z` tends to `1`
  have hmass : Tendsto (fun t => ∑ b ∈ Z, (F.toPolicy (θ t) s) b) atTop (nhds 1) :=
    tendsto_mass_on_zero_set (fun t => F.toPolicy (θ t)) s Z hout
  -- rewrite the mass as `(∑ ratios) * π_t(a₀|s)`
  have hmass' : Tendsto (fun t => (∑ b ∈ Z.attach,
      Real.exp ((θ t) (s, b.1) - (θ t) (s, a₀))) * (F.toPolicy (θ t) s) a₀)
      atTop (nhds 1) := by
    refine hmass.congr (fun t => ?_)
    rw [Finset.sum_mul, ← Finset.sum_attach Z (fun b => (F.toPolicy (θ t) s) b)]
    exact Finset.sum_congr rfl (fun b _ => hid t b.1)
  -- divide out
  have ha₀lim : Tendsto (fun t => (F.toPolicy (θ t) s) a₀) atTop (nhds (1 / R)) := by
    have hdiv := hmass'.div hRlim (ne_of_gt hRpos)
    refine hdiv.congr' ?_
    filter_upwards [hRlim.eventually (eventually_gt_nhds hRpos)] with t ht
    exact mul_div_cancel_left₀ _ (ne_of_gt ht)
  intro a
  by_cases haZ : a ∈ Z
  · refine ⟨ρ a haZ * (1 / R), ?_⟩
    exact ((hρlim a haZ).mul ha₀lim).congr (fun t => (hid t a).symm)
  · exact ⟨0, hout a haZ⟩

/-! ## `γ = 0`: the frozen goal, unconditionally

At `γ = 0` every hypothesis of `coord_tendsto_of_leader` is available:

* `Z s := {a | A^{(t)}(s,a) → 0}` — `exists_adv_tendsto` gives the limits, and
  `tendsto_pi_zero_of_adv_limit_ne` sends every coordinate outside `Z s` to `0`;
* actions in `Z s` are **exactly tied at every finite time**
  (`adv_eq_of_both_zero_limit_gamma_zero`) with **nonnegative** common advantage
  (`adv_nonneg_of_zero_limit_gamma_zero`, from monotonicity of `V^{(t)}(s)`);
* so `gap_monotone_of_adv_dominates` applies to any pair in `Z s`, in particular
  to a leader `a₀` chosen to maximise `θ_T(s,·)` over `Z s` at any fixed `T`.
-/

/-- Choice of a leader: a maximiser of a real function over a nonempty finset. -/
theorem exists_leader (Z : Finset A) (hZ : Z.Nonempty) (f : A → ℝ) :
    ∃ a₀ ∈ Z, ∀ b ∈ Z, f b ≤ f a₀ := by
  obtain ⟨a₀, ha₀, hmax⟩ := Z.exists_max_image f hZ
  exact ⟨a₀, ha₀, hmax⟩

/-- **`Goal.softmax_policy_converges` for `γ = 0`, unconditionally.** -/
theorem softmax_policy_converges_gamma_zero (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ : M.γ = 0)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) := by
  classical
  have hγ₀ : 0 ≤ M.γ := hγ.ge
  have hγ₁ : M.γ < 1 := by rw [hγ]; norm_num
  refine exists_policy_limit_of_coord_tendsto (fun t => F.toPolicy (θ t)) ?_
  -- limits of the advantages
  choose Abar hAbar using exists_adv_tendsto M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep
  intro s
  set Z : Finset A := {a | Abar s a = 0} with hZdef
  have hmemZ : ∀ a, a ∈ Z ↔ Abar s a = 0 := by intro a; simp [hZdef]
  -- outside `Z`, the coordinate dies
  have hout : ∀ b ∉ Z, Tendsto (fun t => (F.toPolicy (θ t) s) b) atTop (nhds 0) := by
    intro b hb
    exact tendsto_pi_zero_of_adv_limit_ne M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
      s b (Abar s b) (fun h => hb ((hmemZ b).mpr h)) (hAbar s b)
  -- inside `Z`: advantages vanish in the limit
  have hzero : ∀ b ∈ Z, Tendsto (fun t => advInf M (F.toPolicy (θ t)) s b) atTop (nhds 0) := by
    intro b hb
    have := hAbar s b
    rwa [(hmemZ b).mp hb] at this
  -- `Z` is nonempty: otherwise all coordinates die, contradicting the mass identity
  have hZne : Z.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hmass := tendsto_mass_on_zero_set (fun t => F.toPolicy (θ t)) s Z
      (fun b hb => hout b hb)
    rw [hemp] at hmass
    simp only [Finset.sum_empty] at hmass
    exact absurd (tendsto_nhds_unique tendsto_const_nhds hmass) (by norm_num)
  -- the exact tie and its nonnegativity
  have hVmono : ∀ s', Monotone (fun t => Vinf M (F.toPolicy (θ t)) s') :=
    fun s' => exists_Vinf_limit M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep s'
  have hnn : ∀ b ∈ Z, ∀ t, 0 ≤ advInf M (F.toPolicy (θ t)) s b := by
    intro b hb
    exact adv_nonneg_of_zero_limit_gamma_zero M hγ (fun t => F.toPolicy (θ t)) s b
      (hVmono s) (hzero b hb)
  have htie : ∀ a ∈ Z, ∀ b ∈ Z, ∀ t,
      advInf M (F.toPolicy (θ t)) s a = advInf M (F.toPolicy (θ t)) s b := by
    intro a ha b hb
    exact adv_eq_of_both_zero_limit_gamma_zero M hγ (fun t => F.toPolicy (θ t)) s a b
      (hzero a ha) (hzero b hb)
  -- pick the leader at time `0`
  obtain ⟨a₀, ha₀, hmax⟩ := exists_leader Z hZne (fun a => (θ 0) (s, a))
  refine coord_tendsto_of_leader F hF θ s Z a₀ ha₀ 0 hmax ?_ hout
  intro b hb t _ hle
  refine gap_monotone_of_adv_dominates M F hF hr hγ₀ hγ₁ μ η hη₀ θ hstep s a₀ b t
    (le_of_eq (htie b hb a₀ ha₀ t)) (hnn b hb t) hle

end Conv3

end Proofs
end PolicyGradient
