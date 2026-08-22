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


end Conv3

end Proofs
end PolicyGradient
