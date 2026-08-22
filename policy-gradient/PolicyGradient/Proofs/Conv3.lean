/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv2

/-!
# Conv3 — `Goal.softmax_policy_converges`: closed for `γ = 0`, open for `γ > 0`

## Status

The goal is **PROVED for `γ = 0`** — `softmax_policy_converges_gamma_zero`, the
frozen statement verbatim, with no hypothesis on `M` beyond the frozen ones — and
**OPEN for `γ > 0`**, with the obstruction reduced to a single, quantified
hypothesis and its failure explained by a closed-form identity `(‡)`.

Read `Conv2.lean`'s header first: it refutes the `∑ ‖θ_{t+1} - θ_t‖ < ∞` route
with a closed form, and reduces the goal to the *tie split* — convergence of the
policy coordinates whose limiting advantage vanishes.  This file attacks that
split and closes it at `γ = 0`.

## 1. The engine: a leading tied action assembles a whole state

`coord_tendsto_of_leader` is the new analytic core, and it is πbar-free.  Fix a
state `s` and a set `Z` of actions.  Suppose

* every action outside `Z` loses its mass (`π_t(b|s) → 0`), and
* some `a₀ ∈ Z` **leads** the rest from a time `T`: `θ_T(s,b) ≤ θ_T(s,a₀)` for
  `b ∈ Z`, and each gap `θ_t(s,a₀) - θ_t(s,b)` never shrinks while nonnegative.

Then **every** coordinate at `s` converges.  The mechanism is `softmax_ratio`:
`π_t(b|s) = exp(θ_t(s,b) - θ_t(s,a₀)) · π_t(a₀|s)`; the exponential factor is a
nonincreasing sequence in `(0,1]`, hence convergent to some `ρ b ∈ [0,1]` with
`ρ a₀ = 1`; and `∑_{b ∈ Z} π_t(b|s) → 1` (`Conv2.tendsto_mass_on_zero_set`) then
pins `π_t(a₀|s) → 1 / ∑_{b∈Z} ρ b`, a limit that is well-defined because the sum
is `≥ ρ a₀ = 1 > 0`.  Every other coordinate follows by multiplying back.

Note what this does **not** need: no monotonicity of the probabilities themselves
(they are not monotone — a non-leading tied coordinate can rise then fall), no
summability of anything, and no rate.  Only the *logit gaps to one leader* have
to be monotone.  That is a strictly weaker demand than `Conv.lean`'s
`policy_converges_of_eventually_monotone`, whose own obstruction note records
that coordinatewise policy monotonicity fails once `|A| ≥ 3`.

`gap_monotone_of_adv_dominates` supplies that gap monotonicity from a hypothesis
strictly weaker than `Conv2.tie_gap_monotone`'s exact tie: it suffices that
`0 ≤ A^{(t)}(s,b) ≤ A^{(t)}(s,a₀)` whenever `b` trails `a₀`, since then
`π_t(a₀|s) A^{(t)}(s,a₀) ≥ π_t(b|s) A^{(t)}(s,b)` and `theta_decrement` gives the
gap a nonnegative increment.

## 2. `γ = 0` closes, with no tie hypothesis on the MDP

At `γ = 0`, `advInf M π s a = r(s,a) - V^π(s)`, so **the difference of two
advantages at a state is the reward difference, at every finite time**
(`advInf_sub_gamma_zero`).  Two actions whose limiting advantages both vanish
therefore have equal rewards and hence *exactly equal advantages at every `t`*
(`adv_eq_of_both_zero_limit_gamma_zero`) — the exact tie is **derived, not
assumed**.  And that common advantage is `r(s,a) - V^{(t)}(s) ≥ 0`, because
`V^{(t)}(s)` increases to its limit (`exists_Vinf_limit`), making the advantage
antitone with limit `0` (`adv_nonneg_of_zero_limit_gamma_zero`).

So both hypotheses of `gap_monotone_of_adv_dominates` hold on the tied set for
*every* `γ = 0` MDP, with the leader taken to be any maximiser of `θ_0(s,·)` over
the tied set (`exists_leader`).  `coord_tendsto_of_leader` closes each state and
`Conv.exists_policy_limit_of_coord_tendsto` assembles the limit policy.  That is
`softmax_policy_converges_gamma_zero`.

This subsumes the `G9b` tie witness (one state, three actions, `γ = 0`,
`r = (1,1,0)`) — exactly the configuration `Goal.lean` worried about, and the one
that breaks `g9_c_positive` without breaking policy convergence.

## 3. `γ > 0`: the obstruction, made quantitative

Let `Vbar s := lim_t V^{(t)}(s)` (`Conv2.exists_Vinf_tendsto`) and
`δ_t s := Vbar s - V^{(t)}(s) ≥ 0`, decreasing to `0`.  For an action `a` whose
limiting advantage vanishes, `Vbar` satisfies the Bellman identity at `(s,a)`
(`vbar_bellman_of_adv_limit_zero`), and subtracting it from `advInf` gives

    A^{(t)}(s,a) = δ_t s - γ · ∑_{s'} P(s'|s,a) · δ_t s'.        (‡)

`adv_eq_value_gap_of_zero_limit` is `(‡)`.  It explains both §2 and what is still
missing:

* **`γ = 0` collapses `(‡)` to `A^{(t)}(s,a) = δ_t s`** — the same nonnegative
  number for every tied `a`.  So §2 is not a lucky special case: `(‡)` shows it
  is the whole content of `γ = 0`.
* **For `γ > 0` the sign of `A^{(t)}(s,a)` on the tied set is free.**  `(‡)` reads
  `δ_t s - γ ⟨P(·|s,a), δ_t⟩`, and nothing forces `δ_t s ≥ γ ⟨P(·|s,a), δ_t⟩`.
  It *is* forced at a state maximising `δ_t`, where `A^{(t)}(s,a) ≥ (1-γ) δ_t s ≥ 0`
  — but the maximiser moves with `t`, so this yields no *eventual* sign at any
  fixed state.  That is precisely `Conv2`'s numerical finding (`γ = 0.6`:
  `A^{(t)}` negative for thousands of consecutive steps at tied states), now with
  a reason.  Hence neither `gap_monotone_of_adv_dominates` nor
  `Conv2.tie_gap_monotone` can be discharged — `(‡)` shows the latter's exact-tie
  hypothesis is equivalent to `⟨P(·|s,a) - P(·|s,b), δ_t⟩ = 0`, an accident of
  the transition kernel rather than a consequence of the tie.
* **The bounded-variation route hits the same wall, and `(‡)` says where.**
  From `(‡)`, `|A^{(t)}(s,a)| ≤ (1 + γ) ‖δ_t‖_∞` for tied `a`, so a tied logit gap
  moves by `O(‖δ_t‖_∞)` per step and `∑_t ‖π_{t+1} - π_t‖` is controlled as soon
  as `∑_t ‖δ_t‖_∞ < ∞`.  But softmax policy gradient converges at rate `Θ(1/t)` —
  in `Conv2`'s two-action model `π_t(loser) ≍ 1/(2ηt)`, so `δ_t ≍ 1/t` — and
  `∑_t ‖δ_t‖_∞` **diverges logarithmically**, by the same logarithm that defeats
  `∑_t ‖θ_{t+1} - θ_t‖`.  The policy total variation nevertheless saturates
  numerically (`Conv.lean`'s header: `6.7328` at `10⁵`, `6.7358` at `10⁶`), so the
  divergence is entirely an artefact of replacing the signed difference
  `π_t(a|s) A^{(t)}(s,a) - π_t(b|s) A^{(t)}(s,b)` by `|A^{(t)}(s,a)| + |A^{(t)}(s,b)|`.
  **So `Summable (fun t => ‖π_{t+1} - π_t‖)` is not reachable by majorisation:
  it requires the cancellation**, i.e. a rate comparison between two tied
  coordinates — which is exactly `ResidC9.ratio_step`'s estimate, and
  `ratio_step` binds `πbar`.  The circularity `Conv2` §4 localises survives; this
  file localises it further, to a statement purely about `δ_t`.

## 4. What is left, exactly

`softmax_policy_converges_of_leader` is the sharpest πbar-free reduction reached
here: the frozen goal follows from `hlead`, which asks for **one** leading action
per state whose gaps to the other tied actions never shrink.  Discharging `hlead`
for `γ > 0` needs one of

* `∑_t ‖Vbar - V^{(t)}‖_∞ < ∞` — **false**, the rate is `Θ(1/t)`; or
* eventual nonnegativity of `A^{(t)}(s,·)` on the tied set — **false** by `(‡)`,
  and confirmed numerically in `Conv2` §4; or
* a signed rate comparison of `π_t(a|s) A^{(t)}(s,a)` against
  `π_t(b|s) A^{(t)}(s,b)` for `a, b` both tied — the one open ingredient, and not
  available πbar-free anywhere in the repo.

**Routes not to retry.**  `∑ ‖θ_{t+1} - θ_t‖ < ∞` (refuted in `Conv2` §1 with a
closed form).  Any `Resid` sign-stability fact, or `ResidC9.ratio_step`, or
`ResidFinal.limit_adv_nonpos_offsupport_proof` — all bind `πbar` and `hlim`.
Łojasiewicz on `‖θ‖` (`‖θ‖ → ∞`).  And **connectedness of the limit set**:
Ostrowski does apply, since `‖θ_{t+1} - θ_t‖ = η‖∇V(θ_t)‖ → 0`
(`AKM51.tendsto_norm_grad_zero`) and the policies are bounded, so the set of limit
points is compact and connected; but every limit point shares the same value
function `Vbar`, hence the same advantage, so the limit set lies inside
`∏_s Δ(Z s)` — a **product of simplices, which is itself connected**.
Connectedness therefore adds nothing beyond `Conv2.coord_tendsto_of_unique_zero`'s
already-handled singleton case.
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

/-! ## The general `γ`: the exact shape of what is missing

For general `γ` the tie split does **not** close, and the computation below says
precisely why.  Let `Vbar s := lim_t V^{(t)}(s)` (`exists_Vinf_tendsto`) and put

    δ_t s := Vbar s - V^{(t)}(s)  ≥ 0,   decreasing to 0

(nonnegative and decreasing because `V^{(t)}(s)` increases to its limit,
`exists_Vinf_limit`).  For an action `a` with vanishing limiting advantage,
`Abar s a = r(s,a) + γ ∑_{s'} P(s'|s,a) Vbar s' - Vbar s = 0`, so subtracting

    A^{(t)}(s,a) = δ_t s - γ ∑_{s'} P(s'|s,a) · δ_t s'.     (‡)

`adv_eq_value_gap_of_zero_limit` below is exactly `(‡)`.

Three consequences, all sharp:

* **`γ = 0` collapses `(‡)` to `A^{(t)}(s,a) = δ_t s`** — the *same* number for
  every `a ∈ Z s`, and `≥ 0`.  That is the exact tie with nonnegative advantage,
  which is why `softmax_policy_converges_gamma_zero` goes through with no
  hypothesis on `M` at all.
* **For `γ > 0` the sign of `A^{(t)}(s,a)` is genuinely free**: `(‡)` is
  `δ_t s - γ ⟨P_a, δ_t⟩`, and nothing forces `δ_t s ≥ γ ⟨P_a, δ_t⟩`.  Only at a
  state maximising `δ_t` is `A^{(t)}(s,a) ≥ (1-γ) δ_t s ≥ 0` — and the maximiser
  moves with `t`, so it supplies no *eventual* sign.  This matches `Conv2`'s
  numerics (`γ = 0.6`: `A^{(t)}` negative for thousands of consecutive steps at
  tied states), and it is why `gap_monotone_of_adv_dominates` — whose only real
  hypothesis is `0 ≤ A^{(t)}(s,b) ≤ A^{(t)}(s,a)` — cannot be discharged.
* **The bounded-variation route hits the same wall.**  From `(‡)`,
  `|A^{(t)}(s,a)| ≤ (1 + γ) ‖δ_t‖_∞` for every `a ∈ Z s`, so the logit gap
  between two tied actions moves by at most `C ‖δ_t‖_∞` per step, and
  `∑_t ‖π_{t+1} - π_t‖` is controlled as soon as `∑_t ‖δ_t‖_∞ < ∞`.  But softmax
  policy gradient converges at rate `Θ(1/t)` — in the two-action model of
  `Conv2`'s header, `π_t(loser) ≍ 1/(2ηt)` and hence `δ_t ≍ 1/t` — so
  `∑_t ‖δ_t‖_∞` **diverges**, by exactly the same logarithm that defeats
  `∑_t ‖θ_{t+1} - θ_t‖`.  The policy-space total variation nevertheless
  saturates numerically, so the divergence is an artefact of dropping the
  cancellation `p_a A_a - p_b A_b` in favour of `|A_a| + |A_b|`.  Recovering it
  is a **rate comparison between two tied coordinates** — the same missing
  ingredient `Conv2` §4 names, and the same one `ResidC9.ratio_step` supplies
  only after assuming a limit policy.

So the obstruction has not moved, but it is now quantitative: what is needed is
either `∑_t ‖Vbar - V^{(t)}‖_∞ < ∞` (false, `Θ(1/t)`) or a signed cancellation
in `π_t(a|s) A^{(t)}(s,a) - π_t(b|s) A^{(t)}(s,b)` for `a, b` both in `Z s`. -/

/-- **`(‡)`** — for an action whose limiting advantage vanishes, the advantage
along the trajectory *is* the value gap, discounted:
`A^{(t)}(s,a) = δ_t s - γ ∑_{s'} P(s'|s,a) δ_t s'`, where `δ_t = Vbar - V^{(t)}`. -/
theorem adv_eq_value_gap_of_zero_limit (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a : A)
    (hVbar : Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s')) (t : ℕ) :
    advInf M (π t) s a
      = (Vbar s - Vinf M (π t) s)
        - M.γ * (∑ s', (M.P s a) s' * (Vbar s' - Vinf M (π t) s')) := by
  have hsplit : ∑ s', (M.P s a) s' * (Vbar s' - Vinf M (π t) s')
      = (∑ s', (M.P s a) s' * Vbar s') - ∑ s', (M.P s a) s' * Vinf M (π t) s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s' _ => by ring)
  rw [hsplit, advInf, hVbar]
  ring

/-- The Bellman identity `hVbar` of `(‡)` holds exactly when the limiting
advantage of `a` at `s` vanishes. -/
theorem vbar_bellman_of_adv_limit_zero (M : FiniteMDP S A)
    (π : ℕ → Policy S A) (Vbar : S → ℝ) (s : S) (a : A)
    (hV : ∀ s', Tendsto (fun t => Vinf M (π t) s') atTop (nhds (Vbar s')))
    (hA : Tendsto (fun t => advInf M (π t) s a) atTop (nhds 0)) :
    Vbar s = M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s') := by
  have hlim : Tendsto (fun t => advInf M (π t) s a) atTop
      (nhds (M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s') - Vbar s)) := by
    have hsum : Tendsto (fun t => ∑ s', (M.P s a) s' * Vinf M (π t) s') atTop
        (nhds (∑ s', (M.P s a) s' * Vbar s')) :=
      tendsto_finsetSum _ (fun s' _ => (hV s').const_mul _)
    have := ((hsum.const_mul M.γ).const_add (M.r s a)).sub (hV s)
    simpa only [advInf] using this
  have := tendsto_nhds_unique hA hlim
  linarith

/-! ## The general `γ`, reduced to one leader hypothesis

`softmax_policy_converges_of_leader` below is the sharpest πbar-free reduction
this file reaches: the frozen goal follows from `hlead`, which asks, at each
state, for **one** action of the tied set to lead the others with gaps that never
shrink.  Everything else — that the tied set is nonempty, that every untied
coordinate dies, that the tied coordinates then assemble into a limit — is
discharged.

`hlead` is implied by `gap_monotone_of_adv_dominates` as soon as the tied
advantages are eventually nonnegative and comparable, which `(‡)` shows holds
automatically at `γ = 0` and fails for `γ > 0`. -/

/-- **The frozen goal, given a leading tied action at each state.** -/
theorem softmax_policy_converges_of_leader (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (hlead : ∀ (s : S) (Z : Finset A),
      (∀ a, a ∈ Z ↔ Tendsto (fun t => advInf M (F.toPolicy (θ t)) s a) atTop (nhds 0)) →
      ∃ a₀ ∈ Z, ∃ T : ℕ, (∀ b ∈ Z, (θ T) (s, b) ≤ (θ T) (s, a₀)) ∧
        (∀ b ∈ Z, ∀ t, T ≤ t → (θ t) (s, b) ≤ (θ t) (s, a₀) →
          (θ t) (s, a₀) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a₀) - (θ (t + 1)) (s, b))) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) := by
  classical
  refine exists_policy_limit_of_coord_tendsto (fun t => F.toPolicy (θ t)) ?_
  choose Abar hAbar using exists_adv_tendsto M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep
  intro s
  set Z : Finset A := {a | Abar s a = 0} with hZdef
  have hmemZ : ∀ a, a ∈ Z ↔ Abar s a = 0 := by intro a; simp [hZdef]
  have hout : ∀ b ∉ Z, Tendsto (fun t => (F.toPolicy (θ t) s) b) atTop (nhds 0) := by
    intro b hb
    exact tendsto_pi_zero_of_adv_limit_ne M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
      s b (Abar s b) (fun h => hb ((hmemZ b).mpr h)) (hAbar s b)
  have hchar : ∀ a, a ∈ Z ↔
      Tendsto (fun t => advInf M (F.toPolicy (θ t)) s a) atTop (nhds 0) := by
    intro a
    constructor
    · intro ha; have := hAbar s a; rwa [(hmemZ a).mp ha] at this
    · intro ha
      exact (hmemZ a).mpr (tendsto_nhds_unique (hAbar s a) ha)
  obtain ⟨a₀, ha₀, T, hT, hgap⟩ := hlead s Z hchar
  exact coord_tendsto_of_leader F hF θ s Z a₀ ha₀ T hT hgap hout

/-! ## Axiom / type audit -/

section Audit

#print axioms softmax_policy_converges_gamma_zero
#print axioms softmax_policy_converges_of_leader
#print axioms coord_tendsto_of_leader
#print axioms gap_monotone_of_adv_dominates
#print axioms adv_eq_value_gap_of_zero_limit

end Audit

end Conv3

end Proofs
end PolicyGradient
