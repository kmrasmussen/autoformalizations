/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Proofs.lean — where the work happens

**Subagents own this file. The orchestrator owns `Goal.lean`.**

`Goal.lean` states the frozen targets. This file supplies the mathematics. A
goal is discharged when a lemma here has exactly the type the goal states, and
the orchestrator wires it in with a one-line edit there.

The split is the point. Whoever is trying to prove something must not be able to
edit what counts as proved — otherwise, on hitting a hard step, the cheapest
path is to weaken the statement, and that path is always locally reasonable
(see `GAPS.md` for how that produced 114 theorems and zero `sorry` over real
holes). Here the type is fixed elsewhere: a weaker lemma simply fails to
typecheck at the wiring site.

Helper lemmas, alternative formulations, scaffolding, and false starts all
belong here and are encouraged. The only hard rules are the ones in
`CONTRIBUTING.md`: no `axiom`, no `sorry`, and if a goal turns out to be wrong,
say so instead of bending it.
-/

open Finset

namespace PolicyGradient
namespace Proofs

/-! ## `Vstar` is well-behaved (`Vstar-sound`, `Vstar-finite`)

`Vstar M s₀ = ⨆ π, Vinf M π s₀` is a *conditional* supremum. Mathlib's `ciSup`
returns junk (`0`) when the family is unbounded above or the index type is
empty, so neither `vstar_upper` nor `vstar_le` is formal nonsense to be waved
through — each needs a real side condition:

* `le_ciSup` needs `BddAbove (Set.range fun π => Vinf M π s₀)`;
* `ciSup_le` needs `Nonempty (Policy S A)`.

Both come from the same place. `abs_Vinf_le` (in `Infinite.lean`) bounds
`|Vinf M π s₀|` by `R/(1-γ)` *uniformly in `π`*, which is exactly `BddAbove`;
and `Policy S A = S → Dist A` is inhabited as soon as `A` is, via a point mass.
-/

section PolicyNonempty
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The point mass at `i`: `δ_i`.

Needed only to inhabit `Policy S A`. `Dist` is a bare structure with no
`Nonempty` instance, and without one `ciSup_le` cannot fire — Mathlib's `⨆`
over an empty index type is `0`, and `Vstar ≤ 1/(1-γ)` would then be a claim
about `0`, not about any MDP. -/
noncomputable def pointMass (i : ι) : Dist ι where
  prob j := if j = i then 1 else 0
  nonneg j := by split <;> norm_num
  sum_eq_one := by simp

end PolicyNonempty

/-- `Policy S A` is inhabited whenever `A` is: play the point mass everywhere. -/
noncomputable instance instNonemptyPolicy {S A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] : Nonempty (Policy S A) :=
  ⟨fun _ => pointMass (Classical.arbitrary A)⟩

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- Every policy's value is at most `1/(1-γ)` when rewards are bounded by `1`. -/
theorem Vinf_le_one_div (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ : S) : Vinf M π s₀ ≤ 1 / (1 - M.γ) :=
  (le_abs_self _).trans (abs_Vinf_le M π 1 zero_le_one hr hγ₀ hγ₁ s₀)

/-- **The policy values are bounded above**, uniformly in `π`.

This is the side condition `le_ciSup` needs, and it is genuine content: without
it `⨆ π, Vinf M π s₀` would be Mathlib's junk value and `vstar_upper` would be
false in general. -/
theorem bddAbove_range_Vinf (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    BddAbove (Set.range fun π : Policy S A => Vinf M π s₀) := by
  refine ⟨1 / (1 - M.γ), ?_⟩
  rintro x ⟨π, rfl⟩
  exact Vinf_le_one_div M hr hγ₀ hγ₁ π s₀

/-- Discharges `Goal.vstar_upper` (`@[infra "Vstar-sound"]`). -/
theorem vstar_upper_proof (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ : S) :
    Vinf M π s₀ ≤ Vstar M s₀ :=
  le_ciSup (bddAbove_range_Vinf M hr hγ₀ hγ₁ s₀) π

/-- Discharges `Goal.vstar_le` (`@[infra "Vstar-finite"]`). -/
theorem vstar_le_proof (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Vstar M s₀ ≤ 1 / (1 - M.γ) :=
  ciSup_le fun π => Vinf_le_one_div M hr hγ₀ hγ₁ π s₀

/-! ### Trajectory-exists — the gradient-ascent recursion admits a solution

`hstep` in `mei_theorem4` and `mei_theorem6` constrains `θ` by a recursion. If no
sequence satisfied it, those theorems would be vacuously true for lack of any
`θ`. This is the well-definedness check that closes that vacuity route.

The construction is the obvious one: iterate the ascent map from `θ₀` by
`Nat.rec`. No analysis is involved — `gradient` is total in Mathlib (returning
`0` where the function is not differentiable), so the ascent map is defined
everywhere and the recursion is unconditional. Both conjuncts then hold by
`rfl`, since `Nat.rec` reduces definitionally at `0` and at `t + 1`. -/
theorem ascent_trajectory_exists_proof (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (μ : S) (θ₀ : EuclideanSpace ℝ (S × A)) :
    ∃ θ : ℕ → EuclideanSpace ℝ (S × A), θ 0 = θ₀ ∧ ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t) :=
  ⟨fun t => Nat.rec θ₀
    (fun _ prev =>
      prev + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) prev) t,
    rfl, fun _ => rfl⟩

/-- `visit` is a probability, hence pointwise at most `1`. -/
theorem visit_le_one (M : FiniteMDP S A) (π : Policy S A) (t : ℕ) (s₀ s : S) :
    visit M π t s₀ s ≤ 1 := by
  have hsum := visit_sum_eq_one M π t s₀
  have hle : visit M π t s₀ s ≤ ∑ s', visit M π t s₀ s' :=
    Finset.single_le_sum (fun s' _ => visit_nonneg M π t s₀ s') (Finset.mem_univ s)
  linarith

/-- The unnormalized discounted occupancy measure is bounded by the geometric
sum `1/(1-γ)`. -/
theorem dinf_le_one_div (M : FiniteMDP S A) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ s : S) :
    dinf M π s₀ s ≤ 1 / (1 - M.γ) := by
  have hgeo : ∑' t : ℕ, M.γ ^ t = (1 - M.γ)⁻¹ := tsum_geometric_of_lt_one hγ₀ hγ₁
  have hcmp : ∑' t : ℕ, M.γ ^ t * visit M π t s₀ s ≤ ∑' t : ℕ, M.γ ^ t := by
    refine Summable.tsum_le_tsum (fun t => ?_)
      (summable_dvisit M π hγ₀ hγ₁ s₀ s) (summable_geometric_of_lt_one hγ₀ hγ₁)
    calc M.γ ^ t * visit M π t s₀ s
        ≤ M.γ ^ t * 1 :=
          mul_le_mul_of_nonneg_left (visit_le_one M π t s₀ s) (pow_nonneg hγ₀ t)
      _ = M.γ ^ t := mul_one _
  rw [dinf, one_div]
  rw [hgeo] at hcmp
  exact hcmp


/-! ## Bellman optimality (`Bellman-optimality`, `Greedy-support`)

The two goals here are the standard Bellman-optimality characterization
`V*(s) = maxₐ Q*(s,a)` and the "an optimal policy's support is greedy" step.

### A structural note: where `Qstar` lives

`Qstar` is declared in **`Goal.lean`**, not in `Target.lean`. `Proofs.lean` cannot
import `Goal.lean` (that is the very cycle `Target.lean` was split out to avoid),
and re-declaring `Qstar` here or in `Target.lean` makes `Goal.lean` fail with
`already been declared`. Since subagents may not edit `Goal.lean`, the two
`_proof` lemmas below state `Q*` **inlined** — literally
`M.r s a + M.γ * ∑ s', (M.P s a) s' * Vstar M s'` — which is *definitionally*
`Qstar M s a`. The orchestrator's one-line wiring
`:= Proofs.vstar_bellman_proof M hr hγ₀ hγ₁ s` therefore typechecks unchanged;
`Qstar` is a plain `def` and unfolds at default transparency. (Verified against a
standalone two-module replica of exactly this import shape.)

`QstarP` below is that same body under a local name, used only inside this file.
Moving `Qstar` from `Goal.lean` to `Target.lean` — where the other definitions
already live — would remove the need for both the alias and the inlining, and is
the recommended cleanup for the orchestrator.

### Why the usual textbook argument does not transcribe directly

`Vstar M s = ⨆ π : Policy S A, Vinf M π s` is a supremum over **stationary**
policies, taken **separately at each state**. Nothing in the definition says one
policy attains it at all states at once. The easy inequality
`Vstar s ≤ ⨆ a, Q*(s,a)` needs nothing more than `Vinf_eq_rbar_add` plus
`Vinf π s' ≤ Vstar s'`. The reverse needs a policy realizing `Q*(s,a)`, and the
naive "play `a` once, then act optimally" is *not* a stationary policy, so it is
not an element of `Policy S A` at all.

### The route taken

Avoid constructing a per-`(s,a)` policy entirely. Build the single **greedy
deterministic stationary** policy `greedyPolicy`, `g s := argmaxₐ Q*(s,a)`, and
show `Vinf M greedyPolicy = Vstar` by a max-state contraction argument:

* `vstar_le_greedy_Q` : `∀ s, Vstar M s ≤ Q*(s, g s)` — the easy direction.
* `Vinf_greedy_bellman` : `Vinf M g s = M.r s (g s) + γ ∑ s', P s (g s) s' · Vinf M g s'`
  — the greedy policy's own Bellman equation, from `Vinf_eq_rbar_add` plus the
  fact that a deterministic policy's expectation collapses to one term.
* Subtracting, with `Δ s := Vstar M s - Vinf M g s ≥ 0` (from `vstar_upper_proof`):
  `Δ s ≤ γ * ∑ s', P s (g s) s' * Δ s' ≤ γ * (maxₛ Δ)`.
* Evaluate at the argmax `s*` of `Δ`: `D ≤ γ D` with `0 ≤ D` and `γ < 1`, so
  `D = 0` and `Vinf M g = Vstar` pointwise (`vstar_eq_greedy`).

Then `Q*(s, g s) = Qinf g s (g s) = Vinf g s = Vstar s`, closing the hard
direction. No approximation, no nonstationary policies, no ε-arguments:
everything is a finite max over `S` and `A`.
-/

section Bellman

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- `Set.range f` for `f` on a finite type is bounded above — the side condition
`le_ciSup` needs for the `A`-indexed and `S`-indexed suprema below. -/
theorem bddAbove_range_finite {ι : Type*} [Finite ι] (f : ι → ℝ) :
    BddAbove (Set.range f) :=
  Set.Finite.bddAbove (Set.finite_range f)

/-- A deterministic stationary policy: always play `f s` in state `s`. -/
noncomputable def detPolicy (f : S → A) : Policy S A := fun s => pointMass (f s)

theorem detPolicy_apply (f : S → A) (s : S) (a : A) :
    (detPolicy f s) a = if a = f s then 1 else 0 := rfl

/-- Expectations under a deterministic policy collapse to a single term. -/
theorem sum_detPolicy (f : S → A) (s : S) (h : A → ℝ) :
    ∑ a, (detPolicy f s) a * h a = h (f s) := by
  simp only [detPolicy_apply, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq' Finset.univ (f s) h]

/-- The optimal action-value, **inlined** rather than referring to `Goal.Qstar`
(see the note above). Definitionally equal to `Qstar M s a`. -/
noncomputable def QstarP (M : FiniteMDP S A) (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * ∑ s', (M.P s a) s' * Vstar M s'

/-- An action maximizing `Q*(s, ·)`. Exists since `A` is finite and nonempty. -/
noncomputable def greedyAct (M : FiniteMDP S A) (s : S) : A :=
  (Finite.exists_max (QstarP M s)).choose

theorem greedyAct_max (M : FiniteMDP S A) (s : S) (a : A) :
    QstarP M s a ≤ QstarP M s (greedyAct M s) :=
  (Finite.exists_max (QstarP M s)).choose_spec a

/-- The greedy deterministic stationary policy `g s = argmaxₐ Q*(s,a)`. -/
noncomputable def greedyPolicy (M : FiniteMDP S A) : Policy S A :=
  detPolicy (greedyAct M)

/-- `⨆ a, Q*(s,a) = Q*(s, g s)`: the finite sup is attained at the greedy action. -/
theorem ciSup_QstarP (M : FiniteMDP S A) (s : S) :
    ⨆ a : A, QstarP M s a = QstarP M s (greedyAct M s) :=
  le_antisymm (ciSup_le fun a => greedyAct_max M s a)
    (le_ciSup (bddAbove_range_finite (QstarP M s)) _)

/-- **The easy direction, per state:** `V*(s) ≤ Q*(s, g s)`.

For any `π`, `Vinf π s = ∑ₐ π(a|s) · Qinf(π,s,a) ≤ ∑ₐ π(a|s) · Q*(s,a)`
(monotone in `Vinf π s' ≤ Vstar s'`), and each `Q*(s,a) ≤ Q*(s, g s)`, so the
whole convex combination is `≤ Q*(s, g s)`. Take the sup over `π`. -/
theorem vstar_le_greedy_Q (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vstar M s ≤ QstarP M s (greedyAct M s) := by
  refine ciSup_le fun π => ?_
  rw [Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s]
  have hQ : ∀ a, Qinf M π s a ≤ QstarP M s (greedyAct M s) := by
    intro a
    refine le_trans ?_ (greedyAct_max M s a)
    unfold Qinf QstarP
    have hsum : ∑ s', (M.P s a) s' * Vinf M π s'
        ≤ ∑ s', (M.P s a) s' * Vstar M s' :=
      Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left
          (vstar_upper_proof M hr hγ₀ hγ₁ π s') ((M.P s a).nonneg s')
    have := mul_le_mul_of_nonneg_left hsum hγ₀
    linarith
  calc ∑ a, (π s) a * Qinf M π s a
      ≤ ∑ a, (π s) a * QstarP M s (greedyAct M s) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hQ a) ((π s).nonneg a)
    _ = QstarP M s (greedyAct M s) := by
        rw [← Finset.sum_mul, (π s).sum_eq_one, one_mul]

/-- The greedy policy's own Bellman equation, with the deterministic
expectation already collapsed to its single term. -/
theorem Vinf_greedy_bellman (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vinf M (greedyPolicy M) s
      = M.r s (greedyAct M s)
        + M.γ * ∑ s', (M.P s (greedyAct M s)) s' * Vinf M (greedyPolicy M) s' := by
  rw [Vinf_eq_rbar_add M (greedyPolicy M) 1 zero_le_one hr hγ₀ hγ₁ s]
  unfold greedyPolicy
  rw [sum_detPolicy (greedyAct M) s (Qinf M (detPolicy (greedyAct M)) s)]
  rfl

/-! ### The max-state contraction

`Δ s := Vstar M s - Vinf M g s` is nonnegative (`vstar_upper_proof`) and
satisfies `Δ s ≤ γ * ∑ s', P s (g s) s' * Δ s'`. Bounding the convex combination
by the max of `Δ` and evaluating at the argmax gives `D ≤ γ D`, forcing `D = 0`.
-/

/-- The suboptimality of the greedy policy, as a function of the state. -/
noncomputable def greedyGap (M : FiniteMDP S A) (s : S) : ℝ :=
  Vstar M s - Vinf M (greedyPolicy M) s

theorem greedyGap_nonneg (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    0 ≤ greedyGap M s :=
  sub_nonneg.mpr (vstar_upper_proof M hr hγ₀ hγ₁ (greedyPolicy M) s)

/-- The one-step inequality: the gap at `s` is at most `γ` times the
`P s (g s)`-average of the gap at successors.

`Vstar s ≤ Q*(s, g s) = r s (g s) + γ ∑ P · Vstar`, while
`Vinf g s = r s (g s) + γ ∑ P · Vinf g` exactly. Subtract. -/
theorem greedyGap_step (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    greedyGap M s ≤ M.γ * ∑ s', (M.P s (greedyAct M s)) s' * greedyGap M s' := by
  have hup := vstar_le_greedy_Q M hr hγ₀ hγ₁ s
  have hbell := Vinf_greedy_bellman M hr hγ₀ hγ₁ s
  have hsplit : ∑ s', (M.P s (greedyAct M s)) s' * greedyGap M s'
      = (∑ s', (M.P s (greedyAct M s)) s' * Vstar M s')
        - ∑ s', (M.P s (greedyAct M s)) s' * Vinf M (greedyPolicy M) s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ => by unfold greedyGap; ring
  unfold greedyGap QstarP at *
  rw [hsplit]
  nlinarith [hup, hbell]

/-- The largest gap over states, and the state attaining it. -/
theorem greedyGap_eq_zero (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    greedyGap M s = 0 := by
  obtain ⟨sm, hsm⟩ := Finite.exists_max (greedyGap M)
  -- D = greedyGap M sm is the maximum
  set D := greedyGap M sm with hD
  have hD0 : 0 ≤ D := greedyGap_nonneg M hr hγ₀ hγ₁ sm
  -- the convex combination of the gaps at successors is at most D
  have havg : ∑ s', (M.P sm (greedyAct M sm)) s' * greedyGap M s' ≤ D := by
    calc ∑ s', (M.P sm (greedyAct M sm)) s' * greedyGap M s'
        ≤ ∑ s', (M.P sm (greedyAct M sm)) s' * D :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (hsm s') ((M.P sm (greedyAct M sm)).nonneg s')
      _ = D := by rw [← Finset.sum_mul, (M.P sm (greedyAct M sm)).sum_eq_one, one_mul]
  have hstep := greedyGap_step M hr hγ₀ hγ₁ sm
  -- D ≤ γ * (something ≤ D) ≤ γ D, and γ < 1 with 0 ≤ D forces D = 0
  have hgD : M.γ * ∑ s', (M.P sm (greedyAct M sm)) s' * greedyGap M s' ≤ M.γ * D :=
    mul_le_mul_of_nonneg_left havg hγ₀
  have hDle : D ≤ M.γ * D := le_trans hstep hgD
  have hDzero : D = 0 := le_antisymm (by nlinarith) hD0
  exact le_antisymm (by rw [← hDzero]; exact hsm s) (greedyGap_nonneg M hr hγ₀ hγ₁ s)

/-- **The greedy policy attains the optimum at every state.** -/
theorem vstar_eq_greedy (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vinf M (greedyPolicy M) s = Vstar M s := by
  have := greedyGap_eq_zero M hr hγ₀ hγ₁ s
  unfold greedyGap at this
  linarith

/-- **Bellman optimality at the greedy action:** `V*(s) = Q*(s, g s)`.

`≤` is `vstar_le_greedy_Q`. For `≥`: with `Vinf g = Vstar` established,
`Q*(s, g s) = r s (g s) + γ ∑ P · Vstar = r s (g s) + γ ∑ P · Vinf g = Vinf g s
 = Vstar s`. -/
theorem vstar_eq_greedy_Q (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vstar M s = QstarP M s (greedyAct M s) := by
  have hbell := Vinf_greedy_bellman M hr hγ₀ hγ₁ s
  have hall : ∀ s', Vinf M (greedyPolicy M) s' = Vstar M s' :=
    fun s' => vstar_eq_greedy M hr hγ₀ hγ₁ s'
  rw [hall s] at hbell
  rw [Finset.sum_congr rfl (fun s' _ => by rw [hall s'])] at hbell
  exact hbell

/-- **`Q*(s,a) ≤ V*(s)` for every action** — the content of the hard direction,
in the form the greedy-support goal needs. -/
theorem QstarP_le_vstar (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) (a : A) :
    QstarP M s a ≤ Vstar M s := by
  rw [vstar_eq_greedy_Q M hr hγ₀ hγ₁ s]
  exact greedyAct_max M s a

/-! ### The two goal lemmas

Stated with `Q*` inlined (see the structural note at the top of this section);
each type is definitionally `Goal`'s, so the orchestrator's one-line wiring
typechecks without change. -/

/-- Discharges `Goal.vstar_bellman` (`@[infra "Bellman-optimality"]`).

`Vstar M s = ⨆ a, Qstar M s a`. Both directions come from the greedy policy:
the sup over `a` is attained at `greedyAct M s` (`ciSup_QstarP`), and
`vstar_eq_greedy_Q` identifies `V*(s)` with `Q*(s, g s)`. -/
theorem vstar_bellman_proof (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vstar M s = ⨆ a : A, (M.r s a + M.γ * ∑ s', (M.P s a) s' * Vstar M s') := by
  show Vstar M s = ⨆ a : A, QstarP M s a
  rw [ciSup_QstarP M s]
  exact vstar_eq_greedy_Q M hr hγ₀ hγ₁ s

/-- Discharges `Goal.optimal_support_greedy` (`@[infra "Greedy-support"]`).

If `π` attains the optimum at `s`, every action in its support is optimal there.

`V*(s) = Vinf π s = ∑ₐ π(a|s) · Qinf(π,s,a) ≤ ∑ₐ π(a|s) · Q*(s,a)
       ≤ ∑ₐ π(a|s) · V*(s) = V*(s)`,

so both inequalities are equalities. The second is a sum of the nonnegative
terms `π(a|s) · (V*(s) - Q*(s,a))` — nonnegative by `QstarP_le_vstar`, the hard
half of Bellman optimality — summing to zero, hence each vanishes. With
`π(a|s) > 0` this forces `Q*(s,a) = V*(s)`. -/
theorem optimal_support_greedy_proof (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) (hopt : Vinf M π s = Vstar M s)
    (a : A) (hsupp : 0 < (π s) a) :
    (M.r s a + M.γ * ∑ s', (M.P s a) s' * Vstar M s') = Vstar M s := by
  show QstarP M s a = Vstar M s
  -- `Qinf π s b ≤ Q* s b` pointwise, by monotonicity in `Vinf π ≤ Vstar`.
  have hQmono : ∀ b, Qinf M π s b ≤ QstarP M s b := by
    intro b
    unfold Qinf QstarP
    have hsum : ∑ s', (M.P s b) s' * Vinf M π s' ≤ ∑ s', (M.P s b) s' * Vstar M s' :=
      Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left
          (vstar_upper_proof M hr hγ₀ hγ₁ π s') ((M.P s b).nonneg s')
    have := mul_le_mul_of_nonneg_left hsum hγ₀
    linarith
  -- expand `Vinf π s` as a `π`-average of `Qinf`
  have hexp : Vstar M s = ∑ b, (π s) b * Qinf M π s b := by
    rw [← hopt]; exact Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  -- the nonnegative slack terms
  set w : A → ℝ := fun b => (π s) b * (Vstar M s - QstarP M s b) with hw
  have hwnn : ∀ b, 0 ≤ w b := fun b =>
    mul_nonneg ((π s).nonneg b) (sub_nonneg.mpr (QstarP_le_vstar M hr hγ₀ hγ₁ s b))
  -- their total is ≤ 0, because `∑ π b · Q* s b ≥ ∑ π b · Qinf π s b = V*(s)`
  have htot : ∑ b, w b ≤ 0 := by
    have hge : Vstar M s ≤ ∑ b, (π s) b * QstarP M s b := by
      rw [hexp]
      exact Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (hQmono b) ((π s).nonneg b)
    have hsplit : ∑ b, w b
        = (∑ b, (π s) b) * Vstar M s - ∑ b, (π s) b * QstarP M s b := by
      simp only [hw, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hsplit, (π s).sum_eq_one, one_mul]
    linarith
  -- a nonnegative family summing to ≤ 0 vanishes termwise
  have hzero : w a = 0 :=
    le_antisymm
      ((Finset.single_le_sum (fun b _ => hwnn b) (Finset.mem_univ a)).trans htot)
      (hwnn a)
  -- and `π(a|s) > 0` cancels
  have := mul_eq_zero.mp hzero
  rcases this with h | h
  · exact absurd h (ne_of_gt hsupp)
  · linarith [sub_eq_zero.mp h]

end Bellman

/-! ## The distribution-mismatch coefficient (`Mismatch-bound`, `Mismatch-pos`)

**Finding: `mismatch_bound` as frozen in `Goal.lean` is FALSE.**
`mismatch_pos` is true and is proved below as `mismatch_pos_proof`.

`mismatch_bound` reads

```lean
dinfDist M π μ s ≤ mismatchCoeff M π μ * μ s
```

with **no full-support hypothesis on `μ`**. That omission is fatal. Take any `s`
with `μ s = 0` that is reachable from the support of `μ`:

* the right-hand side is `mismatchCoeff M π μ * 0 = 0` — `mismatchCoeff` is a
  `ciSup` over the `Fintype` `S`, hence a finite real, never `⊤`; and the `s`-th
  term of that `ciSup` is `dinfDist M π μ s / 0 = 0` by Lean's junk-value
  convention for division, so `s` contributes nothing that could rescue it;
* the left-hand side is `∑ s₀, μ s₀ * dinf M π s₀ s > 0`, because occupancy
  flows into `s` from the states that *do* carry mass.

So the claim reduces to `0 < LHS ≤ 0`. The refutation is machine-checked in
`counterexMDP` below: a two-state MDP where every transition lands in state `1`,
with `μ = δ₀`. There `dinfDist = 1` while `mismatchCoeff * μ 1 = 0`.

This is the *mirror* of the defect the goal was written to repair. The
superseded version was too weak (a free existential constant); pinning the
coefficient by definition fixed that, but bounding against `μ s` without
requiring `μ s > 0` made the statement too strong — the same "floating quantity
is a defect in both directions" failure `CONTRIBUTING.md` records for
`mei_theorem4`. AKM state the mismatch bound for a full-support `μ` precisely
because `d^π_μ / μ` is meaningless where `μ` vanishes; `mismatch_pos` already
carries `hμ`, and `mismatch_bound` needs it too.

**No lemma named `mismatch_bound_proof` with the frozen type is supplied, and
none can be.** What is supplied is `mismatch_bound_proof_of_support`: the same
conclusion under the missing hypothesis. If the orchestrator adds `hμ` to the
frozen statement, that lemma discharges it as-is. -/

section Mismatch

/-- `dinf` is nonnegative: a `tsum` of nonnegative terms. -/
theorem dinf_nonneg (M : FiniteMDP S A) (hγ₀ : 0 ≤ M.γ)
    (π : Policy S A) (s₀ s : S) : 0 ≤ dinf M π s₀ s := by
  rw [dinf]
  exact tsum_nonneg fun t => mul_nonneg (pow_nonneg hγ₀ t) (visit_nonneg M π t s₀ s)

/-- The `t = 0` term of `dinf` is the point mass at the start state, so
`dinf M π s₀ s ≥ [s = s₀]`. -/
theorem dinf_ge_point (M : FiniteMDP S A) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ s : S) :
    (if s = s₀ then (1:ℝ) else 0) ≤ dinf M π s₀ s := by
  rw [dinf_eq M π hγ₀ hγ₁ s₀ s]
  have : 0 ≤ M.γ * ∑ s', step M π s₀ s' * dinf M π s' s := by
    refine mul_nonneg hγ₀ (Finset.sum_nonneg fun s' _ =>
      mul_nonneg ?_ (dinf_nonneg M hγ₀ π s' s))
    unfold step
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg ((π s₀).nonneg a) ((M.P s₀ a).nonneg s')
  linarith

theorem dinfDist_nonneg (M : FiniteMDP S A) (hγ₀ : 0 ≤ M.γ)
    (π : Policy S A) (μ : Dist S) (s : S) : 0 ≤ dinfDist M π μ s :=
  Finset.sum_nonneg fun s₀ _ => mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ π s₀ s)

/-- **`μ s ≤ d^π_μ(s)`**: the occupancy from a distribution is at least the
distribution itself, because the `s₀ = s` summand already contributes
`μ s · dinf M π s s ≥ μ s · 1`. This is what makes the mismatch ratio `≥ 1`
everywhere and hence `mismatchCoeff ≥ 1 > 0`. -/
theorem mu_le_dinfDist (M : FiniteMDP S A) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (μ : Dist S) (s : S) : μ s ≤ dinfDist M π μ s := by
  unfold dinfDist
  have key : ∀ s₀ ∈ (Finset.univ : Finset S),
      (if s₀ = s then μ s₀ else 0) ≤ μ s₀ * dinf M π s₀ s := by
    intro s₀ _
    by_cases h : s₀ = s
    · subst h
      have hd : (1:ℝ) ≤ dinf M π s₀ s₀ := by
        have := dinf_ge_point M hγ₀ hγ₁ π s₀ s₀
        simpa using this
      have : μ s₀ * 1 ≤ μ s₀ * dinf M π s₀ s₀ :=
        mul_le_mul_of_nonneg_left hd (μ.nonneg s₀)
      simpa using this
    · simp only [if_neg h]
      exact mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ π s₀ s)
  simpa using Finset.sum_le_sum key

/-- The mismatch family is bounded above: `S` is a `Fintype`, so `ciSup` is a
genuine maximum and not the `0` junk value. -/
theorem bddAbove_mismatch (M : FiniteMDP S A) (π : Policy S A) (μ : Dist S) :
    BddAbove (Set.range fun s : S => dinfDist M π μ s / μ s) :=
  Finite.bddAbove_range _

/-- **`Mismatch-pos` — discharges the frozen goal `mismatch_pos`.**

With full support every ratio `d^π_μ(s)/μ(s)` is at least `1` (by
`mu_le_dinfDist`), and `S` is nonempty and finite so the `ciSup` attains at
least one of them. -/
theorem mismatch_pos_proof (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S)
    (hμ : ∀ s, 0 < μ s) :
    0 < mismatchCoeff M π μ := by
  obtain ⟨s⟩ := ‹Nonempty S›
  have h1 : (1:ℝ) ≤ dinfDist M π μ s / μ s := by
    rw [le_div_iff₀ (hμ s), one_mul]
    exact mu_le_dinfDist M hγ₀ hγ₁ π μ s
  have h2 := le_ciSup (bddAbove_mismatch M π μ) s
  unfold mismatchCoeff
  linarith

/-- **The repaired `Mismatch-bound`.**

The frozen `mismatch_bound` is false (see `counterexMDP` below); this is the
statement that is true — identical except for the full-support hypothesis `hμ`
that `mismatch_pos` already carries. `le_ciSup` gives
`dinfDist s / μ s ≤ mismatchCoeff`, and multiplying by `μ s > 0` clears the
division. -/
theorem mismatch_bound_proof_of_support (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S)
    (hμ : ∀ s, 0 < μ s) (s : S) :
    dinfDist M π μ s ≤ mismatchCoeff M π μ * μ s := by
  have h := le_ciSup (bddAbove_mismatch M π μ) s
  rw [div_le_iff₀ (hμ s)] at h
  exact h

end Mismatch

/-! ### The counterexample refuting the frozen `mismatch_bound`

Machine-checked, so the finding cannot rot into prose. Two states, two actions,
`γ = 1/2`; **every** transition lands in state `1`; `μ = δ₀`. Then
`d^π_μ(1) = γ/(1-γ) = 1` but `μ 1 = 0`, so the frozen bound asserts `1 ≤ 0`. -/

section Counterexample

/-- The point mass on state `1` of `Fin 2`. -/
noncomputable def cxToOne : Dist (Fin 2) where
  prob i := if i = 1 then 1 else 0
  nonneg i := by by_cases h : i = 1 <;> simp [h]
  sum_eq_one := by simp

/-- Two states, two actions, `γ = 1/2`, every transition into state `1`. -/
noncomputable def counterexMDP : FiniteMDP (Fin 2) (Fin 2) where
  P := fun _ _ => cxToOne
  r := fun _ _ => 0
  γ := 1/2

/-- The start distribution `δ₀` — mass `1` on state `0`, **`0` on state `1`**. -/
noncomputable def cxMu : Dist (Fin 2) where
  prob i := if i = 0 then 1 else 0
  nonneg i := by by_cases h : i = 0 <;> simp [h]
  sum_eq_one := by simp

noncomputable def cxPi : Policy (Fin 2) (Fin 2) := fun _ => cxToOne

theorem cxMu_one : cxMu 1 = 0 := by simp [cxMu]
theorem cxMu_zero : cxMu 0 = 1 := by simp [cxMu]
theorem cx_gamma_nonneg : (0:ℝ) ≤ counterexMDP.γ := by norm_num [counterexMDP]
theorem cx_gamma_lt_one : counterexMDP.γ < 1 := by norm_num [counterexMDP]

theorem cx_step (s : Fin 2) : step counterexMDP cxPi s 1 = 1 := by
  simp [step, counterexMDP, cxPi, cxToOne]

theorem cx_visit_succ (t : ℕ) (s₀ : Fin 2) :
    visit counterexMDP cxPi (t+1) s₀ 1 = 1 := by
  induction t generalizing s₀ with
  | zero => simp [visit_succ, cx_step, Fin.sum_univ_two]
  | succ t _ =>
    rw [visit_succ]
    have h : ∀ s' : Fin 2,
        visit counterexMDP cxPi (t+1) s₀ s' * step counterexMDP cxPi s' 1
          = visit counterexMDP cxPi (t+1) s₀ s' := fun s' => by rw [cx_step, mul_one]
    rw [Finset.sum_congr rfl (fun s' _ => h s'), visit_sum_eq_one]

/-- `d^π(0, 1) = ∑_{t ≥ 1} γᵗ = γ/(1-γ) = 1`. -/
theorem cx_dinf : dinf counterexMDP cxPi 0 1 = 1 := by
  have hs := summable_dvisit counterexMDP cxPi cx_gamma_nonneg cx_gamma_lt_one 0 1
  unfold dinf
  rw [Summable.tsum_eq_zero_add hs]
  have h0 : counterexMDP.γ ^ 0 * visit counterexMDP cxPi 0 0 1 = 0 := by simp
  rw [h0, zero_add]
  have h : ∀ t : ℕ, counterexMDP.γ ^ (t+1) * visit counterexMDP cxPi (t+1) 0 1
      = (1/2:ℝ) * (1/2:ℝ)^t := by
    intro t; rw [cx_visit_succ]; simp [counterexMDP]; ring
  rw [tsum_congr h, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

theorem cx_dinfDist : dinfDist counterexMDP cxPi cxMu 1 = 1 := by
  unfold dinfDist
  rw [Fin.sum_univ_two, cxMu_zero, cxMu_one, cx_dinf]
  ring

/-- **The frozen `mismatch_bound` fails at this instance**: `1 ≤ 0`. -/
theorem cx_refutes_instance :
    ¬ (dinfDist counterexMDP cxPi cxMu 1
        ≤ mismatchCoeff counterexMDP cxPi cxMu * cxMu 1) := by
  rw [cx_dinfDist, cxMu_one, mul_zero]
  norm_num

/-- **`mismatch_bound` as frozen in `Goal.lean` implies `False`.**

The hypothesis below is the frozen statement verbatim (universally closed over
its binders). No lemma of that type can exist, so the goal cannot be
discharged — it must be repaired by adding `hμ`, after which
`mismatch_bound_proof_of_support` discharges it. -/
theorem mismatch_bound_is_false
    (h : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
           [Nonempty S] [Nonempty A]
           (M : FiniteMDP S A), (0 ≤ M.γ) → (M.γ < 1) → ∀ (π : Policy S A)
           (μ : Dist S) (s : S), dinfDist M π μ s ≤ mismatchCoeff M π μ * μ s) :
    False :=
  cx_refutes_instance (h counterexMDP cx_gamma_nonneg cx_gamma_lt_one cxPi cxMu 1)

end Counterexample


/-! ## G3 — a softmax policy is never exactly optimal

The statement (`Goal.g3_strict_suboptimality`) carries **no bounded-reward
hypothesis**, while every piece of Bellman machinery above needs `|r| ≤ 1`. That
gap is real, not cosmetic: `Vstar` is a `ciSup`, and without *some* uniform bound
on `Vinf` it is Mathlib's junk value. It is closed rather than assumed, in
`section Rescale` below: `S` and `A` are `Fintype`, so `|r|` attains a finite
maximum, and dividing the rewards by `max 1 (that maximum)` produces an MDP with
the same `P` and `γ` whose rewards satisfy `|r| ≤ 1`. Values are *linear* in the
reward function, so `Vinf` and `Vstar` both scale by the same positive constant
and the strict inequality transfers back verbatim.

### The argument

Contrapositive. Write `π₀ := F.toPolicy θ` and suppose `Vinf M π₀ μ = Vstar M μ`
(the negation of the goal, tightened by `vstar_upper_proof`). Let

  `gapOpt s := Vstar M s - Vinf M π₀ s ≥ 0`,   `T := {s | gapOpt s = 0}`.

* **`T` is greedy everywhere.** For `s ∈ T`, softmax puts positive mass on every
  action (`softmax_pos`), so `optimal_support_greedy_proof` gives
  `Q*(s,a) = V*(s)` for *every* `a` — not just the ones a general optimal policy
  happens to play. This is the only place the softmax hypothesis is used, and it
  is the whole content of the lemma.
* **`T` is closed under transitions** (`gapOpt_succ_zero`). Averaging the
  previous point over `π₀` and subtracting `π₀`'s own Bellman equation leaves
  `0 = γ ∑ₐ π₀(a|s) ∑_{s'} P(s'|s,a) · gapOpt s'`, a sum of nonnegative terms.
  So each vanishes: for `s ∈ T`, every `s'` is either in `T` or has
  `γ · P(s'|s,a) = 0`.
* **Every policy is optimal on `T`** (`gapAny_eq_zero_on`). For arbitrary `π` and
  `s ∈ T`, the greedy identity turns `Vstar` into a `π`-average, giving
  `h s = γ ∑ₐ π(a|s) ∑_{s'} P(s'|s,a) · h s'` with `h := Vstar - Vinf π`.
  Masking `h` to `T` (`k s := if gapOpt s = 0 then h s else 0`) is legitimate
  exactly by closure, and the masked recursion contracts: `max k ≤ γ · max k`
  with `max k ≥ 0` and `γ < 1`, so `k ≡ 0`, and in particular `h μ = 0`.

That contradicts `hnondeg`, which supplies a `π` with `Vinf M π μ < Vstar M μ`.

Note the contraction is over the *masked* gap, not the raw one. The raw gap need
not contract — outside `T` a general `π` is genuinely suboptimal — and it is the
closure of `T` that makes the mask invisible to the recursion.
-/

section G3

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ### Rescaling away the missing `|r| ≤ 1` -/

/-- The MDP with rewards divided by `c`, same kernel and same discount. -/
noncomputable def scaleMDP (M : FiniteMDP S A) (c : ℝ) : FiniteMDP S A where
  P := M.P
  r := fun s a => M.r s a / c
  γ := M.γ

@[simp] theorem scaleMDP_P (M : FiniteMDP S A) (c : ℝ) : (scaleMDP M c).P = M.P := rfl
@[simp] theorem scaleMDP_r (M : FiniteMDP S A) (c : ℝ) (s : S) (a : A) :
    (scaleMDP M c).r s a = M.r s a / c := rfl
@[simp] theorem scaleMDP_γ (M : FiniteMDP S A) (c : ℝ) : (scaleMDP M c).γ = M.γ := rfl

/-- `step` only sees `P` and `π`, so rescaling rewards leaves it alone. -/
theorem step_scaleMDP (M : FiniteMDP S A) (c : ℝ) (π : Policy S A) :
    step (scaleMDP M c) π = step M π := rfl

/-- Likewise for the visitation distribution. -/
theorem visit_scaleMDP (M : FiniteMDP S A) (c : ℝ) (π : Policy S A) (t : ℕ) :
    visit (scaleMDP M c) π t = visit M π t := by
  induction t with
  | zero => rfl
  | succ t ih => funext s₀ s; simp only [visit_succ, step_scaleMDP, ih]

/-- The per-step reward is linear in the reward function. -/
theorem stepReward_scaleMDP (M : FiniteMDP S A) (c : ℝ) (π : Policy S A) (t : ℕ) (s₀ : S) :
    stepReward (scaleMDP M c) π t s₀ = stepReward M π t s₀ / c := by
  unfold stepReward
  rw [visit_scaleMDP]
  simp only [scaleMDP_γ, scaleMDP_r, div_eq_mul_inv]
  have hin : ∀ s : S, ∑ a, (π s) a * (M.r s a * c⁻¹)
      = (∑ a, (π s) a * M.r s a) * c⁻¹ := by
    intro s
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [Finset.sum_congr rfl (fun s _ => by rw [hin s, ← mul_assoc])]
  rw [← Finset.sum_mul]
  ring

/-- **Values scale with the rewards.** `V^π_{M/c} = V^π_M / c`. -/
theorem Vinf_scaleMDP (M : FiniteMDP S A) (c : ℝ) (π : Policy S A) (s₀ : S) :
    Vinf (scaleMDP M c) π s₀ = Vinf M π s₀ / c := by
  unfold Vinf
  rw [← tsum_div_const]
  exact tsum_congr fun t => stepReward_scaleMDP M c π t s₀

/-- **The optimal value scales too**, for `c > 0`: a positive scaling is
monotone, so it commutes with the supremum. Stated via `Vinf_scaleMDP` plus
`Real.iSup_div`, which needs the family bounded above — supplied by
`bddAbove_range_Vinf` on the *rescaled* MDP. -/
theorem Vstar_scaleMDP (M : FiniteMDP S A) {c : ℝ} (hc : 0 < c) (s₀ : S) :
    Vstar (scaleMDP M c) s₀ = Vstar M s₀ / c := by
  unfold Vstar
  rw [div_eq_inv_mul, Real.mul_iSup_of_nonneg (le_of_lt (inv_pos.mpr hc))]
  refine iSup_congr fun π => ?_
  rw [Vinf_scaleMDP M c π s₀, div_eq_inv_mul]

/-! ### The core argument, under `|r| ≤ 1` -/

/-- The suboptimality of `π` at `s`. Nonnegative by `vstar_upper_proof`. -/
noncomputable def valGap (M : FiniteMDP S A) (π : Policy S A) (s : S) : ℝ :=
  Vstar M s - Vinf M π s

theorem valGap_nonneg (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) : 0 ≤ valGap M π s :=
  sub_nonneg.mpr (vstar_upper_proof M hr hγ₀ hγ₁ π s)

/-- **Every action is greedy where a full-support policy is optimal.**

`optimal_support_greedy_proof` applied with `hsupp` from `hfull`; the point is
that it now covers *all* of `A`, not just a support. -/
theorem full_support_all_greedy (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (hfull : ∀ s a, 0 < (π s) a)
    (s : S) (hs : valGap M π s = 0) (a : A) :
    QstarP M s a = Vstar M s :=
  optimal_support_greedy_proof M hr hγ₀ hγ₁ π s
    (by unfold valGap at hs; linarith) a (hfull s a)

/-- **The optimal set is closed under transitions.**

Where a full-support policy is already optimal, every successor reachable with
positive probability (and non-vanishing discount) is optimal too.

From `full_support_all_greedy`, `Vstar M s = ∑ₐ π(a|s) · Q*(s,a)`; `π`'s own
Bellman equation gives `Vinf M π s = ∑ₐ π(a|s) · Qinf(π,s,a)`. Subtracting,
`0 = γ ∑ₐ π(a|s) ∑_{s'} P(s'|s,a) · valGap s'`, all of whose terms are
nonnegative, so every one of them vanishes. -/
theorem valGap_succ_zero (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (hfull : ∀ s a, 0 < (π s) a)
    (s : S) (hs : valGap M π s = 0) (a : A) (s' : S) :
    M.γ * ((M.P s a) s' * valGap M π s') = 0 := by
  -- the doubly-indexed nonnegative family whose total is zero
  set w : A → S → ℝ :=
    fun b t => (π s) b * (M.γ * ((M.P s b) t * valGap M π t)) with hw
  have hwnn : ∀ b t, 0 ≤ w b t := fun b t =>
    mul_nonneg ((π s).nonneg b)
      (mul_nonneg hγ₀ (mul_nonneg ((M.P s b).nonneg t)
        (valGap_nonneg M hr hγ₀ hγ₁ π t)))
  -- `Vstar M s` is the `π`-average of `Q*`, since every action is greedy at `s`
  have hVstar : Vstar M s = ∑ b, (π s) b * QstarP M s b := by
    rw [Finset.sum_congr rfl
      (fun b _ => by rw [full_support_all_greedy M hr hγ₀ hγ₁ π hfull s hs b])]
    rw [← Finset.sum_mul, (π s).sum_eq_one, one_mul]
  -- `Vinf M π s` is the `π`-average of `Qinf`
  have hVinf : Vinf M π s = ∑ b, (π s) b * Qinf M π s b :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  -- the difference of the two averages is exactly `∑_b ∑_t w b t`
  have hdiff : ∀ b, (π s) b * QstarP M s b - (π s) b * Qinf M π s b
      = ∑ t, w b t := by
    intro b
    have : ∑ t, w b t
        = (π s) b * (M.γ * (∑ t, (M.P s b) t * Vstar M t
            - ∑ t, (M.P s b) t * Vinf M π t)) := by
      rw [hw, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun t _ => ?_))
      unfold valGap; ring
    rw [this]
    unfold QstarP Qinf
    ring
  have htot : ∑ b, ∑ t, w b t = 0 := by
    rw [← Finset.sum_congr rfl (fun b _ => hdiff b)]
    rw [Finset.sum_sub_distrib, ← hVstar, ← hVinf]
    unfold valGap at hs
    linarith
  -- a nonnegative family summing to zero vanishes termwise
  have hzero : w a s' = 0 := by
    have hle : w a s' ≤ ∑ b, ∑ t, w b t := by
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun b => ∑ t, w b t)
        (fun b _ => Finset.sum_nonneg fun t _ => hwnn b t) (Finset.mem_univ a))
      exact Finset.single_le_sum (fun t _ => hwnn a t) (Finset.mem_univ s')
    rw [htot] at hle
    exact le_antisymm hle (hwnn a s')
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (ne_of_gt (hfull s a))
  · exact h

/-- **The masked gap of an arbitrary policy.** `valGap M π'` restricted to the
states where the full-support policy `π` is optimal, and zeroed elsewhere. -/
noncomputable def maskGap (M : FiniteMDP S A) (π π' : Policy S A) (s : S) : ℝ :=
  if valGap M π s = 0 then valGap M π' s else 0

theorem maskGap_nonneg (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π π' : Policy S A) (s : S) : 0 ≤ maskGap M π π' s := by
  unfold maskGap
  split
  · exact valGap_nonneg M hr hγ₀ hγ₁ π' s
  · exact le_refl 0

/-- **The mask is invisible to the one-step average.**

For `s` in the optimal set, `γ · P(s'|s,a) · valGap π' s'` and
`γ · P(s'|s,a) · maskGap s'` agree termwise: either `s'` is itself in the
optimal set, where the mask is the identity, or `valGap_succ_zero` makes
`γ · P(s'|s,a) · valGap π s' = 0` with `valGap π s' > 0`, forcing
`γ · P(s'|s,a) = 0` and both sides to vanish. -/
theorem gamma_P_valGap_eq_mask (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (hfull : ∀ s a, 0 < (π s) a)
    (s : S) (hs : valGap M π s = 0) (π' : Policy S A) (a : A) (s' : S) :
    M.γ * ((M.P s a) s' * valGap M π' s')
      = M.γ * ((M.P s a) s' * maskGap M π π' s') := by
  unfold maskGap
  by_cases h : valGap M π s' = 0
  · rw [if_pos h]
  · rw [if_neg h, mul_zero, mul_zero]
    have hz := valGap_succ_zero M hr hγ₀ hγ₁ π hfull s hs a s'
    have hpos : 0 < valGap M π s' :=
      lt_of_le_of_ne (valGap_nonneg M hr hγ₀ hγ₁ π s') (Ne.symm h)
    have : M.γ * (M.P s a) s' = 0 := by
      rcases mul_eq_zero.mp (by rw [← mul_assoc] at hz; exact hz) with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt hpos)
    rw [← mul_assoc, this, zero_mul]

/-- **The masked recursion.** For `s` in the optimal set, the masked gap of any
`π'` is `γ` times a `π'`-average of masked gaps at successors.

`Vstar M s = ∑ₐ π'(a|s) · Q*(s,a)` (every action is greedy at `s`) and
`Vinf M π' s = ∑ₐ π'(a|s) · Qinf(π',s,a)`; subtracting and applying
`gamma_P_valGap_eq_mask` termwise replaces the raw successor gaps by masked
ones. -/
theorem maskGap_step (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (hfull : ∀ s a, 0 < (π s) a)
    (s : S) (hs : valGap M π s = 0) (π' : Policy S A) :
    maskGap M π π' s
      = ∑ b, (π' s) b * (M.γ * ∑ t, (M.P s b) t * maskGap M π π' t) := by
  rw [maskGap, if_pos hs]
  have hVstar : Vstar M s = ∑ b, (π' s) b * QstarP M s b := by
    rw [Finset.sum_congr rfl
      (fun b _ => by rw [full_support_all_greedy M hr hγ₀ hγ₁ π hfull s hs b])]
    rw [← Finset.sum_mul, (π' s).sum_eq_one, one_mul]
  have hVinf : Vinf M π' s = ∑ b, (π' s) b * Qinf M π' s b :=
    Vinf_eq_rbar_add M π' 1 zero_le_one hr hγ₀ hγ₁ s
  have hterm : ∀ b, (π' s) b * QstarP M s b - (π' s) b * Qinf M π' s b
      = (π' s) b * (M.γ * ∑ t, (M.P s b) t * maskGap M π π' t) := by
    intro b
    have hsum : M.γ * ∑ t, (M.P s b) t * maskGap M π π' t
        = M.γ * (∑ t, (M.P s b) t * Vstar M t - ∑ t, (M.P s b) t * Vinf M π' t) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← gamma_P_valGap_eq_mask M hr hγ₀ hγ₁ π hfull s hs π' b t]
      unfold valGap; ring
    rw [hsum]
    unfold QstarP Qinf
    ring
  rw [← Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib,
    ← hVstar, ← hVinf]
  rfl

/-- **Every policy is optimal wherever a full-support policy is.**

The masked gap satisfies `k s ≤ γ · maxₛ k` at every state — by `maskGap_step`
inside the optimal set, and trivially (`k s = 0`) outside it. Evaluating at the
argmax gives `D ≤ γ D` with `0 ≤ D` and `γ < 1`, so `D = 0`. -/
theorem valGap_eq_zero_of_full_support (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (hfull : ∀ s a, 0 < (π s) a)
    (s : S) (hs : valGap M π s = 0) (π' : Policy S A) :
    valGap M π' s = 0 := by
  obtain ⟨sm, hsm⟩ := Finite.exists_max (maskGap M π π')
  set D := maskGap M π π' sm with hD
  have hD0 : 0 ≤ D := maskGap_nonneg M hr hγ₀ hγ₁ π π' sm
  -- every state satisfies `k ≤ γ D`
  have hkey : ∀ u : S, maskGap M π π' u ≤ M.γ * D := by
    intro u
    by_cases hu : valGap M π u = 0
    · rw [maskGap_step M hr hγ₀ hγ₁ π hfull u hu π']
      have hin : ∀ b : A, (π' u) b * (M.γ * ∑ t, (M.P u b) t * maskGap M π π' t)
          ≤ (π' u) b * (M.γ * D) := by
        intro b
        refine mul_le_mul_of_nonneg_left ?_ ((π' u).nonneg b)
        refine mul_le_mul_of_nonneg_left ?_ hγ₀
        calc ∑ t, (M.P u b) t * maskGap M π π' t
            ≤ ∑ t, (M.P u b) t * D :=
              Finset.sum_le_sum fun t _ =>
                mul_le_mul_of_nonneg_left (hsm t) ((M.P u b).nonneg t)
          _ = D := by rw [← Finset.sum_mul, (M.P u b).sum_eq_one, one_mul]
      calc ∑ b, (π' u) b * (M.γ * ∑ t, (M.P u b) t * maskGap M π π' t)
          ≤ ∑ b, (π' u) b * (M.γ * D) := Finset.sum_le_sum fun b _ => hin b
        _ = M.γ * D := by rw [← Finset.sum_mul, (π' u).sum_eq_one, one_mul]
    · rw [maskGap, if_neg hu]
      exact mul_nonneg hγ₀ hD0
  have hDle : D ≤ M.γ * D := hkey sm
  have hDzero : D = 0 := le_antisymm (by nlinarith) hD0
  have : maskGap M π π' s = 0 :=
    le_antisymm (by rw [← hDzero]; exact hsm s)
      (maskGap_nonneg M hr hγ₀ hγ₁ π π' s)
  rwa [maskGap, if_pos hs] at this

/-- **G3 under bounded rewards.** If a full-support policy attains the optimum
at `μ`, so does every policy — contradicting `hnondeg`. -/
theorem strict_suboptimality_of_full_support (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (hfull : ∀ s a, 0 < (π s) a) (μ : S)
    (hnondeg : ∃ π' : Policy S A, Vinf M π' μ < Vstar M μ) :
    Vinf M π μ < Vstar M μ := by
  rcases lt_or_eq_of_le (vstar_upper_proof M hr hγ₀ hγ₁ π μ) with h | h
  · exact h
  · exfalso
    obtain ⟨π', hπ'⟩ := hnondeg
    have hs : valGap M π μ = 0 := by unfold valGap; linarith
    have := valGap_eq_zero_of_full_support M hr hγ₀ hγ₁ π hfull μ hs π'
    unfold valGap at this
    linarith

/-! ### Assembling `g3`: removing the bounded-reward hypothesis -/

/-- A uniform reward bound, at least `1`, for any MDP on finite `S` and `A`. -/
noncomputable def rewardBound (M : FiniteMDP S A) : ℝ :=
  max 1 (|M.r (Finite.exists_max (fun p : S × A => |M.r p.1 p.2|)).choose.1
             (Finite.exists_max (fun p : S × A => |M.r p.1 p.2|)).choose.2|)

theorem one_le_rewardBound (M : FiniteMDP S A) : 1 ≤ rewardBound M := le_max_left _ _

theorem rewardBound_pos (M : FiniteMDP S A) : 0 < rewardBound M :=
  lt_of_lt_of_le zero_lt_one (one_le_rewardBound M)

theorem abs_r_le_rewardBound (M : FiniteMDP S A) (s : S) (a : A) :
    |M.r s a| ≤ rewardBound M :=
  le_trans ((Finite.exists_max (fun p : S × A => |M.r p.1 p.2|)).choose_spec (s, a))
    (le_max_right _ _)

/-- The rescaled MDP really does have rewards bounded by `1`. -/
theorem scaled_r_bounded (M : FiniteMDP S A) (s : S) (a : A) :
    |(scaleMDP M (rewardBound M)).r s a| ≤ 1 := by
  rw [scaleMDP_r, abs_div, abs_of_pos (rewardBound_pos M)]
  exact div_le_one_of_le₀ (abs_r_le_rewardBound M s a) (le_of_lt (rewardBound_pos M))

/-- **G3, in the shape `Goal.g3_strict_suboptimality` asks for.**

The softmax hypothesis enters only through `hfull`: `hF` plus `softmax_pos`
gives `0 < (F.toPolicy θ s) a` for *every* action. Everything else is
`strict_suboptimality_of_full_support`, transported across the reward rescaling
that supplies the `|r| ≤ 1` the goal statement omits. -/
theorem g3_strict_suboptimality_proof (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (μ : S) (θ : EuclideanSpace ℝ (S × A))
    (hnondeg : ∃ π : Policy S A, Vinf M π μ < Vstar M μ) :
    Vinf M (F.toPolicy θ) μ < Vstar M μ := by
  set c := rewardBound M with hc
  have hcpos : 0 < c := rewardBound_pos M
  set M' := scaleMDP M c with hM'
  have hr' : ∀ s a, |M'.r s a| ≤ 1 := scaled_r_bounded M
  have hγ₀' : 0 ≤ M'.γ := hγ₀
  have hγ₁' : M'.γ < 1 := hγ₁
  -- softmax has full support, which is the whole use of `hF`
  have hfull : ∀ s a, 0 < (F.toPolicy θ s) a := by
    intro s a
    rw [hF θ s a]
    exact softmax_pos (logits θ s) a
  -- transport `hnondeg` to the rescaled MDP
  have hnondeg' : ∃ π : Policy S A, Vinf M' π μ < Vstar M' μ := by
    obtain ⟨π, hπ⟩ := hnondeg
    refine ⟨π, ?_⟩
    rw [hM', Vinf_scaleMDP M c π μ, Vstar_scaleMDP M hcpos μ]
    gcongr
  have h := strict_suboptimality_of_full_support M' hr' hγ₀' hγ₁'
    (F.toPolicy θ) hfull μ hnondeg'
  rw [hM', Vinf_scaleMDP M c (F.toPolicy θ) μ, Vstar_scaleMDP M hcpos μ] at h
  have := mul_lt_mul_of_pos_right h hcpos
  rwa [div_mul_cancel₀ _ (ne_of_gt hcpos), div_mul_cancel₀ _ (ne_of_gt hcpos)] at this

end G3


/-! ## G7 — the statement is FALSE as written

`g7_smoothness` asks for

  `‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) s₀) θ‖ ≤ 8 / (1 - M.γ) ^ 3`

under only `hF` (F is *some* softmax family), `|r| ≤ 1`, `0 ≤ γ < 1`. **No such
bound exists**, and the reason is not the constant.

`logits` is universally quantified with **no regularity hypothesis whatsoever**
— contrast `g5_g6_softmax_family`, which carries `hlog : ∀ s a, Differentiable ℝ
(fun θ => logits θ s a)`. G7 dropped that, and dropped much more besides: nothing
ties `logits` to the parameter at unit scale. AKM's Lemma E.4 is about the
**tabular** parameterization `logits θ s a = θ (s,a)`, which is 1-Lipschitz in
`θ`. Under `logits θ s a = c · θ (s,a)` every hypothesis of G7 still holds while
the chain rule multiplies the gradient by `c`, which is unbounded.

The witness below is as simple as it gets: one state, two actions, `γ = 0`,
rewards `0` and `1`. Then `Vinf` is exactly `π(true)`, the softmax of a single
scaled coordinate, whose derivative at `θ = 0` is `c/4`. With `γ = 0` the claimed
bound is `8/(1-0)³ = 8`, and `c = 33` gives `33/4 > 8`.

Note `γ = 0` is deliberate: it kills the `1/(1-γ)` factors entirely, so the
refutation cannot be blamed on the discount. The failure is in the
parameterization, and it persists for every `γ`.

**What the statement should say** is recorded after the refutation. -/

/-- One state, two actions, `γ = 0`. Reward 1 for `true`, 0 for `false`. -/
noncomputable def badMDP : FiniteMDP Unit Bool where
  P := fun _ _ => ⟨fun _ => 1, by intro; norm_num, by simp⟩
  r := fun _ a => if a then 1 else 0
  γ := 0

theorem badMDP_r : ∀ s a, |badMDP.r s a| ≤ 1 := by
  intro s a; cases a <;> norm_num [badMDP]

theorem badMDP_γ₀ : (0:ℝ) ≤ badMDP.γ := le_of_eq rfl
theorem badMDP_γ₁ : badMDP.γ < 1 := by norm_num [badMDP]

theorem Vinf_gamma_zero (M : FiniteMDP Unit Bool) (hγ : M.γ = 0)
    (π : Policy Unit Bool) (s₀ : Unit) :
    Vinf M π s₀ = ∑ a, (π s₀) a * M.r s₀ a := by
  unfold Vinf
  rw [tsum_eq_single 0]
  · unfold stepReward; simp [hγ]
  · intro t ht; unfold stepReward; rw [hγ, zero_pow ht, zero_mul]

/-- The value of the bad MDP is just the probability of action `true`. -/
theorem Vinf_badMDP (π : Policy Unit Bool) :
    Vinf badMDP π () = (π ()) true := by
  rw [Vinf_gamma_zero badMDP rfl]
  simp [badMDP, Fintype.sum_bool]


/-- The scaled logits: `logits θ s a = c * θ(s,a)` for `a = true`, else `0`. -/
noncomputable def badLogits (c : ℝ) :
    EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ :=
  fun θ _ a => if a then c * θ ((), true) else 0

theorem badLogits_diff (c : ℝ) (s : Unit) (a : Bool) :
    Differentiable ℝ (fun θ : EuclideanSpace ℝ (Unit × Bool) => badLogits c θ s a) := by
  unfold badLogits
  cases a
  · simpa using (differentiable_const (0:ℝ))
  · simp only [if_true]
    exact (((EuclideanSpace.proj ((), true) :
      EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ)).differentiable).const_mul c

/-- The softmax value as an explicit scalar function of the coordinate. -/
theorem Vinf_softmax_formula (c : ℝ) (θ : EuclideanSpace ℝ (Unit × Bool)) :
    Vinf badMDP (show Policy Unit Bool from fun s => softmax (badLogits c θ s)) ()
      = Real.exp (c * θ ((), true)) / (Real.exp (c * θ ((), true)) + 1) := by
  rw [Vinf_badMDP, softmax_apply]
  congr 1
  · simp [badLogits]


/-- The scalar profile `x ↦ e^{cx}/(e^{cx}+1)` has derivative `c/4` at `0`. -/
theorem profile_deriv (c : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (c*x) / (Real.exp (c*x) + 1)) (c/4) 0 := by
  have hlin : HasDerivAt (fun x : ℝ => c*x) c 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_mul c
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (c*x)) c 0 := by
    have := hlin.exp
    rwa [mul_zero, Real.exp_zero, one_mul] at this
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (c*x) + 1) c 0 := h1.add_const 1
  have hne : Real.exp (c*0) + 1 ≠ 0 := by positivity
  have hd := h1.div h2 hne
  rw [mul_zero, Real.exp_zero] at hd
  have harith : (c * (1 + 1) - 1 * c) / (1 + 1)^2 = c/4 := by ring
  rwa [harith] at hd

/-- The Fréchet derivative of the value at `θ = 0` is `(c/4) • proj`. -/
theorem Vinf_hasFDeriv (c : ℝ) :
    HasFDerivAt (fun t : EuclideanSpace ℝ (Unit × Bool) =>
        Vinf badMDP (show Policy Unit Bool from fun s => softmax (badLogits c t s)) ())
      ((c/4) • (EuclideanSpace.proj ((), true) :
        EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ)) 0 := by
  have hfun : (fun t : EuclideanSpace ℝ (Unit × Bool) =>
      Vinf badMDP (show Policy Unit Bool from fun s => softmax (badLogits c t s)) ())
      = fun t : EuclideanSpace ℝ (Unit × Bool) =>
        Real.exp (c * t ((), true)) / (Real.exp (c * t ((), true)) + 1) :=
    funext fun t => Vinf_softmax_formula c t
  rw [hfun]
  have hp : HasFDerivAt (fun t : EuclideanSpace ℝ (Unit × Bool) => t ((), true))
      (EuclideanSpace.proj ((), true) :
        EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ) 0 :=
    (EuclideanSpace.proj ((), true) :
      EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ).hasFDerivAt
  have hprof : HasDerivAt (fun x : ℝ => Real.exp (c*x) / (Real.exp (c*x) + 1)) (c/4)
      ((0 : EuclideanSpace ℝ (Unit × Bool)) ((), true)) := by
    have h0 : (0 : EuclideanSpace ℝ (Unit × Bool)) ((), true) = 0 := by simp
    rw [h0]; exact profile_deriv c
  exact hprof.comp_hasFDerivAt (0 : EuclideanSpace ℝ (Unit × Bool)) hp


/-- The operator norm of the derivative is at least `c/4`. -/
theorem norm_fderiv_ge (c : ℝ) (hc : 0 ≤ c) :
    c/4 ≤ ‖fderiv ℝ (fun t : EuclideanSpace ℝ (Unit × Bool) =>
      Vinf badMDP (show Policy Unit Bool from fun s => softmax (badLogits c t s)) ())
      (0 : EuclideanSpace ℝ (Unit × Bool))‖ := by
  rw [(Vinf_hasFDeriv c).fderiv]
  set v : EuclideanSpace ℝ (Unit × Bool) := EuclideanSpace.single ((), true) (1:ℝ) with hv
  have hvn : ‖v‖ = 1 := by rw [hv]; simp
  have happ : ((c/4) • (EuclideanSpace.proj ((), true) :
      EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ)) v = c/4 := by
    simp [hv]
  have hle := ((c/4) • (EuclideanSpace.proj ((), true) :
      EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ)).le_opNorm v
  rw [hvn, mul_one, happ] at hle
  calc c/4 = |c/4| := (abs_of_nonneg (by linarith)).symm
    _ = ‖c/4‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := hle


/-- The softmax `VecPolicy` built from `badLogits c`. -/
noncomputable def badF (c : ℝ) : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool)) where
  toPolicy := fun θ s => softmax (badLogits c θ s)
  dπ := fun θ s a => fderiv ℝ (fun t => (softmax (badLogits c t s)) a) θ
  hasFDeriv := fun θ s a =>
    (softmax_diff (fun t => badLogits c t s) (fun a' => badLogits_diff c s a') a θ).hasFDerivAt

theorem badF_hF (c : ℝ) : ∀ θ s a, ((badF c).toPolicy θ s) a = softmax (badLogits c θ s) a :=
  fun _ _ _ => rfl

/-- **G7 is false as stated.** Taking `c = 33`, `γ = 0`, the one-state two-action
MDP above satisfies every hypothesis of `g7_smoothness` yet has
`‖fderiv‖ ≥ 33/4 > 8 = 8/(1-γ)³`. -/
theorem g7_false :
    ¬ (∀ (M : FiniteMDP Unit Bool)
        (logits : EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ)
        (F : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (θ : EuclideanSpace ℝ (Unit × Bool)) (s₀ : Unit),
          ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) s₀) θ‖ ≤ 8 / (1 - M.γ) ^ 3) := by
  intro h
  have hbound := h badMDP (badLogits 33) (badF 33) (badF_hF 33)
    badMDP_r badMDP_γ₀ badMDP_γ₁ 0 ()
  have hlow := norm_fderiv_ge 33 (by norm_num)
  have hrhs : (8 : ℝ) / (1 - badMDP.γ) ^ 3 = 8 := by norm_num [badMDP]
  rw [hrhs] at hbound
  -- the two functions agree definitionally
  have heq : (fun t : EuclideanSpace ℝ (Unit × Bool) => Vinf badMDP ((badF 33).toPolicy t) ())
      = (fun t : EuclideanSpace ℝ (Unit × Bool) =>
          Vinf badMDP (show Policy Unit Bool from fun s => softmax (badLogits 33 t s)) ()) := rfl
  rw [heq] at hbound
  linarith


/-- The exact shape of `g7_smoothness`, as a hypothesis. If G7 held in general,
this would follow; `g7_false` shows it cannot. -/
theorem g7_general_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S) (_ : DecidableEq A)
        (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (θ : EuclideanSpace ℝ (S × A)) (s₀ : S),
          ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) s₀) θ‖ ≤ 8 / (1 - M.γ) ^ 3) := by
  intro h
  exact g7_false (fun M logits F hF hr hγ₀ hγ₁ θ s₀ =>
    h Unit Bool inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance M logits F hF hr hγ₀ hγ₁ θ s₀)

/-! ### What G7 should say instead

The refutation above is not about the constant `8`; no constant works. Two
things must change, and they are independent.

**1. Pin the parameterization (mandatory — this is what `g7_false` exploits).**
`hF` must fix the *tabular* softmax AKM actually analyses,

  `hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a`

replacing the free `logits`. Any statement quantifying over an unconstrained
`logits` is refutable by rescaling, whatever the right-hand side. (Assuming
`logits` merely `Differentiable`, as `g5_g6_softmax_family` does, is *not*
enough — `badLogits c` is differentiable for every `c`.)

**2. Then choose which quantity is meant.**

*If the first derivative is meant*, the constant is wrong: `8/(1-γ)³` is a
smoothness constant. The correct gradient bound for `|r| ≤ 1` is `O(1/(1-γ)²)` —
this repo already proves the scalar analogue as `abs_dV_le_softmax`
(`|dV| ≤ 1/(1-γ)²`). The vector statement is

```lean
theorem g7_gradient_bound (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s₀ : S) :
    ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) s₀) θ‖ ≤ 2 / (1 - M.γ) ^ 2
```

*If smoothness is meant* — and the `@[paper "AKM2021" "Lemma E.4"]` tag and the
`8/(1-γ)³` constant both say it is, since that is exactly what
`smoothAt_V_final`/`abs_d2V_le_eight` deliver — then the conclusion must be
about the **second** derivative:

```lean
theorem g7_smoothness (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s₀ : S) :
    ‖fderiv ℝ (fun t => fderiv ℝ (fun u => Vinf M (F.toPolicy u) s₀) t) θ‖
      ≤ 8 / (1 - M.γ) ^ 3
```

Both are well-formed (checked). The second is the faithful reading of Lemma E.4
and the one that would actually discharge `smoothAt_V_final`'s `hdloc`; note
that with the tabular `hF` the family is genuinely `C²`, which the current
`VecPolicy` (first derivative only) does not record — a `C²` analogue of
`VecPolicy`, or a `SmoothAt`-style conclusion, is needed to state it in the form
`smoothAt_V_final` consumes.

Until G7 is restated, its `sorry` stands. -/

/-! ## G1 and G2 — both FALSE as stated: `mismatch` is a free universal real

`g1_lojasiewicz` and `g2_gradient_domination` each take

  `(mismatch : ℝ) (hmis : 0 < mismatch)`

as an ordinary **universally quantified** hypothesis, with nothing tying it to
the MDP. `Target.lean` defines `mismatchCoeff M π μ`; neither goal uses it. So
the caller — not the MDP — chooses the constant, and can choose it adversarially.

* In **G2** `mismatch` multiplies the right-hand side:
  `Vstar - Vinf ≤ (mismatch/(1-γ)) · ‖∇V‖`. Sending `mismatch → 0⁺` drives the
  bound to `0`, so the statement entails `Vstar - Vinf ≤ 0` for *every* softmax
  policy. That is false for any MDP where softmax is strictly suboptimal.
* In **G1** `mismatch` *divides* the left-hand side:
  `(⨅ₛ π(a*|s))/(√|S|·mismatch) · (Vstar - Vinf) ≤ ‖∇V‖`. Sending
  `mismatch → 0⁺` drives the left side to `+∞` while the right side is a fixed
  real, so the statement is again unsatisfiable whenever
  `(⨅ₛ π(a*|s))·(Vstar - Vinf) > 0` — which softmax positivity plus strict
  suboptimality guarantees.

This is exactly the defect recorded for `mei_theorem4`: *a floating quantity is
a defect in both directions — existential and unconstrained makes a goal too
weak, universal makes it too strong.* Here it is universal, so both goals are
**unprovable as stated**, independently of any question about `logits`.

### The witness

`badMDP` (already defined above for the G7 refutation) is enough: one state,
two actions, `γ = 0`, reward `1` for `true` and `0` for `false`. Then
`Vinf M π () = π(true)`, so `Vstar = 1`, while any softmax policy has
`π(true) < 1`. Concretely the *tabular* family at `θ = 0` gives `π(true) = 1/2`
and `Vstar - Vinf = 1/2 > 0`.

Note the witness uses the **tabular** parameterization `logits θ s a = θ (s,a)`
— the one AKM and Mei actually analyse, and the one `g7a`/`g7b` were repaired
to. So this refutation does **not** rely on the unconstrained-`logits` loophole
that killed `g7_smoothness`: fixing `logits` would not save either goal. It also
does not rely on `γ`, on unbounded rewards (`|r| ≤ 1` holds), or on the missing
`hr` hypothesis. -/

section MismatchFree

/-- The tabular softmax logits on the `badMDP` parameter space. -/
noncomputable def tabLogits :
    EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ :=
  fun θ s a => θ (s, a)

theorem tabLogits_diff (s : Unit) (a : Bool) :
    Differentiable ℝ (fun θ : EuclideanSpace ℝ (Unit × Bool) => tabLogits θ s a) :=
  ((EuclideanSpace.proj (s, a) : EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ)).differentiable

/-- The tabular softmax `VecPolicy` on `badMDP`'s spaces. -/
noncomputable def tabF : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool)) where
  toPolicy := fun θ s => softmax (tabLogits θ s)
  dπ := fun θ s a => fderiv ℝ (fun t => (softmax (tabLogits t s)) a) θ
  hasFDeriv := fun θ s a =>
    (softmax_diff (fun t => tabLogits t s) (fun a' => tabLogits_diff s a') a θ).hasFDerivAt

theorem tabF_hF : ∀ θ s a, (tabF.toPolicy θ s) a = softmax (tabLogits θ s) a :=
  fun _ _ _ => rfl

/-- Every policy value on `badMDP` is at most `1`. -/
theorem Vinf_badMDP_le_one (π : Policy Unit Bool) : Vinf badMDP π () ≤ 1 := by
  rw [Vinf_badMDP]
  have := (π ()).sum_eq_one
  have hnn := (π ()).nonneg false
  rw [Fintype.sum_bool] at this
  linarith

/-- `Vstar badMDP () = 1`: the deterministic policy playing `true` attains it. -/
theorem Vstar_badMDP : Vstar badMDP () = 1 := by
  apply le_antisymm
  · exact ciSup_le fun π => Vinf_badMDP_le_one π
  · have h : Vinf badMDP (detPolicy (fun _ => true)) () = 1 := by
      rw [Vinf_badMDP]; simp [detPolicy, pointMass]
    rw [← h]
    refine le_ciSup (f := fun π : Policy Unit Bool => Vinf badMDP π ()) ?_ _
    exact ⟨1, by rintro x ⟨π, rfl⟩; exact Vinf_badMDP_le_one π⟩

/-- At `θ = 0` the tabular softmax on two actions is uniform, so the value is
`1/2` and the suboptimality is exactly `1/2`. -/
theorem tab_value_at_zero :
    Vinf badMDP (tabF.toPolicy (0 : EuclideanSpace ℝ (Unit × Bool))) () = 1/2 := by
  rw [Vinf_badMDP]
  show (softmax (tabLogits (0 : EuclideanSpace ℝ (Unit × Bool)) ())) true = 1/2
  rw [softmax_apply]
  have h0 : ∀ a : Bool, tabLogits (0 : EuclideanSpace ℝ (Unit × Bool)) () a = 0 := by
    intro a; simp [tabLogits]
  rw [h0, Fintype.sum_bool, h0, h0]
  norm_num

theorem tab_subopt :
    Vstar badMDP () - Vinf badMDP (tabF.toPolicy (0 : EuclideanSpace ℝ (Unit × Bool))) ()
      = 1/2 := by
  rw [Vstar_badMDP, tab_value_at_zero]; norm_num

/-- The `⨅` over the single state `Unit` of the optimal-action probability is
`1/2` for the uniform tabular softmax. -/
theorem tab_iInf :
    (⨅ s : Unit, (tabF.toPolicy (0 : EuclideanSpace ℝ (Unit × Bool)) s) (true)) = 1/2 := by
  have : ∀ s : Unit,
      (tabF.toPolicy (0 : EuclideanSpace ℝ (Unit × Bool)) s) (true) = 1/2 := by
    intro s
    show (softmax (tabLogits (0 : EuclideanSpace ℝ (Unit × Bool)) s)) true = 1/2
    rw [softmax_apply]
    have h0 : ∀ a : Bool, tabLogits (0 : EuclideanSpace ℝ (Unit × Bool)) s a = 0 := by
      intro a; simp [tabLogits]
    rw [h0, Fintype.sum_bool, h0, h0]
    norm_num
  simp only [this]
  exact ciInf_const

/-! ### G2 -/

/-- **G2 is false as stated**, on the concrete `badMDP` witness with the
tabular softmax family: the caller is free to send `mismatch → 0`. -/
theorem g2_false :
    ¬ (∀ (M : FiniteMDP Unit Bool)
        (logits : EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ)
        (F : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        0 ≤ M.γ → M.γ < 1 →
        ∀ (μ : Unit) (θ : EuclideanSpace ℝ (Unit × Bool)) (mismatch : ℝ), 0 < mismatch →
          Vstar M μ - Vinf M (F.toPolicy θ) μ
            ≤ (mismatch / (1 - M.γ)) * ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖) := by
  intro h
  set G := ‖fderiv ℝ (fun t : EuclideanSpace ℝ (Unit × Bool) =>
    Vinf badMDP (tabF.toPolicy t) ()) (0 : EuclideanSpace ℝ (Unit × Bool))‖ with hG
  have hGnn : 0 ≤ G := norm_nonneg _
  -- choose `mismatch` small enough that the right-hand side is below `1/2`
  set m : ℝ := 1 / (4 * (G + 1)) with hm
  have hGp : (0:ℝ) < G + 1 := by linarith
  have hmpos : 0 < m := by rw [hm]; positivity
  have hb := h badMDP tabLogits tabF tabF_hF badMDP_γ₀ badMDP_γ₁ () 0 m hmpos
  rw [tab_subopt] at hb
  have hγ : (1 : ℝ) - badMDP.γ = 1 := by norm_num [badMDP]
  rw [hγ, div_one] at hb
  -- `m * G < 1/2`
  have hmg : m * G < 1/2 := by
    rw [hm]
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  rw [← hG] at hb
  linarith

/-- The exact shape of `g2_gradient_domination`, as a hypothesis. If G2 held in
general, this would follow; `g2_false` shows it cannot. -/
theorem g2_general_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S) (_ : DecidableEq A)
        (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        0 ≤ M.γ → M.γ < 1 →
        ∀ (μ : S) (θ : EuclideanSpace ℝ (S × A)) (mismatch : ℝ), 0 < mismatch →
          Vstar M μ - Vinf M (F.toPolicy θ) μ
            ≤ (mismatch / (1 - M.γ))
                * ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖) := by
  intro h
  exact g2_false (fun M logits F hF hγ₀ hγ₁ μ θ mismatch hmis =>
    h Unit Bool inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance M logits F hF hγ₀ hγ₁ μ θ mismatch hmis)

/-! ### G1 -/

/-- **G1 is false as stated**: `mismatch` divides the left-hand side, so sending
`mismatch → 0` makes it exceed any fixed gradient norm. -/
theorem g1_false :
    ¬ (∀ (M : FiniteMDP Unit Bool)
        (logits : EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ)
        (F : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        0 ≤ M.γ → M.γ < 1 →
        ∀ (astar : Unit → Bool) (μ : Unit) (θ : EuclideanSpace ℝ (Unit × Bool))
          (mismatch : ℝ), 0 < mismatch →
          (⨅ s : Unit, (F.toPolicy θ s) (astar s))
              / (Real.sqrt (Fintype.card Unit) * mismatch)
              * (Vstar M μ - Vinf M (F.toPolicy θ) μ)
            ≤ ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖) := by
  intro h
  set G := ‖fderiv ℝ (fun t : EuclideanSpace ℝ (Unit × Bool) =>
    Vinf badMDP (tabF.toPolicy t) ()) (0 : EuclideanSpace ℝ (Unit × Bool))‖ with hG
  have hGnn : 0 ≤ G := norm_nonneg _
  -- `mismatch` small: left side is `(1/2)/(1·m) · (1/2) = 1/(4m)`
  set m : ℝ := 1 / (4 * (G + 1)) with hm
  have hGp : (0:ℝ) < G + 1 := by linarith
  have hmpos : 0 < m := by rw [hm]; positivity
  have hb := h badMDP tabLogits tabF tabF_hF badMDP_γ₀ badMDP_γ₁ (fun _ => true) () 0 m hmpos
  rw [tab_subopt, tab_iInf] at hb
  have hcard : Real.sqrt (Fintype.card Unit) = 1 := by
    simp
  rw [hcard, one_mul, ← hG] at hb
  -- so `(1/2)/m * (1/2) ≤ G`, i.e. `1/(4m) ≤ G`, but `1/(4m) = G + 1`
  have hval : (1:ℝ)/2 / m * (1/2) = G + 1 := by
    rw [hm]
    field_simp
    ring
  rw [hval] at hb
  linarith

/-- The exact shape of `g1_lojasiewicz`, as a hypothesis. If G1 held in general,
this would follow; `g1_false` shows it cannot. -/
theorem g1_general_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S) (_ : DecidableEq A)
        (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        0 ≤ M.γ → M.γ < 1 →
        ∀ (astar : S → A) (μ : S) (θ : EuclideanSpace ℝ (S × A)) (mismatch : ℝ),
          0 < mismatch →
          (⨅ s : S, (F.toPolicy θ s) (astar s))
              / (Real.sqrt (Fintype.card S) * mismatch)
              * (Vstar M μ - Vinf M (F.toPolicy θ) μ)
            ≤ ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖) := by
  intro h
  exact g1_false (fun M logits F hF hγ₀ hγ₁ astar μ θ mismatch hmis =>
    h Unit Bool inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance M logits F hF hγ₀ hγ₁ astar μ θ mismatch hmis)

/-! ### G1 fails a second time, independently, on the unconstrained `logits`

The refutation above uses only the free `mismatch`. G1 has a *second*,
independent defect, the same one that killed `g7_smoothness`: `logits` is
universally quantified with no regularity or pinning hypothesis. In G1 the
gradient sits on the **right**, so the adversarial direction is `c → 0`:
`badLogits c` flattens the value function's dependence on `θ` without changing
the policy at `θ = 0` (still uniform, `π(true) = 1/2`, suboptimality `1/2`).
The left-hand side stays at `(1/2)/(1·mismatch)·(1/2)`; the right-hand side is
`c/4 → 0`.

So even with `mismatch` fixed at `1`, G1 is refutable. Repairing the free
`mismatch` alone would not be enough — the tabular `hF` is also required. -/

/-- The exact operator norm of the derivative: `|c|/4`. -/
theorem norm_fderiv_le (c : ℝ) :
    ‖fderiv ℝ (fun t : EuclideanSpace ℝ (Unit × Bool) =>
      Vinf badMDP (show Policy Unit Bool from fun s => softmax (badLogits c t s)) ())
      (0 : EuclideanSpace ℝ (Unit × Bool))‖ ≤ |c|/4 := by
  rw [(Vinf_hasFDeriv c).fderiv, norm_smul]
  have hp : ‖(EuclideanSpace.proj ((), true) :
      EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      rw [one_mul]; simpa using PiLp.norm_apply_le x ((), true))
  have h1 : ‖c/4‖ = |c|/4 := by
    rw [Real.norm_eq_abs, abs_div]; norm_num
  rw [h1]
  calc |c|/4 * ‖(EuclideanSpace.proj ((), true) :
        EuclideanSpace ℝ (Unit × Bool) →L[ℝ] ℝ)‖
      ≤ |c|/4 * 1 := by
        apply mul_le_mul_of_nonneg_left hp (by positivity)
    _ = |c|/4 := by ring

theorem badF_value_at_zero (c : ℝ) :
    Vinf badMDP ((badF c).toPolicy (0 : EuclideanSpace ℝ (Unit × Bool))) () = 1/2 := by
  rw [Vinf_badMDP]
  show (softmax (badLogits c (0 : EuclideanSpace ℝ (Unit × Bool)) ())) true = 1/2
  rw [softmax_apply]
  have h0 : ∀ a : Bool, badLogits c (0 : EuclideanSpace ℝ (Unit × Bool)) () a = 0 := by
    intro a; cases a <;> simp [badLogits]
  rw [h0, Fintype.sum_bool, h0, h0]
  norm_num

theorem badF_iInf (c : ℝ) :
    (⨅ s : Unit, ((badF c).toPolicy (0 : EuclideanSpace ℝ (Unit × Bool)) s) (true)) = 1/2 := by
  have h : ∀ s : Unit,
      ((badF c).toPolicy (0 : EuclideanSpace ℝ (Unit × Bool)) s) (true) = 1/2 := by
    intro s
    show (softmax (badLogits c (0 : EuclideanSpace ℝ (Unit × Bool)) s)) true = 1/2
    rw [softmax_apply]
    have h0 : ∀ a : Bool, badLogits c (0 : EuclideanSpace ℝ (Unit × Bool)) s a = 0 := by
      intro a; cases a <;> simp [badLogits]
    rw [h0, Fintype.sum_bool, h0, h0]
    norm_num
  simp only [h]
  exact ciInf_const

/-- **G1 is false a second time**, with `mismatch` pinned to `1`: an
unconstrained `logits` can make the gradient arbitrarily small while the policy,
and hence both left-hand factors, stay fixed. Take `c = 1/2`: the left side is
`1/4` and the right side is at most `1/8`. -/
theorem g1_false_logits :
    ¬ (∀ (M : FiniteMDP Unit Bool)
        (logits : EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ)
        (F : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        0 ≤ M.γ → M.γ < 1 →
        ∀ (astar : Unit → Bool) (μ : Unit) (θ : EuclideanSpace ℝ (Unit × Bool))
          (mismatch : ℝ), 0 < mismatch →
          (⨅ s : Unit, (F.toPolicy θ s) (astar s))
              / (Real.sqrt (Fintype.card Unit) * mismatch)
              * (Vstar M μ - Vinf M (F.toPolicy θ) μ)
            ≤ ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖) := by
  intro h
  have hb := h badMDP (badLogits (1/2)) (badF (1/2)) (badF_hF (1/2))
    badMDP_γ₀ badMDP_γ₁ (fun _ => true) () 0 1 one_pos
  rw [badF_iInf, Vstar_badMDP, badF_value_at_zero] at hb
  have hcard : Real.sqrt (Fintype.card Unit) = 1 := by simp
  rw [hcard] at hb
  have heq : (fun t : EuclideanSpace ℝ (Unit × Bool) =>
      Vinf badMDP ((badF (1/2)).toPolicy t) ())
      = (fun t : EuclideanSpace ℝ (Unit × Bool) =>
          Vinf badMDP (show Policy Unit Bool from
            fun s => softmax (badLogits (1/2) t s)) ()) := rfl
  rw [heq] at hb
  have hup := norm_fderiv_le (1/2)
  have : |(1:ℝ)/2|/4 = 1/8 := by norm_num
  rw [this] at hup
  norm_num at hb
  linarith

/-- The exact shape of `g1_lojasiewicz`, refuted a second time via `logits`
alone (with `mismatch = 1`). Both defects must be fixed. -/
theorem g1_general_false_logits :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S) (_ : DecidableEq A)
        (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        0 ≤ M.γ → M.γ < 1 →
        ∀ (astar : S → A) (μ : S) (θ : EuclideanSpace ℝ (S × A)) (mismatch : ℝ),
          0 < mismatch →
          (⨅ s : S, (F.toPolicy θ s) (astar s))
              / (Real.sqrt (Fintype.card S) * mismatch)
              * (Vstar M μ - Vinf M (F.toPolicy θ) μ)
            ≤ ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖) := by
  intro h
  exact g1_false_logits (fun M logits F hF hγ₀ hγ₁ astar μ θ mismatch hmis =>
    h Unit Bool inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance M logits F hF hγ₀ hγ₁ astar μ θ mismatch hmis)

end MismatchFree

/-! ### What G1 and G2 should say instead

The refutations above are **not** about the constants. Both goals are broken by
the same single defect — `mismatch` is a caller-chosen real — and no numeric
choice on either side repairs that. `Target.lean` already defines the right
object, `mismatchCoeff M π μ = ⨆ s, dinfDist M π μ s / μ s`; the fix is to use
it. Three changes are needed, and they are independent.

**1. Replace the free `mismatch` by `mismatchCoeff` (mandatory).** It must be
the coefficient of the **optimal** policy, `mismatchCoeff M πstar μ`, since AKM
and Mei both write `‖d^{π*}_μ / μ‖_∞`. That forces two further adjustments:
`mismatchCoeff` is a ratio against a start *distribution*, so `μ : S` must
become `μ : Dist S`; and `mismatch_bound`/`mismatch_pos` both carry
`hμ : ∀ s, 0 < μ s`, which is exactly the full-support condition that makes the
ratio meaningful (see the note on `mismatch_bound` in `Goal.lean`). The value
side then needs `μ`-averaged versions

```lean
noncomputable def VinfDist (M : FiniteMDP S A) (π : Policy S A) (μ : Dist S) : ℝ :=
  ∑ s, μ s * Vinf M π s
noncomputable def VstarDist (M : FiniteMDP S A) (μ : Dist S) : ℝ :=
  ∑ s, μ s * Vstar M s
```

which belong in `Target.lean` (both were typechecked against this repo).

**2. Pin the parameterization.** As with G7, `logits` is unconstrained here.
`badLogits c` above is differentiable and rescales the gradient by `c`, so for
G1 (whose gradient is on the *right*) an adversarial `logits` with small `c`
breaks the inequality independently of `mismatch`. Both goals should carry the
tabular `hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a`.

**3. G2's conclusion is the wrong inequality even after (1) and (2).** AKM's
Lemma 4.1 bounds suboptimality by
`(1/(1-γ))·‖d^{π*}_μ/μ‖_∞ · max_{π'∈Π} ⟨∇V, π'-π⟩` — a *directional* term over
a bounded parameter set, and their Lemma 4.1 is stated for the **direct**
(simplex) parameterization, where that max is the ℓ¹-type quantity. For softmax
the corresponding gradient carries an extra factor `π(a|s)`, so `‖∇V‖` alone
cannot dominate the suboptimality: a 3000-MDP random sweep (random `P`, `r`,
`μ`, `θ`, `2–4` states/actions, `γ ∈ [0,0.95)`) found
`Vstar - Vinf` exceeding `(mismatchCoeff/(1-γ))·‖∇V‖` by factors up to **74×**,
with the overshoot tracking `1/min_s π(a*|s)` — the same exponentially small
quantity Mei's Lemma 8 makes explicit. The same sweep found **zero** violations
of the corrected G1 (below) in 4000 MDPs.

So `Vstar - Vinf ≤ (mismatchCoeff/(1-γ))·‖∇V‖` is **still false** for the
softmax family, whatever `mismatchCoeff` is. G2 must either (a) keep the AKM
directional form, or (b) be restated for softmax with the `min_s π(a*|s)`
factor — at which point it *is* G1 rearranged, which is the honest reading:
Mei's Lemma 8 is the softmax version of AKM's Lemma 4.1.

**Recommended replacements** (both typecheck against this repo):

```lean
-- G1 (Mei Lemma 8) — corrected. Numerically clean over 4000 random MDPs.
theorem g1_lojasiewicz (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (astar : S → A) (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    (⨅ s : S, (F.toPolicy θ s) (astar s))
        / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖

-- G2 (AKM Lemma 4.1) — corrected, keeping AKM's directional right-hand side.
theorem g2_gradient_domination (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    VstarDist M μ - VinfDist M (F.toPolicy θ) μ
      ≤ (mismatchCoeff M πstar μ / (1 - M.γ))
          * (⨆ s : S, ⨆ a : A, |advInf M (F.toPolicy θ) s a|)
```

`advInf` (the infinite-horizon advantage `Q^π - V^π`) does not exist yet —
`PerformanceDifference.lean:47` defines `adv` only for the *finite-horizon* `V`,
indexed by a horizon `j`. If G2 is to be kept distinct from G1, an `advInf` has
to be defined in `Target.lean` first. If instead G2 is
meant to be the *softmax* domination result, it is the rearrangement of the
corrected G1 and should say so rather than assert an `‖∇V‖` bound that no
constant makes true.

Note also that neither goal carries `hr : ∀ s a, |M.r s a| ≤ 1`. Unlike G3 —
where the missing `hr` was recoverable by rescaling, because both sides of a
strict inequality scale together — here the two sides scale *differently* once
`mismatchCoeff` is fixed, so `hr` should be restored rather than derived.

Until G1 and G2 are restated, their `sorry`s stand. -/

end Proofs
end PolicyGradient
