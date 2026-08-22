/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target

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


end Proofs
end PolicyGradient
