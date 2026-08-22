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

end Proofs
end PolicyGradient
