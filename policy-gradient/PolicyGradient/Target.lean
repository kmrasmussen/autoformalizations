/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Infinite
import PolicyGradient.Softmax
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Target.lean — the objects the goals talk about

Definitions only: no goals, no `sorry`.

Split out of `Goal.lean` because the import direction demanded it. `Proofs.lean`
must import these definitions, and `Goal.lean` must be able to reference the
lemmas in `Proofs.lean` to discharge its goals — so definitions and goals cannot
live in the same file without a cycle.

The split is right on its own terms too: `Goal.lean` should hold *what we are
trying to prove*, not the vocabulary it is phrased in. Definitions here are
ordinary content and may be edited by anyone; the frozen statements in
`Goal.lean` remain the orchestrator's.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ### The optimal value

Both papers state their rates against `V*`, the supremum over policies. -/

/-- The optimal infinite-horizon value: the supremum over all policies. -/
noncomputable def Vstar (M : FiniteMDP S A) (s₀ : S) : ℝ :=
  ⨆ π : Policy S A, Vinf M π s₀

/-- A policy family differentiable in a **vector** parameter.

The Fréchet derivative `dπ θ s a : E →L[ℝ] ℝ` replaces the scalar `dπ` of
`DiffPolicy`. -/
structure VecPolicy (S A : Type*) [Fintype A] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The policy at parameter `θ`. -/
  toPolicy : E → Policy S A
  /-- The Fréchet derivative of `θ ↦ π(a|s)`. -/
  dπ : E → S → A → (E →L[ℝ] ℝ)
  /-- `dπ` really is the derivative. -/
  hasFDeriv : ∀ θ s a, HasFDerivAt (fun t => (toPolicy t s) a) (dπ θ s a) θ

/-- The Shannon entropy of a distribution. -/
noncomputable def entropy (d : Dist A) : ℝ := -∑ a, d a * Real.log (d a)

/-- The entropy-regularized value `Ṽ = V + τ·H`. -/
noncomputable def VinfSoft (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ) (s₀ : S) : ℝ :=
  Vinf M π s₀ + τ * entropy (π s₀)

/-- The optimal entropy-regularized value: the supremum over policies.

Defined rather than existentially quantified. Stating Theorem 6 as
`∃ Vsoftstar, Vsoftstar - Ṽ ≤ C(1-K)^t` would be **dischargeable in one line**
by `⟨b + c, by linarith⟩` — pick a small enough number and the inequality is
free. The target must name the real optimum. -/
noncomputable def VsoftStar (M : FiniteMDP S A) (τ : ℝ) (s₀ : S) : ℝ :=
  ⨆ π : Policy S A, VinfSoft M π τ s₀


/-- The optimal action-value `Q*(s,a)`: reward now, then optimal value after. -/
noncomputable def Qstar (M : FiniteMDP S A) (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * ∑ s', (M.P s a) s' * Vstar M s'

/-! ### Occupancy from a start *distribution*

`dinf` takes a start state. AKM's distribution-mismatch coefficient is a ratio
against a starting *distribution*, so it is not expressible without this. -/

/-- Discounted occupancy from a start distribution `μ`. -/
noncomputable def dinfDist (M : FiniteMDP S A) (π : Policy S A) (μ : Dist S) (s : S) : ℝ :=
  ∑ s₀, μ s₀ * dinf M π s₀ s

/-- **The distribution-mismatch coefficient**, `‖d^π_μ / μ‖_∞` (AKM).

*Defined*, not chosen. The previous goal took `mismatch` as a free positive real
and bounded `dinf ≤ mismatch * (1/(1-γ))` — but `1/(1-γ)` already bounds `dinf`
on its own, so **any** positive multiplier worked and `mismatch = 1` discharged
it for every MDP and policy. The bound must be against `μ s`, which is what
forces the coefficient to see where `μ` puts little mass. -/
noncomputable def mismatchCoeff (M : FiniteMDP S A) (π : Policy S A) (μ : Dist S) : ℝ :=
  ⨆ s : S, dinfDist M π μ s / μ s

/-! ### Values against a start distribution

`mismatchCoeff` is a ratio against a start *distribution*, so the goals that use
it must measure value against one too. -/

/-- Expected value under a start distribution. -/
noncomputable def VinfDist (M : FiniteMDP S A) (π : Policy S A) (μ : Dist S) : ℝ :=
  ∑ s, μ s * Vinf M π s

/-- Expected optimal value under a start distribution. -/
noncomputable def VstarDist (M : FiniteMDP S A) (μ : Dist S) : ℝ :=
  ∑ s, μ s * Vstar M s

/-- The infinite-horizon advantage `A^π(s,a) = Q^π(s,a) - V^π(s)`.

`PerformanceDifference.adv` is finite-horizon and indexed by a horizon; AKM's
Lemma 4.1 needs this one. -/
noncomputable def advInf (M : FiniteMDP S A) (π : Policy S A) (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * (∑ s', (M.P s a) s' * Vinf M π s') - Vinf M π s

end PolicyGradient
