/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite-horizon MDPs and parameterized policies

Substrate for the policy gradient theorem in the finite-horizon, finite-state,
finite-action setting.

## Design notes

**Distributions as `stdSimplex`, not `PMF`.** Mathlib's `PMF` is valued in `ℝ≥0∞`,
which is not a vector space and carries no differentiation API. The policy gradient
theorem differentiates *through* the policy, so we model distributions as real
probability vectors (`stdSimplex ℝ ι`, unfolded to an explicit subtype).

**Value by backward recursion, not by trajectory expectation.** For a finite horizon
`V` is defined by recursion on the number of remaining steps. This avoids product
measures on trajectory space entirely, and makes the policy gradient theorem an
induction on the horizon rather than an infinite unrolling. (The `∑ₜ γᵗ ...`
trajectory formulation is the right one for the infinite-horizon file, where the
unrolling must be justified by dominated convergence.)
-/

open Finset

namespace PolicyGradient

variable {S A : Type*}

/-- A probability vector over a finite type: a point of the standard simplex. -/
structure Dist (ι : Type*) [Fintype ι] where
  prob : ι → ℝ
  nonneg : ∀ i, 0 ≤ prob i
  sum_eq_one : ∑ i, prob i = 1

namespace Dist
variable {ι : Type*} [Fintype ι]

instance : CoeFun (Dist ι) (fun _ => ι → ℝ) := ⟨prob⟩

@[ext] theorem ext {p q : Dist ι} (h : ∀ i, p i = q i) : p = q := by
  cases p; cases q; simp only [Dist.mk.injEq]; exact funext h

/-- The expectation of `f` under `p`. -/
noncomputable def expect (p : Dist ι) (f : ι → ℝ) : ℝ := ∑ i, p i * f i

end Dist

/-- A finite MDP with a fixed horizon. The policy is *not* part of this structure:
the policy gradient theorem varies the policy while holding the MDP fixed. -/
structure FiniteMDP (S A : Type*) [Fintype S] [Fintype A] where
  /-- Transition kernel: `P s a` is the next-state distribution. -/
  P : S → A → Dist S
  /-- Reward for taking action `a` in state `s`. -/
  r : S → A → ℝ
  /-- Discount factor. -/
  γ : ℝ

/-- A policy assigns to each state a distribution over actions. -/
def Policy (S A : Type*) [Fintype A] := S → Dist A

end PolicyGradient
