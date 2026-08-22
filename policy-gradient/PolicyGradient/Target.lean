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

/-- **Start-state-only** entropy regularization: `V + τ·H(π(·|s₀))`.

**This is not Mei's objective**, and `mei_theorem6` stated over it was false for
that reason among others. Mei's `Ṽ` discounts entropy along the *whole
trajectory* (the soft Bellman fixed point). With entropy added only at the start
state the bonus does not propagate, `VsoftStar` has no log-sum-exp closed form,
and their Lemmas 14/15/16 are not true as stated. Kept only because the
refutations reference it. -/
noncomputable def VinfSoft (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ) (s₀ : S) : ℝ :=
  Vinf M π s₀ + τ * entropy (π s₀)

/-- The optimal start-state-only regularized value. See `VinfSoft`'s warning.

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

⚠ **NORMALIZATION DEFECT, found 2026-08-22 and not yet repaired.**

Both papers define the occupancy measure **with a leading `(1−γ)`**:

* AKM eq. (4): `d^π_{s₀}(s) := (1 − γ) ∑_{t=0}^∞ γ^t Pr^π(s_t = s | s₀)`
* Mei eqs. (335)–(338): `d^{π_θ}_μ(s) = E[(1−γ) ∑ …] ≥ (1−γ)·μ(s)`
* Kakade–Langford eq. (2.1): "where the `1 − γ` is necessary for normalization"

This repo's `dinf` omits it (`Infinite.lean`: `∑' t, γ^t · visit`), so

```
mismatchCoeff (repo) = (1/(1−γ)) · ‖d^{π*}_μ / μ‖_∞ (papers)
```

Airtight cross-check: the repo proves `dinf ≤ 1/(1−γ)` (`Proofs.dinf_le_one_div`),
where a normalized occupancy is bounded by `1`.

**Direction: SAFE, not an over-claim.** Every statement using `mismatchCoeff` on
a right-hand side is thereby *weaker* than the paper's. But in `mei_theorem4` the
coefficient enters **squared**, silently converting the paper's sharp `(1−γ)⁶`
rate into `(1−γ)⁸` — exactly in the regime the constant is meant to track. So
the rate results are true but not the papers' rates.

Affects `mismatchCoeff`, `g1_lojasiewicz`, `g2_advantage_bound`, `mei_theorem4`.
Repairing it means inserting `(1−γ)` into `dinf` and re-deriving everything
downstream — a large, mechanical change, deliberately not attempted while proofs
are in flight against the current definition.

Note `performance_difference` is the instructive contrast: it is missing the same
`(1−γ)`, and there it is **correct**, because the papers' factor cancels against
their normalized `d`. Same omission, opposite verdict — which is why this needed
checking term by term rather than pattern-matching.

VERBATIM, AKM (arXiv:1908.00261) Definition 3.1:

> **Definition 3.1 (Distribution mismatch coefficient).** Given a policy `π` and
> measures `ρ, μ ∈ Δ(S)`, we refer to `‖d^π_ρ / μ‖_∞` as the distribution
> mismatch coefficient of `π` relative to `μ`. Here, `d^π_ρ / μ` denotes
> componentwise division.
>
> We often instantiate this coefficient with `μ` as the initial state
> distribution used in a policy optimization algorithm, `ρ` as the distribution
> to measure the sub-optimality of our policy [...] and where `π` above is often
> chosen to be `π⋆ ∈ argmax_{π∈Π} V^π(ρ)`.

Note the paper takes TWO measures, `ρ` and `μ`; this definition collapses them
to one. That is a simplification, not the paper's definition.

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
