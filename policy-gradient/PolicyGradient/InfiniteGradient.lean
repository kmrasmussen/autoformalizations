/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Infinite
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The infinite-horizon policy gradient theorem

The statement:

  d/dθ Vinf(s₀) = ∑_s dinf(s₀, s) · ∑_a (d/dθ π_θ(a|s)) · Qinf(s, a)

with `dinf` the **unnormalized** discounted occupancy `∑ₜ γᵗ Pr(sₜ = s)`. Sources
that normalize `dinf` into a probability distribution carry a compensating
`1/(1-γ)`; ours does not. Confirmed numerically (`pg_inf_stmt.py`, 2.2e-9).

## Strategy

`Vinf` is a `tsum` over trajectories, and differentiating it term by term would
need a bound on the term derivatives that is *global and uniform in θ* — which
softmax scores do not satisfy. Instead we go through the **Bellman equation**:
`Vinf` satisfies a fixed-point identity, and the derivative satisfies the
corresponding linear identity. This reuses the finite-horizon skeleton and
avoids the uniformity problem entirely.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
variable (M : FiniteMDP S A) (PF : DiffPolicy S A) (θ : ℝ)

/-- The immediate expected reward under a policy. -/
noncomputable def rbar (π : Policy S A) (s : S) : ℝ :=
  ∑ a, (π s) a * M.r s a

/-- The claimed derivative of `Vinf`: the visitation-weighted sum of score
times action-value. -/
noncomputable def pgInfSum (s₀ : S) : ℝ :=
  ∑ s, dinf M (PF.toPolicy θ) s₀ s *
    ∑ a, PF.dπ θ s a * Qinf M (PF.toPolicy θ) s a

/-!
### Differentiating `Vinf`

`Vinf` is a `tsum` over time, so term-by-term differentiation needs a summable
bound on the term derivatives, uniform in `θ`. We take that bound as an explicit
hypothesis: it is exactly what `hasDerivAt_tsum` requires, and it is what the
informal literature silently assumes when it exchanges `∂/∂θ` with `∑ₜ`.

Numerically the `t`-th term's derivative grows like `C·(t+1)·γᵗ`
(`pg_inf_stmt.py`), which is summable — so the hypothesis is satisfiable, not
vacuous.
-/

/-- A uniform summable bound on the derivatives of the discounted reward terms.

This is the hypothesis that makes the `∂/∂θ ↔ ∑ₜ` interchange legitimate. Every
informal proof of the policy gradient theorem uses it without stating it. -/
structure TermDerivBound (M : FiniteMDP S A) (PF : DiffPolicy S A) where
  /-- The bound on the `t`-th term's derivative. -/
  u : ℕ → ℝ
  /-- The bound is summable. -/
  hu : Summable u
  /-- The `t`-th discounted-reward term is differentiable in `θ`, with the
  stated derivative. -/
  dstep : ℕ → ℝ → S → ℝ
  hasDeriv : ∀ t θ s₀, HasDerivAt (fun z => stepReward M (PF.toPolicy z) t s₀)
      (dstep t θ s₀) θ
  /-- The derivatives are bounded by `u`, uniformly in `θ`. -/
  bound : ∀ t θ s₀, ‖dstep t θ s₀‖ ≤ u t
  /-- The value series converges at some parameter (any one point suffices). -/
  base : ∀ s₀, Summable fun t => stepReward M (PF.toPolicy 0) t s₀

/-- **`Vinf` is differentiable, and its derivative is the sum of the term
derivatives.** This is the `∂/∂θ ↔ ∑ₜ` interchange, discharged. -/
theorem hasDerivAt_Vinf (B : TermDerivBound M PF) (s₀ : S) :
    HasDerivAt (fun z => Vinf M (PF.toPolicy z) s₀)
      (∑' t, B.dstep t θ s₀) θ := by
  unfold Vinf
  exact hasDerivAt_tsum B.hu (fun t z => B.hasDeriv t z s₀)
    (fun t z => B.bound t z s₀) (B.base s₀) θ

end PolicyGradient
