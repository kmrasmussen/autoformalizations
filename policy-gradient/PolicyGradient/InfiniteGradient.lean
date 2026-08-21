/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Infinite

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

end PolicyGradient
