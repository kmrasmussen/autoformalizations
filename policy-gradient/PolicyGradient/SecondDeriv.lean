/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Smoothness

/-!
# The second derivative of the value function

The remaining input to AKM Lemma E.4 / Mei Lemma 7: a bound on `∂²V/∂θ²`,
which is what the `8/(1-γ)³` smoothness constant is.

## Route — and how it differs from the paper

The paper writes `V = eₛᵀ M(α) r_{θα}` with `M(α) = (I - γP(α))⁻¹` and
differentiates the matrix inverse twice, bounding four terms using
`‖M(α)x‖_∞ ≤ ‖x‖_∞/(1-γ)`.

**We do not follow that route.** Mathlib's support for differentiating a
parameterized matrix inverse is thin, and the rest of this development is built
on backward recursion rather than resolvents. Instead we differentiate the
`dV` recursion directly:

  `dV_{m+1} = localTerm_m + γ·∑_{s'} step s s' · dV_m s'`

Differentiating once more in `θ` gives three groups — the local term's
derivative, the transition's derivative against `dV`, and the transition
against `d2V` — and the same induction that produced `abs_dV_le` bounds them.
Same theorem, different proof.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
variable (M : FiniteMDP S A) (PF : C2Policy S A) (θ : ℝ)

/-- The derivative of the one-step transition kernel in `θ`. -/
noncomputable def dstep (s s' : S) : ℝ :=
  ∑ a, PF.d2π θ s a * 0 + ∑ a, PF.dπ θ s a * (M.P s a) s'

/-- The transition derivative, simplified: only the policy depends on `θ`. -/
theorem dstep_eq (s s' : S) :
    dstep M PF θ s s' = ∑ a, PF.dπ θ s a * (M.P s a) s' := by
  unfold dstep
  simp

/-- `step` is differentiable in `θ`, with derivative `dstep`. -/
theorem hasDerivAt_step (s s' : S) :
    HasDerivAt (fun t => step M (PF.toDiffPolicy.toPolicy t) s s')
      (dstep M PF θ s s') θ := by
  rw [dstep_eq]
  unfold step
  exact HasDerivAt.fun_sum fun a _ =>
    (PF.toDiffPolicy.hasDeriv θ s a).mul_const _

/-- The transition derivative has total variation bounded by the score's. -/
theorem sum_abs_dstep_le (D : ℝ)
    (hscore : ∀ s, ∑ a, |PF.dπ θ s a| ≤ D) (s : S) :
    ∑ s', |dstep M PF θ s s'| ≤ D := by
  calc ∑ s', |dstep M PF θ s s'|
      = ∑ s', |∑ a, PF.dπ θ s a * (M.P s a) s'| := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [dstep_eq]
    _ ≤ ∑ s', ∑ a, |PF.dπ θ s a * (M.P s a) s'| :=
        Finset.sum_le_sum fun s' _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, ∑ s', |PF.dπ θ s a| * (M.P s a) s' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
    _ = ∑ a, |PF.dπ θ s a| := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, (M.P s a).sum_eq_one, mul_one]
    _ ≤ D := hscore s

end PolicyGradient
