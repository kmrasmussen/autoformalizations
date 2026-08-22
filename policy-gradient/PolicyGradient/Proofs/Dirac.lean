/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1

/-!
# Dirac — gradient domination from a single start state

Work file for the frozen goal `Goal.dirac_gradient_domination`.

`g1_lojasiewicz` and `g2_gradient_domination` both carry `hμ : ∀ s, 0 < μ s`,
because they route through `mismatchCoeff` and `mismatch_bound` is refuted
without full support (`Proofs.mismatch_bound_is_false`). A Dirac start state is
the maximally degenerate violation, so `softmax_ascent_converges` and
`mei_theorem4` — which start from a single state — cannot use that route.

The fix is to never form `dinf s / μ s` at all. Bound directly against the
comparator occupancy `dinf M πstar μ`, which is supported exactly on the states
`πstar` reaches from `μ`. Then no positivity hypothesis on the start state is
needed, and in fact the result is an **equality**, not an inequality: it *is*
the AKM 4.1 performance difference lemma, `Proofs.perfDiffInf`, read with
`π := F.toPolicy θ`, `π' := πstar`, `s₀ := μ`.

The repo's `dinf` is the **unnormalized** occupancy (it sums to `1/(1-γ)`, see
the docstring of `Infinite.dinf`), so AKM's explicit `1/(1-γ)` prefactor is
already absorbed into the measure and the statement carries no extra factor.
-/

open Finset

namespace PolicyGradient
namespace Proofs

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **Dirac-compatible gradient domination, equality form.**

`V*(μ) - V^π(μ) = ∑_s d^{πstar}(μ, s) · ∑_a πstar(a|s) · A^π(s, a)`.

This is `perfDiffInf` with the comparator `πstar` assumed optimal at `μ`; note
that only `hstar μ` is used, so the hypothesis could be weakened to that single
state. No hypothesis on the support of the start state appears, because the
proof never divides by a start-state mass. -/
theorem dirac_gradient_domination_eq (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (μ : S) (θ : EuclideanSpace ℝ (S × A)) :
    Vstar M μ - Vinf M (F.toPolicy θ) μ
      = (∑ s, dinf M πstar μ s * ∑ a, (πstar s) a * advInf M (F.toPolicy θ) s a) := by
  have h := perfDiffInf M (F.toPolicy θ) πstar hr hγ₀ hγ₁ μ
  rw [hstar μ] at h
  simpa [pdInf, advGapInf] using h

/-- **Dirac-compatible gradient domination** (frozen `Goal.dirac_gradient_domination`).

The frozen statement is an inequality; `dirac_gradient_domination_eq` shows it
in fact holds with equality. -/
theorem dirac_gradient_domination_proof (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (μ : S) (θ : EuclideanSpace ℝ (S × A)) :
    Vstar M μ - Vinf M (F.toPolicy θ) μ
      ≤ (∑ s, dinf M πstar μ s * ∑ a, (πstar s) a * advInf M (F.toPolicy θ) s a) :=
  le_of_eq (dirac_gradient_domination_eq M F hr hγ₀ hγ₁ πstar hstar μ θ)

end Proofs
end PolicyGradient
