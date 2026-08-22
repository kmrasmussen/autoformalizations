/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv

/-! # Conv2 — scratch -/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv2

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

-- probe: is tendsto_pi_adv_zero usable with exactly the goal's hypotheses?
example (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a : A) :
    Tendsto (fun t => (F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)
      atTop (nhds 0) :=
  tendsto_pi_adv_zero M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep s a

end Conv2

end Proofs
end PolicyGradient
