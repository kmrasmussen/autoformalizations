/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.GradientDomination

/-!
# Natural policy gradient

Kakade, *A Natural Policy Gradient*, NeurIPS 2001; Agarwal–Kakade–Lee–Mahajan
JMLR 2021, Theorem 5.3.

## The key structural fact

For softmax parameterization the natural policy gradient update has a closed
form: the Fisher inverse and the state-occupancy weighting **cancel**, leaving

  `θ_{t+1}(s,a) = θ_t(s,a) + (η / (1-γ)) · A^{π_t}(s,a)`

i.e. NPG on softmax is exactly *advantage-weighted logit ascent*, with no
dependence on the visitation distribution at all. That cancellation is why the
AKM rate is dimension-free — independent of `|S|`, `|A|`, and the distribution
mismatch coefficient — and it is the fact worth formalizing.

We take the closed form as the *definition* of the softmax NPG update (which is
what AKM Lemma 5.2 establishes) and develop its consequences.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty A]
variable (M : FiniteMDP S A)

/-- One step of softmax NPG on the logits: add the scaled advantage. -/
noncomputable def npgStep (π : Policy S A) (j : ℕ) (η : ℝ)
    (w : S → A → ℝ) : S → A → ℝ :=
  fun s a => w s a + η * adv M π j s a

/-- The NPG update changes each logit by exactly the scaled advantage — no
occupancy weighting appears. -/
@[simp] theorem npgStep_apply (π : Policy S A) (j : ℕ) (η : ℝ) (w : S → A → ℝ)
    (s : S) (a : A) :
    npgStep M π j η w s a = w s a + η * adv M π j s a := rfl

/-- The NPG update is invariant to adding a constant to all logits at a state:
softmax quotients out constants, so the induced policy is unchanged. -/
theorem softmax_add_const (w : A → ℝ) (c : ℝ) :
    softmax (fun a => w a + c) = softmax w := by
  ext a
  simp only [softmax_apply, Real.exp_add]
  rw [← Finset.sum_mul]
  rw [mul_comm (Real.exp (w a)) (Real.exp c)]
  rw [mul_comm (∑ a', Real.exp (w a')) (Real.exp c)]
  rw [mul_div_mul_left _ _ (ne_of_gt (Real.exp_pos c))]

end PolicyGradient
