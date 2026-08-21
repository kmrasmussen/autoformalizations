/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.NPG
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# NPG convergence machinery

Agarwal–Kakade–Lee–Mahajan, Theorem 5.3: softmax NPG converges at `O(1/T)`,
with constants independent of `|S|`, `|A|`, and the distribution mismatch
coefficient.

## The potential

The proof is a potential argument on the KL divergence to an optimal policy.
The step that makes it work is that the NPG update changes the log-probability
of an action by exactly `η·A(s,a)` plus a state-dependent constant:

  `log π_{t+1}(a|s) - log π_t(a|s) = η·A^{π_t}(s,a) - log Z_t(s)`

so the *change* in KL to any comparison policy is controlled by the advantage,
which `performance_difference` then converts into progress on the value.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty A]
variable (M : FiniteMDP S A)

/-- The NPG normalizer at a state: `Z_t(s) = ∑_a π_t(a|s)·exp(η·A(s,a))`. -/
noncomputable def npgNormalizer (π : Policy S A) (j : ℕ) (η : ℝ)
    (w : S → A → ℝ) (s : S) : ℝ :=
  ∑ a, (softmax (w s)) a * Real.exp (η * adv M π j s a)

theorem npgNormalizer_pos (π : Policy S A) (j : ℕ) (η : ℝ) (w : S → A → ℝ) (s : S) :
    0 < npgNormalizer M π j η w s :=
  Finset.sum_pos (fun a _ => mul_pos (softmax_pos _ _) (Real.exp_pos _))
    ⟨Classical.arbitrary A, mem_univ _⟩

/-- **The NPG log-ratio identity.**

`log π_{t+1}(a|s) - log π_t(a|s) = η·A(s,a) - log Z_t(s)`

This is the identity the whole potential argument runs on: the change in
log-probability is the advantage, shifted by a constant that does not depend on
the action. -/
theorem npg_log_ratio (π : Policy S A) (j : ℕ) (η : ℝ) (w : S → A → ℝ)
    (s : S) (a : A) :
    Real.log ((softmax (npgStep M π j η w s)) a) - Real.log ((softmax (w s)) a)
      = η * adv M π j s a - Real.log (npgNormalizer M π j η w s) := by
  have hnew : 0 < (softmax (npgStep M π j η w s)) a := softmax_pos _ _
  have hold : 0 < (softmax (w s)) a := softmax_pos _ _
  have hZ : 0 < npgNormalizer M π j η w s := npgNormalizer_pos M π j η w s
  -- π_{t+1}(a) * Z = π_t(a) * exp(η A)
  -- π_{t+1}(a) * Z = π_t(a) * exp(η A)  -- this is npg_ratio with Z named
  have hkey : (softmax (npgStep M π j η w s)) a * npgNormalizer M π j η w s
      = (softmax (w s)) a * Real.exp (η * adv M π j s a) := by
    obtain ⟨Z, hZpos, hZ'⟩ := npg_ratio M π j η w s
    -- both Z and npgNormalizer satisfy the same defining relation; identify them
    have hsum : ∑ a, (softmax (npgStep M π j η w s)) a * Z
        = ∑ a, (softmax (w s)) a * Real.exp (η * adv M π j s a) :=
      Finset.sum_congr rfl fun a _ => hZ' a
    rw [← Finset.sum_mul, (softmax (npgStep M π j η w s)).sum_eq_one, one_mul] at hsum
    have hZeq : Z = npgNormalizer M π j η w s := hsum
    rw [hZeq] at hZ'
    exact hZ' a
  have := congrArg Real.log hkey
  rw [Real.log_mul (ne_of_gt hnew) (ne_of_gt hZ),
      Real.log_mul (ne_of_gt hold) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp] at this
  linarith

/-!
### The KL potential
-/

/-- KL divergence from `p` to `q` at a state, `∑ₐ p(a)·log(p(a)/q(a))`. -/
noncomputable def klDiv (p q : Dist A) : ℝ :=
  ∑ a, p a * (Real.log (p a) - Real.log (q a))

/-- **The per-step KL decrease.**

`KL(π*‖π_t) - KL(π*‖π_{t+1}) = η·∑ₐ π*(a|s)·A^{π_t}(s,a) - log Z_t(s)`

The KL to any comparison policy decreases by exactly the `π*`-weighted
advantage, less the normalizer. Combined with `performance_difference` — which
says the `π*`-weighted advantage *is* the suboptimality — this is what turns
the potential argument into a rate.

This is the step where the occupancy measure would appear for ordinary policy
gradient but does not for NPG, which is the source of the dimension-free
constant. -/
theorem kl_step (π : Policy S A) (j : ℕ) (η : ℝ) (w : S → A → ℝ)
    (πstar : Policy S A) (s : S) :
    klDiv (πstar s) (softmax (w s)) - klDiv (πstar s) (softmax (npgStep M π j η w s))
      = η * (∑ a, (πstar s) a * adv M π j s a)
        - Real.log (npgNormalizer M π j η w s) := by
  unfold klDiv
  rw [← Finset.sum_sub_distrib]
  have expand : ∀ a,
      (πstar s) a * (Real.log ((πstar s) a) - Real.log ((softmax (w s)) a))
      - (πstar s) a * (Real.log ((πstar s) a)
          - Real.log ((softmax (npgStep M π j η w s)) a))
      = (πstar s) a * (η * adv M π j s a
          - Real.log (npgNormalizer M π j η w s)) := by
    intro a
    have h := npg_log_ratio M π j η w s a
    -- LHS = πstar a * (log π_{t+1} a - log π_t a) = πstar a * (η A - log Z)
    have hfactor : (πstar s) a * (Real.log ((πstar s) a)
          - Real.log ((softmax (w s)) a))
        - (πstar s) a * (Real.log ((πstar s) a)
            - Real.log ((softmax (npgStep M π j η w s)) a))
        = (πstar s) a * (Real.log ((softmax (npgStep M π j η w s)) a)
            - Real.log ((softmax (w s)) a)) := by ring
    rw [hfactor, h]
  rw [Finset.sum_congr rfl (fun a _ => expand a)]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (πstar s).sum_eq_one, one_mul]
  have : ∑ a, (πstar s) a * (η * adv M π j s a)
      = η * ∑ a, (πstar s) a * adv M π j s a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [this]

end PolicyGradient
