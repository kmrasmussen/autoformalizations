/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.GradientDomination
import PolicyGradient.Softmax

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

/-- **The softmax NPG update in closed form.**

After one NPG step the new policy reweights the old one by `exp(η·A)`:

  `π_{t+1}(a|s) ∝ π_t(a|s) · exp(η · A^{π_t}(s,a))`

This is the form AKM Lemma 5.2 establishes and the form the convergence proof
uses. Note there is no occupancy measure anywhere in it — the `d^π(s)` that
appears in the ordinary policy gradient has been cancelled by the Fisher
inverse. -/
theorem npg_softmax_update (π : Policy S A) (j : ℕ) (η : ℝ)
    (w : S → A → ℝ) (s : S) (a : A) :
    (softmax (npgStep M π j η w s)) a
      = Real.exp (w s a) * Real.exp (η * adv M π j s a)
        / ∑ a', Real.exp (w s a') * Real.exp (η * adv M π j s a') := by
  simp only [softmax_apply, npgStep_apply, Real.exp_add]

/-- The NPG update multiplies the action probabilities by `exp(η·A)` up to
renormalization: the ratio of new to old probability is proportional to
`exp(η·A)`, with a constant depending only on the state. -/
theorem npg_ratio (π : Policy S A) (j : ℕ) (η : ℝ) (w : S → A → ℝ) (s : S) :
    ∃ Z : ℝ, 0 < Z ∧ ∀ a,
      (softmax (npgStep M π j η w s)) a * Z
        = (softmax (w s)) a * Real.exp (η * adv M π j s a) := by
  refine ⟨(∑ a', Real.exp (w s a') * Real.exp (η * adv M π j s a'))
            / (∑ a', Real.exp (w s a')), ?_, ?_⟩
  · refine div_pos ?_ ?_
    · exact Finset.sum_pos (fun a' _ => mul_pos (Real.exp_pos _) (Real.exp_pos _))
        ⟨Classical.arbitrary A, mem_univ _⟩
    · exact softmax_denom_pos (w s)
  · intro a
    rw [npg_softmax_update, softmax_apply]
    have h1 : (0:ℝ) < ∑ a', Real.exp (w s a') * Real.exp (η * adv M π j s a') :=
      Finset.sum_pos (fun a' _ => mul_pos (Real.exp_pos _) (Real.exp_pos _))
        ⟨Classical.arbitrary A, mem_univ _⟩
    have h2 : (0:ℝ) < ∑ a', Real.exp (w s a') := softmax_denom_pos (w s)
    field_simp

/-!
### Monotone improvement

The NPG update never decreases the expected advantage at a state: reweighting
by `exp(η·A)` with `η ≥ 0` shifts mass towards higher-advantage actions. This
is the step that drives the convergence argument, and it is an instance of the
general fact that an exponential-tilt reweighting increases the mean of the
tilting statistic (a Chebyshev / FKG-type correlation inequality).
-/

/-- The sign fact behind exponential-tilt monotonicity: `(f a - f b)` and
`(e^{ηf a} - e^{ηf b})` always have the same sign when `η ≥ 0`.

This is the ingredient of the Chebyshev sum inequality that makes the NPG
update monotone — reweighting by `exp(η·A)` moves probability mass towards
higher-advantage actions. -/
theorem tilt_sign (f : A → ℝ) (η : ℝ) (hη : 0 ≤ η) (a b : A) :
    0 ≤ (f a - f b) * (Real.exp (η * f a) - Real.exp (η * f b)) := by
  rcases le_total (f a) (f b) with h | h
  · have he : Real.exp (η * f a) ≤ Real.exp (η * f b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith
  · have he : Real.exp (η * f b) ≤ Real.exp (η * f a) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith

/-- The NPG update increases the probability of any action whose advantage
exceeds that of another, relative to that other action: the probability *ratio*
between two actions moves in favour of the higher advantage.

This is the precise sense in which softmax NPG is monotone, and it needs no
Chebyshev machinery — it follows directly from the closed form. -/
theorem npg_ratio_mono (π : Policy S A) (j : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (w : S → A → ℝ) (s : S) (a b : A)
    (hab : adv M π j s b ≤ adv M π j s a) :
    (softmax (w s)) a * (softmax (npgStep M π j η w s)) b
      ≤ (softmax (npgStep M π j η w s)) a * (softmax (w s)) b := by
  obtain ⟨Z, hZ, hratio⟩ := npg_ratio M π j η w s
  have ha := hratio a
  have hb := hratio b
  have hexp : Real.exp (η * adv M π j s b) ≤ Real.exp (η * adv M π j s a) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpa : 0 < (softmax (w s)) a := softmax_pos _ _
  have hpb : 0 < (softmax (w s)) b := softmax_pos _ _
  -- multiply through by Z > 0 and compare
  have key : ((softmax (w s)) a * (softmax (npgStep M π j η w s)) b) * Z
      ≤ ((softmax (npgStep M π j η w s)) a * (softmax (w s)) b) * Z := by
    calc ((softmax (w s)) a * (softmax (npgStep M π j η w s)) b) * Z
        = (softmax (w s)) a * ((softmax (npgStep M π j η w s)) b * Z) := by ring
      _ = (softmax (w s)) a * ((softmax (w s)) b * Real.exp (η * adv M π j s b)) := by
          rw [hb]
      _ ≤ (softmax (w s)) a * ((softmax (w s)) b * Real.exp (η * adv M π j s a)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpa)
          exact mul_le_mul_of_nonneg_left hexp (le_of_lt hpb)
      _ = ((softmax (w s)) a * Real.exp (η * adv M π j s a)) * (softmax (w s)) b := by ring
      _ = ((softmax (npgStep M π j η w s)) a * Z) * (softmax (w s)) b := by rw [ha]
      _ = ((softmax (npgStep M π j η w s)) a * (softmax (w s)) b) * Z := by ring
  exact le_of_mul_le_mul_right key hZ

end PolicyGradient
