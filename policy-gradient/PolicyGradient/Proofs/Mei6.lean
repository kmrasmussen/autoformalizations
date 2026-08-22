/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Mei6 — Mei et al. Theorem 6, the entropy-regularized geometric rate

Work file for the frozen goal `Goal.mei_theorem6`.

## Verdict: the frozen statement is FALSE.

`K` is a *universally quantified* parameter constrained only by `0 < K < 1`, and
`logits` is a *free* parameter. Together these break the statement outright, and
neither the step size nor any entropy analysis is involved in the refutation.

Take `logits θ s a = 0` — a legal instantiation, since `logits` is universally
quantified and nothing forces it to depend on `θ`. Then `F.toPolicy θ` is the
uniform distribution for **every** `θ`, so

  `w ↦ VinfSoft M (F.toPolicy w) τ μ`

is a *constant* function, its `gradient` is `0`, and `hstep` degenerates to
`θ (t+1) = θ t`. The trajectory never moves. Yet the suboptimality gap
`VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ 0)) τ μ` is strictly positive,
because the uniform policy is not the soft-optimal one. The claim then asserts

  `gap ≤ gap * (1 - K) ^ t`

for a `gap > 0` and *every* `K ∈ (0,1)`; at `t = 1`, `K = 1/2` this says
`gap ≤ gap / 2`, i.e. `gap ≤ 0`. Contradiction.

The concrete MDP is `m6MDP`: one state, two actions, `γ = 0`,
`r(s, true) = 1`, `r(s, false) = 0`, and `τ = 1`. Positivity of the gap needs
only the single witness policy `π(true) = 3/4`, whose soft value exceeds the
uniform policy's by `1/4 + log 2 - (3/4) log 3 > 0`.

## What the statement should say instead

`K` must be **existential** — chosen by the theorem and tied to `τ`, `γ` and the
MDP — and `logits` must be **pinned** to the tabular softmax. See the discussion
at the bottom of this file.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Mei6

/-! ### The counterexample MDP

One state, two actions, `γ = 0`. `r(s, true) = 1`, `r(s, false) = 0`. -/

/-- The counterexample MDP for Theorem 6: one state, two actions, `γ = 0`. -/
noncomputable def m6MDP : FiniteMDP Unit Bool where
  P := fun _ _ => ⟨fun _ => 1, by intro; norm_num, by simp⟩
  r := fun _ a => if a then 1 else 0
  γ := 0

theorem m6MDP_r : ∀ s a, |m6MDP.r s a| ≤ 1 := by
  intro s a; cases a <;> norm_num [m6MDP]

theorem m6MDP_γ₀ : (0:ℝ) ≤ m6MDP.γ := le_of_eq rfl
theorem m6MDP_γ₁ : m6MDP.γ < 1 := by norm_num [m6MDP]

/-- With `γ = 0` only the `t = 0` term of the return survives. -/
theorem Vinf_m6 (π : Policy Unit Bool) : Vinf m6MDP π () = (π ()) true := by
  have h : Vinf m6MDP π () = ∑ a, (π ()) a * m6MDP.r () a := by
    unfold Vinf
    rw [tsum_eq_single 0]
    · unfold stepReward; simp [m6MDP]
    · intro t ht; unfold stepReward
      have : m6MDP.γ = 0 := rfl
      rw [this, zero_pow ht, zero_mul]
  rw [h]; simp [m6MDP, Fintype.sum_bool]

/-! ### The two policies we compare -/

/-- The uniform policy on `Bool`. -/
noncomputable def unifPol : Policy Unit Bool :=
  fun _ => ⟨fun _ => 1/2, by intro; norm_num, by simp [Fintype.sum_bool]⟩

/-- The witness policy `π(true) = 3/4`, which beats uniform on the soft value. -/
noncomputable def witPol : Policy Unit Bool :=
  fun _ => ⟨fun a => if a then 3/4 else 1/4, by intro a; cases a <;> norm_num, by
    simp [Fintype.sum_bool]; norm_num⟩

/-! ### The soft values of those two policies -/

theorem entropy_unif : entropy (unifPol ()) = Real.log 2 := by
  have h : ∀ a : Bool, (unifPol ()) a = 1/2 := fun _ => rfl
  simp only [entropy, Fintype.sum_bool, h]
  rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

theorem VinfSoft_unif : VinfSoft m6MDP unifPol 1 () = 1/2 + Real.log 2 := by
  rw [VinfSoft, Vinf_m6, entropy_unif]
  have : (unifPol ()) true = 1/2 := rfl
  rw [this]; ring

theorem entropy_wit :
    entropy (witPol ()) = -((3/4) * Real.log (3/4) + (1/4) * Real.log (1/4)) := by
  have h1 : (witPol ()) true = 3/4 := rfl
  have h0 : (witPol ()) false = 1/4 := rfl
  simp only [entropy, Fintype.sum_bool, h1, h0]

theorem VinfSoft_wit :
    VinfSoft m6MDP witPol 1 () = 3/4 - ((3/4) * Real.log (3/4) + (1/4) * Real.log (1/4)) := by
  rw [VinfSoft, Vinf_m6, entropy_wit]
  have : (witPol ()) true = 3/4 := rfl
  rw [this]; ring

/-- **The witness beats uniform**: the margin is `1/4 + log 2 - (3/4) log 3 > 0`. -/
theorem wit_gt_unif : VinfSoft m6MDP unifPol 1 () < VinfSoft m6MDP witPol 1 () := by
  rw [VinfSoft_unif, VinfSoft_wit]
  -- rewrite both logs in terms of `log 2` and `log 3`
  have h34 : Real.log (3/4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (3:ℝ)/4 = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have h14 : Real.log (1/4) = -(2 * Real.log 2) := by
    rw [show (1:ℝ)/4 = ((2:ℝ) ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast; ring
  rw [h34, h14]
  -- `log 3 ≤ 2 log 2 - 1/4`, from `log x ≥ 1 - 1/x` at `x = 4/3`
  have hlog43 : (1:ℝ)/4 ≤ Real.log (4/3) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 4/3 by norm_num)
    norm_num at h ⊢
    linarith
  have h43 : Real.log (4/3) = 2 * Real.log 2 - Real.log 3 := by
    rw [show (4:ℝ)/3 = 2 ^ 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 - 1/4 := by rw [h43] at hlog43; linarith
  -- and `log 2 < 7/8`
  have hlog2 : Real.log 2 < 7/8 := lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num)
  linarith


/-! ### The degenerate softmax family

`logits ≡ 0`, so the policy is uniform at every parameter and the objective is
constant. This is a legal instantiation: `logits` is universally quantified in
the frozen statement and nothing ties it to `θ`. -/

/-- The constant-zero logits. -/
noncomputable def m6Logits : EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ :=
  fun _ _ _ => 0

/-- `softmax` of the zero logits on `Bool` is the uniform distribution. -/
theorem softmax_zero_eq_unif :
    (softmax (fun _ : Bool => (0:ℝ))) = unifPol () := by
  ext a
  rw [softmax_apply]
  simp [unifPol]

/-- The degenerate `VecPolicy`: constant in `θ`, hence trivially differentiable
with derivative `0`. -/
noncomputable def m6F : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool)) where
  toPolicy := fun θ s => softmax (m6Logits θ s)
  dπ := fun _ _ _ => 0
  hasFDeriv := fun θ s a => by
    have : (fun t : EuclideanSpace ℝ (Unit × Bool) => (softmax (m6Logits t s)) a)
        = fun _ => (softmax (fun _ : Bool => (0:ℝ))) a := rfl
    rw [this]
    exact hasFDerivAt_const _ _

theorem m6F_hF : ∀ θ s a, (m6F.toPolicy θ s) a = softmax (m6Logits θ s) a :=
  fun _ _ _ => rfl

/-- The policy is uniform at every parameter. -/
theorem m6F_toPolicy (θ : EuclideanSpace ℝ (Unit × Bool)) : m6F.toPolicy θ = unifPol := by
  funext s
  exact softmax_zero_eq_unif

/-- Hence the entropy-regularized objective is a **constant** function of `θ`. -/
theorem m6_obj_const :
    (fun w : EuclideanSpace ℝ (Unit × Bool) => VinfSoft m6MDP (m6F.toPolicy w) 1 ())
      = fun _ => VinfSoft m6MDP unifPol 1 () := by
  funext w; rw [m6F_toPolicy]

/-- A constant function has zero gradient, so every ascent step stands still. -/
theorem m6_gradient_zero (θ : EuclideanSpace ℝ (Unit × Bool)) :
    gradient (fun w => VinfSoft m6MDP (m6F.toPolicy w) 1 ()) θ = 0 := by
  rw [m6_obj_const]
  simp [gradient]

/-! ### The gap is positive and constant -/

/-- `VsoftStar` is an upper bound reached by no worse than the witness policy,
so it strictly exceeds the uniform policy's soft value. -/
theorem gap_pos : 0 < VsoftStar m6MDP 1 () - VinfSoft m6MDP unifPol 1 () := by
  have hbdd : BddAbove (Set.range (fun π : Policy Unit Bool => VinfSoft m6MDP π 1 ())) := by
    refine ⟨1 + 2, ?_⟩
    rintro x ⟨π, rfl⟩
    show Vinf m6MDP π () + 1 * entropy (π ()) ≤ 1 + 2
    rw [Vinf_m6]
    have h1 : (π ()) true ≤ 1 := by
      have := (π ()).sum_eq_one
      have hnn := (π ()).nonneg false
      rw [Fintype.sum_bool] at this
      linarith
    -- `x * log x ≥ x - 1` gives `-x * log x ≤ 1 - x`, so each of the two terms
    -- contributes at most `1`.
    have h2 : entropy (π ()) ≤ 2 := by
      have hb : ∀ a : Bool, -((π ()) a * Real.log ((π ()) a)) ≤ 1 := by
        intro a
        have := Real.self_sub_one_le_mul_log ((π ()).nonneg a)
        have hnn := (π ()).nonneg a
        linarith
      have := hb true
      have := hb false
      simp only [entropy, Fintype.sum_bool, neg_add]
      linarith
    linarith
  have hwit : VinfSoft m6MDP witPol 1 () ≤ VsoftStar m6MDP 1 () :=
    le_ciSup hbdd witPol
  have := wit_gt_unif
  linarith


/-! ### The refutation

The frozen statement, instantiated at the counterexample. -/

/-- **Mei Theorem 6 is false as frozen** (concrete instance).

At `S = Unit`, `A = Bool`, `γ = 0`, `τ = 1`, `η = 1`, constant logits, `K = 1/2`
and `t = 1`: the trajectory is constant (zero gradient), so the gap at `t = 1`
equals the gap at `t = 0`, which is strictly positive; but the claimed bound is
half of it. -/
theorem mei6_false :
    ¬ (∀ (M : FiniteMDP Unit Bool)
        (logits : EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ)
        (F : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (τ : ℝ), 0 < τ → ∀ (μ : Unit) (η : ℝ), 0 < η →
        ∀ (θ : ℕ → EuclideanSpace ℝ (Unit × Bool)),
        (∀ t, θ (t + 1)
          = θ t + η • gradient (fun w => VinfSoft M (F.toPolicy w) τ μ) (θ t)) →
        ∀ (K : ℝ), 0 < K → K < 1 → ∀ (t : ℕ),
          VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ t)) τ μ
            ≤ (VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ 0)) τ μ) * (1 - K) ^ t) := by
  intro h
  -- the constant trajectory really is a gradient-ascent trajectory here
  set Θ : ℕ → EuclideanSpace ℝ (Unit × Bool) := fun _ => 0 with hΘ
  have hstep : ∀ t : ℕ, Θ (t + 1)
      = Θ t + (1:ℝ) • gradient (fun w => VinfSoft m6MDP (m6F.toPolicy w) 1 ()) (Θ t) := by
    intro t; rw [m6_gradient_zero]; simp [hΘ]
  have hbound := h m6MDP m6Logits m6F m6F_hF m6MDP_r m6MDP_γ₀ m6MDP_γ₁
    1 one_pos () 1 one_pos Θ hstep (1/2) (by norm_num) (by norm_num) 1
  -- both sides collapse: the policy is uniform at every parameter
  simp only [m6F_toPolicy, pow_one] at hbound
  have hgap := gap_pos
  linarith

/-- The exact shape of the frozen `mei_theorem6`, as a hypothesis. If Theorem 6
held in the generality stated, this would follow; `mei6_false` shows it cannot. -/
theorem mei6_general_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S) (_ : DecidableEq A)
        (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (τ : ℝ), 0 < τ → ∀ (μ : S) (η : ℝ), 0 < η →
        ∀ (θ : ℕ → EuclideanSpace ℝ (S × A)),
        (∀ t, θ (t + 1)
          = θ t + η • gradient (fun w => VinfSoft M (F.toPolicy w) τ μ) (θ t)) →
        ∀ (K : ℝ), 0 < K → K < 1 → ∀ (t : ℕ),
          VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ t)) τ μ
            ≤ (VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ 0)) τ μ) * (1 - K) ^ t) := by
  intro h
  exact mei6_false (fun M logits F hF hr hγ₀ hγ₁ τ hτ μ η hη θ hstep K hK₀ hK₁ t =>
    h Unit Bool inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance M logits F hF hr hγ₀ hγ₁ τ hτ μ η hη θ hstep K hK₀ hK₁ t)

end Mei6

end Proofs
end PolicyGradient
