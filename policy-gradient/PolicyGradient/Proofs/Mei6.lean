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


/-! ### A second, stronger refutation: the genuine tabular softmax

The refutation above uses the freedom in `logits`. One might hope that pinning
`logits` to the tabular parameterization — the one Mei actually analyses —
rescues the statement. It does not: `η` is also free, and a step size that is
too large makes the objective *decrease*, so the gap **grows**. That contradicts
the claimed bound for **every** `K ∈ (0,1)` at once, which isolates the two
defects: even with `logits` pinned, `η` free and `K` universal is still false.

The MDP is one state, two actions, `γ = 0`, `r = (1, 0)`, `τ = 1`. Writing
`d = θ i0 - θ i1` for the logit gap, the objective reduces to the scalar profile

  `sig d = e^d/(e^d+1)`,  `fsoft d = sig d * (1 - d) + log (e^d + 1)`

with `fsoft' d = (1 - d) e^d / (e^d + 1)^2`, so `fsoft' 0 = 1/4`. Starting at
`θ 0 = 0` and taking `η = 10`, one ascent step sends `d` from `0` to
`2 * 10 * (1/4) = 5`, and `fsoft 5 < fsoft 0`. -/

section Tabular

/-- The one-state two-action MDP with `γ = 0` and `r = (1, 0)`. -/
noncomputable def tMDP : FiniteMDP (Fin 1) (Fin 2) where
  P := fun _ _ => ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩
  r := fun _ a => if a = 0 then 1 else 0
  γ := 0

theorem tMDP_hr : ∀ s a, |tMDP.r s a| ≤ 1 := by
  intro s a; by_cases h : a = 0 <;> simp [tMDP, h]

theorem tMDP_hγ₀ : (0:ℝ) ≤ tMDP.γ := le_of_eq rfl
theorem tMDP_hγ₁ : tMDP.γ < 1 := by norm_num [tMDP]

/-- With `γ = 0`, `Vinf` is the one-step expected reward. -/
theorem Vinf_tMDP (π : Policy (Fin 1) (Fin 2)) :
    Vinf tMDP π 0 = (π 0) 0 := by
  have h : Vinf tMDP π 0 = ∑ a, (π 0) a * tMDP.r 0 a := by
    unfold Vinf
    rw [tsum_eq_single 0]
    · unfold stepReward; simp [tMDP]
    · intro t ht; unfold stepReward
      have : tMDP.γ = 0 := rfl
      rw [this, zero_pow ht, zero_mul]
  rw [h, Fin.sum_univ_two]
  show (π 0) 0 * tMDP.r 0 0 + (π 0) 1 * tMDP.r 0 1 = _
  simp [tMDP]

/-! #### The scalar profile -/

/-- `sig d = e^d / (e^d + 1)`, the probability of action `0`. -/
noncomputable def sig (d : ℝ) : ℝ := Real.exp d / (Real.exp d + 1)

/-- The entropy-regularized objective as a function of the logit gap. -/
noncomputable def fsoft (d : ℝ) : ℝ := sig d * (1 - d) + Real.log (Real.exp d + 1)

theorem fsoft_deriv (d : ℝ) :
    HasDerivAt fsoft ((1 - d) * Real.exp d / (Real.exp d + 1) ^ 2) d := by
  have hp : (0:ℝ) < Real.exp d + 1 := by positivity
  have hne : Real.exp d + 1 ≠ 0 := ne_of_gt hp
  -- `sig` has derivative `e^d/(e^d+1)^2`
  have hsig : HasDerivAt sig (Real.exp d / (Real.exp d + 1) ^ 2) d := by
    have hnum : HasDerivAt Real.exp (Real.exp d) d := Real.hasDerivAt_exp d
    have hden : HasDerivAt (fun y => Real.exp y + 1) (Real.exp d) d :=
      (Real.hasDerivAt_exp d).add_const 1
    have h := hnum.div hden hne
    have heq : (Real.exp d * (Real.exp d + 1) - Real.exp d * Real.exp d)
        / (Real.exp d + 1) ^ 2 = Real.exp d / (Real.exp d + 1) ^ 2 := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [← heq]; exact h
  -- `log (e^d+1)` has derivative `e^d/(e^d+1)` = `sig d`
  have hlog : HasDerivAt (fun y => Real.log (Real.exp y + 1))
      (Real.exp d / (Real.exp d + 1)) d := by
    have hden : HasDerivAt (fun y => Real.exp y + 1) (Real.exp d) d :=
      (Real.hasDerivAt_exp d).add_const 1
    simpa [div_eq_mul_inv, mul_comm] using hden.log hne
  have hlin : HasDerivAt (fun y => (1:ℝ) - y) (-1) d := by
    simpa using (hasDerivAt_id d).const_sub 1
  have hcomb := (hsig.mul hlin).add hlog
  have heq2 : Real.exp d / (Real.exp d + 1) ^ 2 * (1 - d) + sig d * (-1)
      + Real.exp d / (Real.exp d + 1)
      = (1 - d) * Real.exp d / (Real.exp d + 1) ^ 2 := by
    simp only [sig]
    field_simp
    ring
  rw [heq2] at hcomb
  exact hcomb

theorem fsoft_zero : fsoft 0 = 1/2 + Real.log 2 := by
  simp [fsoft, sig]
  norm_num

theorem fsoft_deriv_zero : (1 - (0:ℝ)) * Real.exp 0 / (Real.exp 0 + 1) ^ 2 = 1/4 := by
  simp; norm_num


/-! #### The tabular softmax family -/

/-- The tabular softmax policy family on `E9` — the parameterization Mei uses. -/
noncomputable def Ft : VecPolicy (Fin 1) (Fin 2) E9 where
  toPolicy := fun θ s => softmax (tlog θ s)
  dπ := fun θ s a => fderiv ℝ (fun t => (softmax (tlog t s)) a) θ
  hasFDeriv := fun θ s a => by
    have hd : Differentiable ℝ (fun t : E9 => (softmax (tlog t s)) a) :=
      softmax_diff (fun t => tlog t s)
        (fun a' t => (EuclideanSpace.proj (𝕜 := ℝ) (s, a')).differentiableAt) a
    exact (hd θ).hasFDerivAt

theorem Ft_hF : ∀ θ s a, (Ft.toPolicy θ s) a = softmax (tlog θ s) a := fun _ _ _ => rfl

/-- The entropy of the tabular softmax policy, in terms of the logit gap. -/
theorem entropy_tabular (θ : E9) :
    entropy (Ft.toPolicy θ 0) = Real.log (Real.exp (θ i0 - θ i1) + 1)
      - sig (θ i0 - θ i1) * (θ i0 - θ i1) := by
  set d := θ i0 - θ i1 with hd
  have hp : (0:ℝ) < Real.exp d + 1 := by positivity
  have h0 : (Ft.toPolicy θ 0) 0 = sig d := by
    rw [Ft_hF, softmax_a0]; rfl
  have h1 : (Ft.toPolicy θ 0) 1 = 1 / (Real.exp d + 1) := by
    rw [Ft_hF, softmax_a1]
  -- `log (sig d) = d - log (e^d+1)` and `log (1/(e^d+1)) = -log (e^d+1)`
  have hl0 : Real.log (sig d) = d - Real.log (Real.exp d + 1) := by
    rw [sig, Real.log_div (by positivity) (ne_of_gt hp), Real.log_exp]
  have hl1 : Real.log (1 / (Real.exp d + 1)) = -Real.log (Real.exp d + 1) := by
    rw [one_div, Real.log_inv]
  have hsum : sig d + 1 / (Real.exp d + 1) = 1 := by
    rw [sig]; field_simp
  have h1' : (Ft.toPolicy θ 0) 1 = 1 - sig d := by rw [h1]; linarith [hsum]
  have hl1' : Real.log ((1:ℝ) - sig d) = -Real.log (Real.exp d + 1) := by
    rw [show (1:ℝ) - sig d = 1 / (Real.exp d + 1) by linarith [hsum]]; exact hl1
  simp only [entropy, Fin.sum_univ_two, h0, h1', hl0, hl1']
  ring

/-- **The objective equals `fsoft` of the logit gap.** -/
theorem VinfSoft_eq_fsoft (θ : E9) :
    VinfSoft tMDP (Ft.toPolicy θ) 1 0 = fsoft (θ i0 - θ i1) := by
  show Vinf tMDP (Ft.toPolicy θ) 0 + 1 * entropy (Ft.toPolicy θ 0) = _
  rw [Vinf_tMDP, entropy_tabular]
  have h0 : (Ft.toPolicy θ 0) 0 = sig (θ i0 - θ i1) := by
    rw [Ft_hF, softmax_a0]; rfl
  rw [h0, fsoft]
  ring


/-! #### The gradient, and one ascent step from `θ = 0` -/

/-- The gradient of the entropy-regularized objective at `θ`. -/
theorem gradient_VinfSoft (θ : E9) :
    gradient (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) θ
      = ((1 - (θ i0 - θ i1)) * Real.exp (θ i0 - θ i1)
          / (Real.exp (θ i0 - θ i1) + 1) ^ 2) • dvec := by
  have hfun : (fun w : E9 => VinfSoft tMDP (Ft.toPolicy w) 1 0)
      = fun w : E9 => fsoft (w i0 - w i1) := funext VinfSoft_eq_fsoft
  rw [hfun]
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt, map_smul, toDual_dvec]
  have hl : HasFDerivAt (fun w : E9 => w i0 - w i1) dl θ := dl.hasFDerivAt
  exact (fsoft_deriv (θ i0 - θ i1)).comp_hasFDerivAt θ hl

/-- One ascent step of size `η` from `θ` moves the logit gap by `2η·f'`. -/
theorem tgap_step (θ : E9) (η : ℝ) :
    (θ + η • gradient (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) θ) i0
      - (θ + η • gradient (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) θ) i1
      = (θ i0 - θ i1)
        + 2 * η * ((1 - (θ i0 - θ i1)) * Real.exp (θ i0 - θ i1)
            / (Real.exp (θ i0 - θ i1) + 1) ^ 2) := by
  rw [gradient_VinfSoft]
  simp [PiLp.add_apply, PiLp.smul_apply, dvec_i0, dvec_i1, smul_eq_mul]
  ring

/-- From `θ = 0` with `η = 10`, one step sends the logit gap to exactly `5`. -/
theorem tgap_step_zero :
    ((0 : E9) + (10:ℝ) • gradient (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) 0) i0
      - ((0 : E9) + (10:ℝ) • gradient (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) 0) i1
      = 5 := by
  rw [tgap_step]
  norm_num


/-! #### The objective *decreases*: `fsoft 5 < fsoft 0` -/

/-- `fsoft 5 < fsoft 0`: the ascent step with `η = 10` overshoots so badly that
the entropy-regularized objective goes **down**. -/
theorem fsoft_five_lt_zero : fsoft 5 < fsoft 0 := by
  have he : (148:ℝ) < Real.exp 5 := by
    have h := Real.exp_one_gt_d9
    have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h5]
    have hb : (2.7182818283 : ℝ) ≤ Real.exp 1 := h.le
    calc (148:ℝ) < 2.7182818283 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := by
          exact pow_le_pow_left₀ (by norm_num) hb 5
  have hp : (0:ℝ) < Real.exp 5 + 1 := by positivity
  -- `fsoft 5 = sig 5 * (-4) + log (e^5+1)`
  have hf5 : fsoft 5 = -(4 * sig 5) + Real.log (Real.exp 5 + 1) := by
    rw [fsoft]; ring
  -- `sig 5 ≥ 148/149`
  have hsig : (148:ℝ)/149 ≤ sig 5 := by
    rw [sig, le_div_iff₀ hp]
    nlinarith [he]
  -- `log (e^5+1) ≤ 5 + 1/148`, since `e^5+1 ≤ e^5 * (1 + 1/148)` and `log(1+x) ≤ x`
  have hlog : Real.log (Real.exp 5 + 1) ≤ 5 + 1/148 := by
    have hle : Real.exp 5 + 1 ≤ Real.exp (5 + 1/148) := by
      rw [Real.exp_add]
      have h1 : (1:ℝ) + 1/148 ≤ Real.exp (1/148) := by
        have := Real.add_one_le_exp (1/148 : ℝ); linarith
      nlinarith [Real.exp_pos (5:ℝ), he]
    calc Real.log (Real.exp 5 + 1) ≤ Real.log (Real.exp (5 + 1/148)) :=
          Real.log_le_log (by positivity) hle
      _ = 5 + 1/148 := Real.log_exp _
  -- `fsoft 0 = 1/2 + log 2 ≥ 1/2 + 0.693`
  have hl2 : (0.693 : ℝ) < Real.log 2 :=
    lt_of_lt_of_le (by norm_num) Real.log_two_gt_d9.le
  rw [hf5, fsoft_zero]
  nlinarith [hsig, hlog, hl2]


/-! #### The refutation with the tabular softmax pinned

Because the objective *decreases* on the first step, the gap **grows**:
`gap 1 > gap 0 ≥ gap 0 * (1 - K)` for every `K ∈ (0,1)`. So no choice of `K`
rescues the statement — the defect is not the size of `K` but the presence of a
free `η` together with a `K` the caller chooses. -/

/-- **Theorem 6 is false even with the tabular softmax pinned.**

`logits = tlog` is exactly Mei's tabular parameterization, yet with `η = 10` the
first ascent step overshoots, the objective decreases, and the suboptimality gap
*grows* — contradicting the claimed bound for **every** `K ∈ (0,1)`. -/
theorem mei6_false_tabular :
    ¬ (∀ (M : FiniteMDP (Fin 1) (Fin 2))
        (logits : E9 → Fin 1 → Fin 2 → ℝ)
        (F : VecPolicy (Fin 1) (Fin 2) E9),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (τ : ℝ), 0 < τ → ∀ (μ : Fin 1) (η : ℝ), 0 < η →
        ∀ (θ : ℕ → E9),
        (∀ t, θ (t + 1)
          = θ t + η • gradient (fun w => VinfSoft M (F.toPolicy w) τ μ) (θ t)) →
        ∀ (K : ℝ), 0 < K → K < 1 → ∀ (t : ℕ),
          VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ t)) τ μ
            ≤ (VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ 0)) τ μ) * (1 - K) ^ t) := by
  intro h
  -- the trajectory: `θ 0 = 0`, then ascent steps of size `10`
  set Θ : ℕ → E9 := fun t => Nat.rec (0 : E9)
    (fun _ prev => prev + (10:ℝ) • gradient
      (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) prev) t with hΘdef
  have hstep : ∀ t, Θ (t + 1)
      = Θ t + (10:ℝ) • gradient (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) (Θ t) :=
    fun _ => rfl
  have hbound := h tMDP tlog Ft Ft_hF tMDP_hr tMDP_hγ₀ tMDP_hγ₁
    1 one_pos 0 10 (by norm_num) Θ hstep (1/2) (by norm_num) (by norm_num) 1
  -- the two values, via the scalar profile
  have hΘ0 : Θ 0 = (0 : E9) := rfl
  have hv0 : VinfSoft tMDP (Ft.toPolicy (Θ 0)) 1 0 = fsoft 0 := by
    rw [VinfSoft_eq_fsoft, hΘ0]
    norm_num
  have hd1 : (Θ 1) i0 - (Θ 1) i1 = 5 := by
    have h1 : Θ 1 = Θ 0 + (10:ℝ) • gradient
        (fun w => VinfSoft tMDP (Ft.toPolicy w) 1 0) (Θ 0) := hstep 0
    rw [h1, hΘ0]; exact tgap_step_zero
  have hv1 : VinfSoft tMDP (Ft.toPolicy (Θ 1)) 1 0 = fsoft 5 := by
    rw [VinfSoft_eq_fsoft, hd1]
  rw [hv0, hv1, pow_one] at hbound
  -- the gap at `t = 0` is nonnegative, since `VsoftStar` is a supremum
  have hbdd : BddAbove (Set.range (fun π : Policy (Fin 1) (Fin 2) => VinfSoft tMDP π 1 0)) := by
    refine ⟨1 + 2, ?_⟩
    rintro x ⟨π, rfl⟩
    show Vinf tMDP π 0 + 1 * entropy (π 0) ≤ 1 + 2
    rw [Vinf_tMDP]
    have h1 : (π 0) 0 ≤ 1 := by
      have hs := (π 0).sum_eq_one
      have hnn := (π 0).nonneg 1
      rw [Fin.sum_univ_two] at hs
      linarith
    have h2 : entropy (π 0) ≤ 2 := by
      have hb : ∀ a : Fin 2, -((π 0) a * Real.log ((π 0) a)) ≤ 1 := by
        intro a
        have := Real.self_sub_one_le_mul_log ((π 0).nonneg a)
        have hnn := (π 0).nonneg a
        linarith
      have hb0 := hb 0
      have hb1 := hb 1
      simp only [entropy, Fin.sum_univ_two, neg_add]
      linarith
    linarith
  have hge : fsoft 0 ≤ VsoftStar tMDP 1 0 := by
    have hle := le_ciSup hbdd (Ft.toPolicy (Θ 0))
    rwa [hv0] at hle
  have hlt := fsoft_five_lt_zero
  linarith

end Tabular



/-! ### A reusable general entropy bound

The only entropy fact the repo has. `x log x ≥ x - 1` for `x ≥ 0` gives
`-x log x ≤ 1 - x`, and summing over a distribution yields `H ≤ |A| - 1`.
(Not the sharp `log |A|`, but enough for `BddAbove`, which is what
`VsoftStar = ⨆ π, …` needs to be a genuine supremum rather than Mathlib's
junk value `0`.) -/

theorem entropy_le_card {A : Type*} [Fintype A] (d : Dist A) :
    entropy d ≤ Fintype.card A - 1 := by
  have hb : ∀ a : A, -(d a * Real.log (d a)) ≤ 1 - d a := by
    intro a
    have := Real.self_sub_one_le_mul_log (d.nonneg a)
    linarith
  have hsum : entropy d ≤ ∑ _a : A, (1:ℝ) - ∑ a, d a := by
    rw [entropy, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun a _ => hb a
  rw [d.sum_eq_one] at hsum
  simpa using hsum

theorem entropy_nonneg {A : Type*} [Fintype A] (d : Dist A) (h : ∀ a, d a ≤ 1) :
    0 ≤ entropy d := by
  rw [entropy, ← Finset.sum_neg_distrib]
  refine Finset.sum_nonneg fun a _ => ?_
  rcases eq_or_lt_of_le (d.nonneg a) with h0 | h0
  · simp [← h0]
  · have := Real.log_nonpos (d.nonneg a) (h a)
    nlinarith

/-! ## What Theorem 6 should say instead

Three things must change. The first two are what the refutations above exploit;
the third is what Mei's proof actually needs.

**1. `K` must be existential, not universal.**
As frozen, `K` is the *caller's* to choose, so a caller picks `K` close to `1`
and demands near-instant convergence. The rate constant is a *conclusion* of the
theorem, determined by `τ`, `γ` and the MDP — not an input. The statement must
open with `∃ K, 0 < K ∧ K < 1 ∧ ∀ t, …`, with `K` outside the `∀ t`. This is the
same defect that sank `mei_theorem4` v1.

In Mei's Theorem 6 the constant is explicit:
`K = (2 τ) / (‖1/μ‖_∞ · (1 - γ)) · (inf_t min_{s,a} π_t(a|s))^2`, so it also
depends on the trajectory — which means either the trajectory-dependent
quantity is carried as an explicit hypothesis (the honest reading, matching how
`c` enters Theorem 4), or a lower bound on `inf_t min_{s,a} π_t(a|s)` is proved
first (their Lemma 16).

**2. `η` must be pinned to the smoothness constant, not free.**
`mei6_false_tabular` takes the *genuine tabular* softmax and `η = 10`: the first
step overshoots so far that the objective **decreases** and the gap grows. Mei
fixes `η = (1-γ)^3 / (8 + τ (4 + 8 log|A|))`, the reciprocal smoothness constant
of the entropy-regularized objective (their Lemma 14). Any statement with `η`
free is false for large `η`, whatever `K` is.

**3. The regularizer is the wrong one — `VinfSoft` is not Mei's `Ṽ`.**
`Target.VinfSoft M π τ s₀ = Vinf M π s₀ + τ * entropy (π s₀)` adds entropy at the
**start state only**. Mei's soft value is the discounted sum of entropies along
the trajectory,
`Ṽ(s₀) = E[∑_t γ^t (r(s_t,a_t) - τ log π(a_t|s_t))]`,
equivalently the fixed point of the soft Bellman operator
`Ṽ(s) = ∑_a π(a|s) (r(s,a) - τ log π(a|s) + γ ∑_{s'} P(s'|s,a) Ṽ(s'))`.
Only the latter makes `VsoftStar` the soft-optimal value with the log-sum-exp
closed form `Ṽ*(s) = τ log ∑_a exp(Q̃*(s,a)/τ)`, and only the latter satisfies
the soft performance-difference and Łojasiewicz lemmas the proof runs on. With
the start-state-only version, the entropy bonus does not propagate, and none of
Lemmas 14-16 is even true as stated.

## Suggested restatement

```lean
theorem mei_theorem6 (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (tabularLogits θ s) a)  -- pinned
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (τ : ℝ) (hτ : 0 < τ) (μ : S)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    -- η pinned to the reciprocal smoothness constant of the *soft* objective
    (hstep : ∀ t, θ (t + 1) = θ t
      + ((1 - M.γ)^3 / (8 + τ * (4 + 8 * Real.log (Fintype.card A))))
        • gradient (fun w => VsoftDisc M (F.toPolicy w) τ μ) (θ t)) :
    ∃ K : ℝ, 0 < K ∧ K < 1 ∧ ∀ t,
      VsoftStarDisc M τ μ - VsoftDisc M (F.toPolicy (θ t)) τ μ
        ≤ (VsoftStarDisc M τ μ - VsoftDisc M (F.toPolicy (θ 0)) τ μ) * (1 - K) ^ t
```
where `VsoftDisc` is the discounted-entropy soft value described in (3).

## Prerequisite goals this needs (none of which exist yet)

* **`VsoftDisc`** — define the soft value as the fixed point of the soft Bellman
  operator (or as a `tsum` of discounted reward-plus-entropy), and prove it is
  well defined and bounded. `entropy_le_card` above is the only entropy bound in
  the repo right now.
* **Soft Bellman / soft performance difference** — the entropy analogue of
  `G1`'s `Vinf_performance_difference`.
* **Mei Lemma 14** — the soft objective is `(8/(1-γ)^3 + τ(4 + 8 log|A|)/(1-γ)^2)`
  smooth. The entropy analogue of `G7b`.
* **Mei Lemma 15** — the soft non-uniform Łojasiewicz inequality.
* **Mei Lemma 16** — `inf_t min_{s,a} π_t(a|s) > 0` along the trajectory.
* **`VsoftStar` is attained** — with the discounted-entropy value the sup is a
  max, attained at the soft-optimal policy `π*(a|s) ∝ exp(Q̃*(s,a)/τ)`.
-/

end Mei6

end Proofs
end PolicyGradient
