/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G7b

/-!
# A sharper Lipschitz constant for the softmax expected-value gradient map.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section DgLip

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- `ℓ²` version of `norm_comb_le`: the projections `pr (s,b)` are orthonormal,
so a combination has operator norm at most the `ℓ²` norm of the coefficients. -/
theorem norm_comb_le_l2 (s : S) (c : A → ℝ) :
    ‖∑ b : A, c b • (pr (S:=S) (A:=A) (s,b))‖ ≤ Real.sqrt (∑ b, (c b)^2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun v => ?_)
  have happ : (∑ b : A, c b • (pr (S:=S) (A:=A) (s,b))) v = ∑ b, c b * v (s,b) := by
    simp [ContinuousLinearMap.sum_apply]
  rw [happ, Real.norm_eq_abs]
  have hcs : |∑ b, c b * v (s,b)| ≤ Real.sqrt (∑ b, (c b)^2) * Real.sqrt (∑ b, (v (s,b))^2) := by
    have h1 : ∑ b, c b * v (s,b) ≤ Real.sqrt (∑ b, (c b)^2) * Real.sqrt (∑ b, (v (s,b))^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    have h2 : ∑ b, (-(c b)) * v (s,b) ≤ Real.sqrt (∑ b, (-(c b))^2) * Real.sqrt (∑ b, (v (s,b))^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    have h3 : ∑ b, (-(c b)) * v (s,b) = -(∑ b, c b * v (s,b)) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun b _ => by ring
    have h4 : ∑ b, (-(c b))^2 = ∑ b, (c b)^2 := Finset.sum_congr rfl fun b _ => by ring
    rw [h3, h4] at h2
    exact abs_le.2 ⟨by linarith, h1⟩
  refine hcs.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [show ‖v‖ = Real.sqrt (∑ i : S × A, ‖v i‖^2) from EuclideanSpace.norm_eq v]
  refine Real.sqrt_le_sqrt ?_
  rw [Fintype.sum_prod_type]
  refine Finset.single_le_sum (f := fun x : S => ∑ b : A, ‖v (x,b)‖^2)
    (fun x _ => Finset.sum_nonneg fun b _ => by positivity) (mem_univ s) |>.trans_eq' ?_
  exact Finset.sum_congr rfl fun b _ => by rw [Real.norm_eq_abs, sq_abs]

/-- **`‖dg‖ ≤ ‖q‖₂`.** The coefficient vector is `P_b (q_b - ḡ)`; since `P_b ≤ 1`
we have `∑ P_b²(q_b-ḡ)² ≤ ∑ P_b (q_b-ḡ)² = Var_P(q) ≤ ∑ P_b q_b² ≤ ∑ q_b²`. -/
theorem norm_dg_le_l2 (s : S) (q : A → ℝ) (t : E S A) :
    ‖dg (S:=S) (A:=A) s q t‖ ≤ Real.sqrt (∑ a, (q a)^2) := by
  set P : A → ℝ := fun b => p (S := S) (A := A) s b t with hPdef
  have hPn : ∀ b, 0 ≤ P b := fun b => p_nonneg (S := S) (A := A) s b t
  have hP1 : ∀ b, P b ≤ 1 := fun b => p_le_one (S := S) (A := A) s b t
  have hsum : ∑ b, P b = 1 := p_sum_eq_one (S := S) (A := A) s t
  set G : ℝ := ∑ a, P a * q a with hG
  have hdg : dg (S:=S) (A:=A) s q t = ∑ b : A, (P b * (q b - G)) • (pr (S:=S) (A:=A) (s,b)) := rfl
  rw [hdg]
  refine (norm_comb_le_l2 s (fun b => P b * (q b - G))).trans ?_
  refine Real.sqrt_le_sqrt ?_
  -- ∑ P_b² (q_b - G)² ≤ ∑ P_b (q_b - G)² = ∑ P_b q_b² - G² ≤ ∑ q_b²
  have step1 : ∑ b, (P b * (q b - G))^2 ≤ ∑ b, P b * (q b - G)^2 := by
    refine Finset.sum_le_sum fun b _ => ?_
    have heq : (P b * (q b - G))^2 = P b * (P b * (q b - G)^2) := by ring
    rw [heq]
    have hnn : (0:ℝ) ≤ P b * (q b - G)^2 := mul_nonneg (hPn b) (sq_nonneg _)
    exact mul_le_of_le_one_left hnn (hP1 b)
  have step2 : ∑ b, P b * (q b - G)^2 = (∑ b, P b * (q b)^2) - G^2 := by
    have expand : ∀ b, P b * (q b - G)^2 = P b * (q b)^2 - 2*G*(P b * q b) + G^2 * P b := by
      intro b; ring
    rw [Finset.sum_congr rfl (fun b _ => expand b)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum (a := G^2), hsum, mul_one]
    have : ∑ b, 2*G*(P b * q b) = 2*G*G := by rw [← Finset.mul_sum, ← hG]
    rw [this]; ring
  have step3 : ∑ b, P b * (q b)^2 ≤ ∑ b, (q b)^2 := by
    refine Finset.sum_le_sum fun b _ => ?_
    nlinarith [sq_nonneg (q b), hP1 b, hPn b]
  nlinarith [sq_nonneg G]

/-- Mean-value form of `norm_dg_le_l2`: `g s q` is `‖q‖₂`-Lipschitz. -/
theorem g_lipschitz_l2 (s : S) (q : A → ℝ) (θ₁ θ₂ : E S A) :
    |g (S:=S) (A:=A) s q θ₁ - g (S:=S) (A:=A) s q θ₂|
      ≤ Real.sqrt (∑ a, (q a)^2) * ‖θ₁ - θ₂‖ := by
  have hdiff : ∀ x : E S A, DifferentiableAt ℝ (g (S:=S) (A:=A) s q) x :=
    fun x => (hasFDeriv_g s q x).differentiableAt
  have hfd : ∀ x : E S A, fderiv ℝ (g (S:=S) (A:=A) s q) x = dg (S:=S) (A:=A) s q x :=
    fun x => (hasFDeriv_g s q x).fderiv
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g (S:=S) (A:=A) s q)
    (s := (Set.univ : Set (E S A))) (C := Real.sqrt (∑ a, (q a)^2))
    (fun x _ => hdiff x) (fun x _ => by rw [hfd x]; exact norm_dg_le_l2 s q x)
    convex_univ (Set.mem_univ θ₂) (Set.mem_univ θ₁)
  simpa [Real.norm_eq_abs] using hmvt

/-- **The softmax probability vector is `1`-Lipschitz in `ℓ²`.**

Duality: `‖ΔP‖₂ = ⟨ε, ΔP⟩` for the unit vector `ε = ΔP/‖ΔP‖₂`, and
`θ ↦ ⟨ε, P(θ)⟩` is exactly `g s ε`, which is `‖ε‖₂ = 1`-Lipschitz by
`g_lipschitz_l2`. -/
theorem l2_p_sub_le (s : S) (θ₁ θ₂ : E S A) :
    Real.sqrt (∑ b, (p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂)^2)
      ≤ ‖θ₁ - θ₂‖ := by
  classical
  set d : A → ℝ := fun b => p (S := S) (A := A) s b θ₁ - p (S := S) (A := A) s b θ₂ with hd
  set N : ℝ := Real.sqrt (∑ b, (d b)^2) with hN
  have hNn : 0 ≤ N := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hNn with hz | hpos
  · rw [← hz]; exact norm_nonneg _
  have hNne : N ≠ 0 := ne_of_gt hpos
  -- ε = d / N
  set ε : A → ℝ := fun b => d b / N with hε
  have hεsq : ∑ b, (ε b)^2 = 1 := by
    have hNsq : N^2 = ∑ b, (d b)^2 := Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg _)
    have : ∑ b, (ε b)^2 = (∑ b, (d b)^2) / N^2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by rw [hε]; field_simp
    rw [this, hNsq]
    have hsne : (∑ b, (d b)^2) ≠ 0 := by rw [← hNsq]; exact pow_ne_zero 2 hNne
    exact div_self hsne
  have hgd : ∑ b, ε b * d b = g (S := S) (A := A) s ε θ₁ - g (S := S) (A := A) s ε θ₂ := by
    unfold g
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [hd]; unfold p; ring
  have hNeq : ∑ b, ε b * d b = N := by
    have : ∑ b, ε b * d b = (∑ b, (d b)^2) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun b _ => by rw [hε]; ring
    rw [this, ← Real.sq_sqrt (Finset.sum_nonneg fun b _ => sq_nonneg (d b)), ← hN]
    field_simp
  have hlip := g_lipschitz_l2 (S := S) (A := A) s ε θ₁ θ₂
  rw [hεsq, Real.sqrt_one, one_mul] at hlip
  calc N = ∑ b, ε b * d b := hNeq.symm
    _ = g (S := S) (A := A) s ε θ₁ - g (S := S) (A := A) s ε θ₂ := hgd
    _ ≤ |g (S := S) (A := A) s ε θ₁ - g (S := S) (A := A) s ε θ₂| := le_abs_self _
    _ ≤ ‖θ₁ - θ₂‖ := hlip

/-- `‖P‖₂ ≤ 1` for a probability vector: `∑ P_b² ≤ (∑ P_b)² = 1`. -/
theorem l2_p_le_one (s : S) (θ : E S A) :
    Real.sqrt (∑ b, (p (S := S) (A := A) s b θ)^2) ≤ 1 := by
  set P : A → ℝ := fun b => p (S := S) (A := A) s b θ with hP
  have hPn : ∀ b, 0 ≤ P b := fun b => p_nonneg (S := S) (A := A) s b θ
  have hP1 : ∀ b, P b ≤ 1 := fun b => p_le_one (S := S) (A := A) s b θ
  have hsum : ∑ b, P b = 1 := p_sum_eq_one (S := S) (A := A) s θ
  have hle : ∑ b, (P b)^2 ≤ 1 := by
    calc ∑ b, (P b)^2 ≤ ∑ b, P b := by
          refine Finset.sum_le_sum fun b _ => ?_
          have : (P b)^2 = P b * P b := sq (P b) ▸ by ring
          rw [this]
          exact mul_le_of_le_one_left (hPn b) (hP1 b)
      _ = 1 := hsum
  calc Real.sqrt (∑ b, (P b)^2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
    _ = 1 := Real.sqrt_one

/-- **The softmax gradient map is `4B`-Lipschitz** — sharper than AKM's `5B`.

The `ℓ²` split of the coefficient difference is
`Δ_b = (ΔP)_b (q_b - G₁) + P₂(b) (G₂ - G₁)`, so
`‖Δ‖₂ ≤ 2B ‖ΔP‖₂ + |G₂ - G₁| ‖P₂‖₂ ≤ 2B‖Δθ‖ + 2B‖Δθ‖`,
using `l2_p_sub_le` (`‖ΔP‖₂ ≤ ‖Δθ‖`) and `l2_p_le_one` (`‖P₂‖₂ ≤ 1`). -/
theorem dg_lipschitz4 (s : S) (q : A → ℝ) (B : ℝ) (hq : ∀ a, |q a| ≤ B) (θ₁ θ₂ : E S A) :
    ‖dg (S := S) (A := A) s q θ₁ - dg (S := S) (A := A) s q θ₂‖ ≤ 4 * B * ‖θ₁ - θ₂‖ := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hq (Classical.arbitrary A))
  set P₁ : A → ℝ := fun b => p (S := S) (A := A) s b θ₁ with hP₁
  set P₂ : A → ℝ := fun b => p (S := S) (A := A) s b θ₂ with hP₂
  set G₁ : ℝ := g (S := S) (A := A) s q θ₁ with hG₁
  set G₂ : ℝ := g (S := S) (A := A) s q θ₂ with hG₂
  have hdiff : dg (S := S) (A := A) s q θ₁ - dg (S := S) (A := A) s q θ₂
      = ∑ b : A, ((P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂))) • (pr (S := S) (A := A) (s, b)) := by
    unfold dg
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    show (P₁ b * (q b - G₁)) • (pr (S := S) (A := A) (s, b))
        - (P₂ b * (q b - G₂)) • (pr (S := S) (A := A) (s, b)) = _
    module
  rw [hdiff]
  refine (norm_comb_le_l2 s (fun b => (P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂)))).trans ?_
  -- Split the coefficient vector: u_b + w_b
  set u : A → ℝ := fun b => (P₁ b - P₂ b) * (q b - G₁) with hu
  set w : A → ℝ := fun b => P₂ b * (G₂ - G₁) with hw
  have hsplit : ∀ b, (P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂)) = u b + w b := by
    intro b; rw [hu, hw]; ring
  rw [Finset.sum_congr rfl (fun b _ => by rw [hsplit b] :
      ∀ b ∈ (univ : Finset A), ((P₁ b * (q b - G₁)) - (P₂ b * (q b - G₂)))^2 = (u b + w b)^2)]
  -- Minkowski: √(∑ (u+w)²) ≤ √(∑ u²) + √(∑ w²)
  have hmink : Real.sqrt (∑ b, (u b + w b)^2)
      ≤ Real.sqrt (∑ b, (u b)^2) + Real.sqrt (∑ b, (w b)^2) := by
    have := norm_add_le ((EuclideanSpace.equiv A ℝ).symm u) ((EuclideanSpace.equiv A ℝ).symm w)
    simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using this
  refine hmink.trans ?_
  -- Bound each piece.
  have hbarB : |G₁| ≤ B := abs_g_le s q B hq θ₁
  have hrange : ∀ b, |q b - G₁| ≤ 2 * B := by
    intro b
    calc |q b - G₁| ≤ |q b| + |G₁| := abs_sub _ _
      _ ≤ B + B := add_le_add (hq b) hbarB
      _ = 2 * B := by ring
  -- ‖u‖₂ ≤ 2B ‖ΔP‖₂ ≤ 2B ‖Δθ‖
  have hu2 : Real.sqrt (∑ b, (u b)^2) ≤ 2 * B * ‖θ₁ - θ₂‖ := by
    have hptw : ∑ b, (u b)^2 ≤ (2*B)^2 * ∑ b, (P₁ b - P₂ b)^2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [hu]
      have : ((P₁ b - P₂ b) * (q b - G₁))^2 = (P₁ b - P₂ b)^2 * (q b - G₁)^2 := by ring
      rw [this, mul_comm ((2*B)^2) _]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have h1 : (q b - G₁)^2 = |q b - G₁|^2 := (sq_abs _).symm
      rw [h1]
      nlinarith [abs_nonneg (q b - G₁), hrange b, hB]
    calc Real.sqrt (∑ b, (u b)^2)
        ≤ Real.sqrt ((2*B)^2 * ∑ b, (P₁ b - P₂ b)^2) := Real.sqrt_le_sqrt hptw
      _ = (2*B) * Real.sqrt (∑ b, (P₁ b - P₂ b)^2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
      _ ≤ (2*B) * ‖θ₁ - θ₂‖ := by
          refine mul_le_mul_of_nonneg_left (l2_p_sub_le (S := S) (A := A) s θ₁ θ₂) (by linarith)
      _ = 2 * B * ‖θ₁ - θ₂‖ := by ring
  -- ‖w‖₂ = |G₂ - G₁| ‖P₂‖₂ ≤ 2B ‖Δθ‖ · 1
  have hw2 : Real.sqrt (∑ b, (w b)^2) ≤ 2 * B * ‖θ₁ - θ₂‖ := by
    have hfac : ∑ b, (w b)^2 = (G₂ - G₁)^2 * ∑ b, (P₂ b)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [hw]; ring
    have hgl : |G₁ - G₂| ≤ 2 * B * ‖θ₁ - θ₂‖ := g_lipschitz s q B hq θ₁ θ₂
    have hgl' : |G₂ - G₁| ≤ 2 * B * ‖θ₁ - θ₂‖ := by rwa [abs_sub_comm] at hgl
    calc Real.sqrt (∑ b, (w b)^2)
        = |G₂ - G₁| * Real.sqrt (∑ b, (P₂ b)^2) := by
          rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      _ ≤ |G₂ - G₁| * 1 :=
          mul_le_mul_of_nonneg_left (l2_p_le_one (S := S) (A := A) s θ₂) (abs_nonneg _)
      _ = |G₂ - G₁| := by ring
      _ ≤ 2 * B * ‖θ₁ - θ₂‖ := hgl'
  linarith

/-- **AKM Lemma E.2 with the stated `5B`**, an immediate corollary of the
sharper `4B` bound of `dg_lipschitz4`. -/
theorem dg_lipschitz5 (s : S) (q : A → ℝ) (B : ℝ) (hq : ∀ a, |q a| ≤ B) (θ₁ θ₂ : E S A) :
    ‖dg (S := S) (A := A) s q θ₁ - dg (S := S) (A := A) s q θ₂‖ ≤ 5 * B * ‖θ₁ - θ₂‖ := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hq (Classical.arbitrary A))
  have h4 := dg_lipschitz4 (S := S) (A := A) s q B hq θ₁ θ₂
  nlinarith [norm_nonneg (θ₁ - θ₂)]

end DgLip

end Proofs
end PolicyGradient
