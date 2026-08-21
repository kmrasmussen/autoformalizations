/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The `1/t` rate from a quadratic decrease recursion

If a nonnegative sequence satisfies `δ_{t+1} ≤ δ_t - K·δ_t²` then `δ_t ≤ 1/(K·t)`.

This recursion is what produces the iteration-complexity bounds in
Agarwal–Kakade–Lee–Mahajan (JMLR 2021) — Theorem 4.1's `T > 64γ|S||A|/((1-γ)⁶ε²)`
and Corollary 5.1's `T ≥ 320|S|²|A|²/((1-γ)⁶ε²)` both come from a quadratic
decrease of exactly this shape. Neither paper that uses it writes the induction
out (Mei et al. defer it to a bandit case with different constants, and dispatch
the base case as "trivially holds up to `t ≤ 5`"), so here it is in full.

The argument: from `δ_{t+1} ≤ δ_t - K δ_t²` and `δ_t > 0`, dividing by
`δ_t δ_{t+1}` gives `1/δ_t ≤ 1/δ_{t+1} - K·δ_t/δ_{t+1} ≤ 1/δ_{t+1} - K`
(using `δ_{t+1} ≤ δ_t`), so `1/δ_t` increases by at least `K` each step.
-/

namespace PolicyGradient

/-- One step of the reciprocal recursion: a quadratic decrease in `δ` is an
additive increase of at least `K` in `1/δ`. -/
theorem inv_add_le_of_quad_decrease {K δ δ' : ℝ} (hK : 0 < K)
    (hδ : 0 < δ) (hδ' : 0 < δ') (hstep : δ' ≤ δ - K * δ ^ 2) :
    1 / δ + K ≤ 1 / δ' := by
  have hmono : δ' ≤ δ := by nlinarith
  -- 1/δ' - 1/δ = (δ - δ')/(δ δ') ≥ K δ² /(δ δ') = K δ/δ' ≥ K
  have hkey : K * δ ^ 2 ≤ δ - δ' := by linarith
  have hprod : 0 < δ * δ' := mul_pos hδ hδ'
  -- multiply through by δ δ' > 0
  have expand : 1 / δ' - (1 / δ + K) = (δ - δ' - K * δ * δ') / (δ * δ') := by
    field_simp; ring
  have hnn : 0 ≤ 1 / δ' - (1 / δ + K) := by
    rw [expand]
    refine div_nonneg ?_ (le_of_lt hprod)
    nlinarith [hkey, hmono, hδ, hδ']
  linarith

/-- **The `1/t` rate.** A nonnegative sequence with a quadratic decrease
satisfies `δ_t ≤ 1/(K·t)` for `t ≥ 1`. -/
theorem le_inv_mul_of_quad_decrease {K : ℝ} (hK : 0 < K) (δ : ℕ → ℝ)
    (hpos : ∀ t, 0 < δ t)
    (hstep : ∀ t, δ (t + 1) ≤ δ t - K * (δ t) ^ 2) (t : ℕ) :
    1 / δ 0 + K * t ≤ 1 / δ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := inv_add_le_of_quad_decrease hK (hpos t) (hpos (t + 1)) (hstep t)
    push_cast
    push_cast at ih
    linarith

/-- The rate in the form the papers state it: `δ_t ≤ 1/(K·t)`. -/
theorem quad_decrease_rate {K : ℝ} (hK : 0 < K) (δ : ℕ → ℝ)
    (hpos : ∀ t, 0 < δ t)
    (hstep : ∀ t, δ (t + 1) ≤ δ t - K * (δ t) ^ 2) (t : ℕ) (ht : 1 ≤ t) :
    δ t ≤ 1 / (K * t) := by
  have hmain := le_inv_mul_of_quad_decrease hK δ hpos hstep t
  have ht' : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hKt : 0 < K * (t : ℝ) := mul_pos hK (by linarith)
  have h0 : 0 < 1 / δ 0 := by
    have := hpos 0
    positivity
  have : K * (t : ℝ) ≤ 1 / δ t := by linarith
  rw [le_div_iff₀ (hpos t)] at this
  rw [le_div_iff₀ hKt]
  linarith

end PolicyGradient
