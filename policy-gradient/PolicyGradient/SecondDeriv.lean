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

/-!
### The second derivative of the value function

Differentiating `dV_{m+1} = localTerm_m + γ·∑ step·dV_m` in `θ` gives

  `d2V_{m+1} = d(localTerm_m) + γ·∑ (dstep · dV_m + step · d2V_m)`

We define `d2V` by that recursion and bound it by the same induction that
bounded `dV`.
-/

/-- The second derivative of the value function, by the recursion obtained from
differentiating `dV_succ`. The `dlocal` argument is the derivative of the local
term, supplied by the caller since it depends on how `Q` varies. -/
noncomputable def d2V (dlocal : ℕ → S → ℝ) : ℕ → S → ℝ
  | 0, _ => 0
  | m + 1, s => dlocal m s
      + M.γ * ∑ s', (dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'
          + step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V dlocal m s')

@[simp] theorem d2V_zero (dlocal : ℕ → S → ℝ) (s : S) :
    d2V M PF θ dlocal 0 s = 0 := rfl

theorem d2V_succ (dlocal : ℕ → S → ℝ) (m : ℕ) (s : S) :
    d2V M PF θ dlocal (m + 1) s
      = dlocal m s
        + M.γ * ∑ s', (dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'
            + step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V M PF θ dlocal m s') :=
  rfl

/-- **The second-derivative bound.**

If the local term's derivative is bounded by `L₂` and the first derivative by
`G` (which `abs_dV_le_concrete` supplies as `D/(1-γ)²`), then

  `|d2V_m| ≤ (L₂ + γ·D·G) · ∑_{i<m} γⁱ`

The same induction as `abs_dV_le`: the new ingredient is the `dstep · dV` cross
term, whose total variation is `D·G` by `sum_abs_dstep_le`. -/
theorem abs_d2V_le (dlocal : ℕ → S → ℝ) (L₂ G D : ℝ)
    (hL₂ : 0 ≤ L₂) (hG : 0 ≤ G) (hD : 0 ≤ D)
    (hdloc : ∀ (j : ℕ) (s : S), |dlocal j s| ≤ L₂)
    (hdV : ∀ (j : ℕ) (s : S), |dV M PF.toDiffPolicy θ j s| ≤ G)
    (hscore : ∀ s, ∑ a, |PF.dπ θ s a| ≤ D)
    (hγ₀ : 0 ≤ M.γ) (m : ℕ) (s : S) :
    |d2V M PF θ dlocal m s| ≤ (L₂ + M.γ * (D * G)) * ∑ i ∈ range m, M.γ ^ i := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [d2V_succ]
    set K := L₂ + M.γ * (D * G) with hK
    have hKnn : 0 ≤ K := by
      have : 0 ≤ M.γ * (D * G) := mul_nonneg hγ₀ (mul_nonneg hD hG)
      simp only [hK]; linarith
    -- cross term: ∑ |dstep| |dV| ≤ D·G
    have hcross : |∑ s', dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'| ≤ D * G := by
      calc |∑ s', dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'|
          ≤ ∑ s', |dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s', |dstep M PF θ s s'| * |dV M PF.toDiffPolicy θ m s'| := by
            refine Finset.sum_congr rfl fun s' _ => abs_mul _ _
        _ ≤ ∑ s', |dstep M PF θ s s'| * G := by
            refine Finset.sum_le_sum fun s' _ => ?_
            exact mul_le_mul_of_nonneg_left (hdV m s') (abs_nonneg _)
        _ = (∑ s', |dstep M PF θ s s'|) * G := by rw [← Finset.sum_mul]
        _ ≤ D * G := mul_le_mul_of_nonneg_right
            (sum_abs_dstep_le M PF θ D hscore s) hG
    -- recursive term: ∑ step · d2V ≤ K ∑_{i<m} γⁱ
    have hrec : |∑ s', step M (PF.toDiffPolicy.toPolicy θ) s s'
          * d2V M PF θ dlocal m s'| ≤ K * ∑ i ∈ range m, M.γ ^ i := by
      calc |∑ s', step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V M PF θ dlocal m s'|
          ≤ ∑ s', |step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V M PF θ dlocal m s'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s', step M (PF.toDiffPolicy.toPolicy θ) s s' * |d2V M PF θ dlocal m s'| := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [abs_mul, abs_of_nonneg (step_nonneg M _ s s')]
        _ ≤ ∑ s', step M (PF.toDiffPolicy.toPolicy θ) s s' * (K * ∑ i ∈ range m, M.γ ^ i) := by
            refine Finset.sum_le_sum fun s' _ => ?_
            exact mul_le_mul_of_nonneg_left (ih s') (step_nonneg M _ s s')
        _ = K * ∑ i ∈ range m, M.γ ^ i := by
            rw [← Finset.sum_mul, step_sum_eq_one, one_mul]
    -- combine: |dlocal| + γ(|cross| + |rec|) ≤ K + γ·K·∑ = K·∑_{i<m+1}
    have hsplit : |∑ s', (dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'
          + step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V M PF θ dlocal m s')|
        ≤ D * G + K * ∑ i ∈ range m, M.γ ^ i := by
      rw [Finset.sum_add_distrib]
      exact le_trans (abs_add_le _ _) (add_le_add hcross hrec)
    calc |dlocal m s + M.γ * ∑ s', (dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'
            + step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V M PF θ dlocal m s')|
        ≤ |dlocal m s| + |M.γ * ∑ s', (dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'
            + step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V M PF θ dlocal m s')| :=
          abs_add_le _ _
      _ ≤ L₂ + M.γ * (D * G + K * ∑ i ∈ range m, M.γ ^ i) := by
          refine add_le_add (hdloc m s) ?_
          rw [abs_mul, abs_of_nonneg hγ₀]
          exact mul_le_mul_of_nonneg_left hsplit hγ₀
      _ = K + M.γ * (K * ∑ i ∈ range m, M.γ ^ i) := by simp only [hK]; ring
      _ = K * ∑ i ∈ range (m + 1), M.γ ^ i := by
          rw [Finset.sum_range_succ']
          simp only [pow_zero, pow_succ]
          rw [← Finset.sum_mul]
          ring

end PolicyGradient
