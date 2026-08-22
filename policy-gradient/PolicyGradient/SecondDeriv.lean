/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Smoothness
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PolicyGradient.Meta.Paper

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

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [Nonempty A] [DecidableEq A]
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

/-- **The concrete second-derivative bound for softmax.**

With rewards in `[-1,1]`, score total variation `≤ 1`, and the local-term
derivative bounded by `L₂`, the second derivative of the value function is
bounded by

  `(L₂ + γ/(1-γ)²) / (1-γ)`

Taking `L₂ = 3/(1-γ)` — the paper's bound on the reward term — gives
`(3/(1-γ) + γ/(1-γ)²)/(1-γ) ≤ 8/(1-γ)³` by `smoothness_arithmetic`-style
arithmetic. -/
theorem abs_d2V_le_concrete (dlocal : ℕ → S → ℝ) (L₂ : ℝ) (hL₂ : 0 ≤ L₂)
    (hdloc : ∀ (j : ℕ) (s : S), |dlocal j s| ≤ L₂)
    (hscore : ∀ s, ∑ a, |PF.dπ θ s a| ≤ 1)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (m : ℕ) (s : S) :
    |d2V M PF θ dlocal m s|
      ≤ (L₂ + M.γ * (1 / (1 - M.γ) ^ 2)) * (1 / (1 - M.γ)) := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hG : ∀ (j : ℕ) (s' : S), |dV M PF.toDiffPolicy θ j s'| ≤ 1 / (1 - M.γ) ^ 2 :=
    fun j s' => abs_dV_le_softmax M PF.toDiffPolicy θ hscore hr hγ₀ hγ₁ j s'
  have hGnn : (0:ℝ) ≤ 1 / (1 - M.γ) ^ 2 := by positivity
  have hb := abs_d2V_le M PF θ dlocal L₂ (1 / (1 - M.γ) ^ 2) 1
    hL₂ hGnn zero_le_one hdloc hG hscore hγ₀ m s
  refine le_trans hb ?_
  have hgeom : ∑ i ∈ range m, M.γ ^ i ≤ 1 / (1 - M.γ) := by
    have hlt : M.γ ≠ 1 := ne_of_lt hγ₁
    have hpow : (0:ℝ) ≤ M.γ ^ m := pow_nonneg hγ₀ m
    rw [geom_sum_eq hlt, ← sub_nonneg]
    have expand : 1 / (1 - M.γ) - (M.γ ^ m - 1) / (M.γ - 1)
        = M.γ ^ m / (1 - M.γ) := by field_simp; ring
    rw [expand]; positivity
  have hKnn : (0:ℝ) ≤ L₂ + M.γ * (1 * (1 / (1 - M.γ) ^ 2)) := by
    have h2 : (0:ℝ) ≤ M.γ * (1 * (1 / (1 - M.γ) ^ 2)) := by positivity
    linarith
  calc (L₂ + M.γ * (1 * (1 / (1 - M.γ) ^ 2))) * ∑ i ∈ range m, M.γ ^ i
      ≤ (L₂ + M.γ * (1 * (1 / (1 - M.γ) ^ 2))) * (1 / (1 - M.γ)) :=
        mul_le_mul_of_nonneg_left hgeom hKnn
    _ = (L₂ + M.γ * (1 / (1 - M.γ) ^ 2)) * (1 / (1 - M.γ)) := by ring

/-- **The `8/(1-γ)³` constant.** With the paper's local bound `L₂ = 3/(1-γ)`,
the second derivative of the value function is bounded by `8/(1-γ)³` — AKM
Lemma E.4 / Mei Lemma 7's constant. -/
theorem abs_d2V_le_eight (dlocal : ℕ → S → ℝ)
    (hdloc : ∀ (j : ℕ) (s : S), |dlocal j s| ≤ 3 / (1 - M.γ))
    (hscore : ∀ s, ∑ a, |PF.dπ θ s a| ≤ 1)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (m : ℕ) (s : S) :
    |d2V M PF θ dlocal m s| ≤ 8 / (1 - M.γ) ^ 3 := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hL₂ : (0:ℝ) ≤ 3 / (1 - M.γ) := by positivity
  refine le_trans (abs_d2V_le_concrete M PF θ dlocal _ hL₂ hdloc hscore hr hγ₀ hγ₁ m s) ?_
  rw [← sub_nonneg]
  have expand : 8 / (1 - M.γ) ^ 3
      - (3 / (1 - M.γ) + M.γ * (1 / (1 - M.γ) ^ 2)) * (1 / (1 - M.γ))
      = (8 - (3 * (1 - M.γ) + M.γ)) / (1 - M.γ) ^ 3 := by
    field_simp
  rw [expand]
  refine div_nonneg ?_ (by positivity)
  linarith

/-!
### Closing the loop: from the second-derivative bound to `SmoothAt`

A bound `|f''| ≤ β` gives `SmoothAt f f' β` by Taylor's theorem with Lagrange
remainder. Rather than invoke the full machinery we record the implication in
the form the value function supplies it: a bound on the second derivative,
together with `hasDerivAt` for both levels, yields the two-sided Taylor bound.
-/

/-- **From a second-derivative bound to smoothness.**

If `f` has first derivative `f'` and second derivative `f''` everywhere, and
`|f''| ≤ β`, then `f` is `β`-smooth in AKM's sense.

The remainder identity is Taylor–Lagrange: `f y - f x - f'(x)(y-x) =
f''(ξ)(y-x)²/2` for some `ξ` between `x` and `y`. -/
theorem smoothAt_of_abs_second_deriv_le {f f' f'' : ℝ → ℝ} {β : ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x, |f'' x| ≤ β)
    (htaylor : ∀ x y, ∃ ξ, f y - f x - f' x * (y - x) = f'' ξ * (y - x) ^ 2 / 2) :
    SmoothAt f f' β := by
  intro x y
  obtain ⟨ξ, hξ⟩ := htaylor x y
  rw [hξ, abs_div, abs_mul]
  have h2 : |(2:ℝ)| = 2 := by norm_num
  rw [h2, abs_of_nonneg (sq_nonneg (y - x))]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have := hbound ξ
  nlinarith [sq_nonneg (y - x), abs_nonneg (f'' ξ)]

/-- The canonical derivative of the local term.

`localTerm_j s = ∑ₐ dπ(a|s)·Q_j(s,a)`, so by the product rule its derivative is

  `∑ₐ (d2π(a|s)·Q_j(s,a) + dπ(a|s)·dQ_j(s,a))`

with `dQ_j = γ·∑_{s'} P(s'|s,a)·dV_j(s')` from `hasDerivAt_Q`. Everything on the
right is already available, so this needs no new input. -/
noncomputable def dLocalTerm (j : ℕ) (s : S) : ℝ :=
  ∑ a, (PF.d2π θ s a * Q M (PF.toDiffPolicy.toPolicy θ) j s a
    + PF.dπ θ s a * (M.γ * ∑ s', (M.P s a) s' * dV M PF.toDiffPolicy θ j s'))

/-- **`dLocalTerm` really is the derivative of `localTerm`.**

Discharges what was previously the `hdlocal` hypothesis: the product rule
applied termwise, with `hasDeriv2` supplying the policy's second derivative and
`hasDerivAt_Q` the action-value's first. -/
theorem hasDerivAt_localTerm (j : ℕ) (s : S) :
    HasDerivAt (fun t => localTerm M PF.toDiffPolicy t j s)
      (dLocalTerm M PF θ j s) θ := by
  unfold localTerm dLocalTerm
  refine HasDerivAt.fun_sum fun a _ => ?_
  exact (PF.hasDeriv2 θ s a).mul
    (hasDerivAt_Q M PF.toDiffPolicy θ j s a
      (fun s' => hasDerivAt_V M PF.toDiffPolicy θ j s'))

/-- **`d2V` really is the derivative of `dV`.**

By induction on the horizon, mirroring `hasDerivAt_V`. The step differentiates

  `dV_{m+1} = localTerm_m + γ·∑_{s'} step s s' · dV_m s'`

using the product rule on each `step · dV` term: the `dstep · dV` and
`step · d2V` pieces are exactly the two summands in `d2V_succ`.

`hdlocal` supplies that `dlocal` is the derivative of `localTerm`; it depends on
how `Q` varies with the parameter, which is why it is an input rather than
derived here. -/
theorem hasDerivAt_dV (dlocal : ℕ → S → ℝ)
    (hdlocal : ∀ (j : ℕ) (s' : S),
      HasDerivAt (fun t => localTerm M PF.toDiffPolicy t j s') (dlocal j s') θ)
    (m : ℕ) (s : S) :
    HasDerivAt (fun t => dV M PF.toDiffPolicy t m s) (d2V M PF θ dlocal m s) θ := by
  induction m generalizing s with
  | zero => simpa [dV] using hasDerivAt_const θ (0 : ℝ)
  | succ m ih =>
    rw [d2V_succ]
    have hdV : ∀ t, dV M PF.toDiffPolicy t (m + 1) s
        = localTerm M PF.toDiffPolicy t m s
          + M.γ * ∑ s', step M (PF.toDiffPolicy.toPolicy t) s s'
              * dV M PF.toDiffPolicy t m s' := fun t => rfl
    simp only [hdV]
    -- product rule on each step·dV term
    have hterm : ∀ s' ∈ (univ : Finset S),
        HasDerivAt (fun t => step M (PF.toDiffPolicy.toPolicy t) s s'
            * dV M PF.toDiffPolicy t m s')
          (dstep M PF θ s s' * dV M PF.toDiffPolicy θ m s'
            + step M (PF.toDiffPolicy.toPolicy θ) s s' * d2V M PF θ dlocal m s') θ := by
      intro s' _
      exact (hasDerivAt_step M PF θ s s').mul (ih s')
    have hsum := HasDerivAt.fun_sum hterm
    exact (hdlocal m s).add (hsum.const_mul M.γ)

/-- **Sharp smoothness from a second-derivative bound.**

`|f''| ≤ β` gives `SmoothAt f f' β` — the *sharp* constant, matching AKM
Lemma E.4 rather than losing a factor of two.

The trick avoiding the integral form: apply the mean value theorem not to the
remainder `R(t) = f y - f t - f'(t)(y-t)` directly, but to

  `h(t) = R(t) - (β/2)(y-t)²`   and   `k(t) = R(t) + (β/2)(y-t)²`.

Then `h'(t) = -f''(t)(y-t) + β(y-t) = (y-t)(β - f''(t)) ≥ 0` for `t ≤ y`, so `h`
is monotone; likewise `k' ≤ 0`. Since `h(y) = k(y) = 0`, monotonicity pins
`R(x)` between `∓(β/2)(y-x)²`, which is exactly the two-sided Taylor bound. -/
theorem smoothAt_of_abs_second_deriv_le_sharp {f f' f'' : ℝ → ℝ} {β : ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x, |f'' x| ≤ β) :
    SmoothAt f f' β := by
  intro x y
  -- R t = f y - f t - f' t * (y - t);  R' t = -f'' t * (y - t)
  set R : ℝ → ℝ := fun t => f y - f t - f' t * (y - t) with hR
  have hRderiv : ∀ t, HasDerivAt R (-(f'' t * (y - t))) t := by
    intro t
    have hsub : HasDerivAt (fun w : ℝ => y - w) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub y
    have h1 : HasDerivAt (fun w => f' w * (y - w))
        (f'' t * (y - t) + f' t * (-1)) t := (hderiv2 t).mul hsub
    have h2 : HasDerivAt (fun w => f y - f w) (-(f' t)) t := by
      simpa using (hderiv t).const_sub (f y)
    have hsum := h2.sub h1
    have harith : -(f' t) - (f'' t * (y - t) + f' t * (-1)) = -(f'' t * (y - t)) := by
      ring
    rw [harith] at hsum
    exact hsum
  have hRy : R y = 0 := by simp [hR]
  -- h t = R t - (β/2)(y-t)^2 has h' t = (y-t)(β - f'' t) ≥ 0 for t ≤ y
  set h : ℝ → ℝ := fun t => R t - β / 2 * (y - t) ^ 2 with hh
  set k : ℝ → ℝ := fun t => R t + β / 2 * (y - t) ^ 2 with hk
  have hsqderiv : ∀ t, HasDerivAt (fun w : ℝ => (y - w) ^ 2) (-2 * (y - t)) t := by
    intro t
    have hsub : HasDerivAt (fun w : ℝ => y - w) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub y
    have hmul := hsub.mul hsub
    have harith : (-1 : ℝ) * (y - t) + (y - t) * (-1) = -2 * (y - t) := by ring
    have hsq : (fun w : ℝ => (y - w) ^ 2) = fun w : ℝ => (y - w) * (y - w) := by
      funext w; ring
    rw [hsq, ← harith]
    exact hmul
  have hhderiv : ∀ t, HasDerivAt h ((y - t) * (β - f'' t)) t := by
    intro t
    have := (hRderiv t).sub ((hsqderiv t).const_mul (β / 2))
    have harith : -(f'' t * (y - t)) - β / 2 * (-2 * (y - t)) = (y - t) * (β - f'' t) := by
      ring
    rw [harith] at this
    exact this
  have hkderiv : ∀ t, HasDerivAt k (-((y - t) * (β + f'' t))) t := by
    intro t
    have := (hRderiv t).add ((hsqderiv t).const_mul (β / 2))
    have harith : -(f'' t * (y - t)) + β / 2 * (-2 * (y - t))
        = -((y - t) * (β + f'' t)) := by ring
    rw [harith] at this
    exact this
  have hbnn : ∀ t, 0 ≤ β - f'' t := fun t => by
    have := hbound t; cases abs_cases (f'' t) with
    | inl hc => linarith [hc.1]
    | inr hc => linarith [hc.1]
  have hbnn' : ∀ t, 0 ≤ β + f'' t := fun t => by
    have := hbound t; cases abs_cases (f'' t) with
    | inl hc => linarith [hc.1]
    | inr hc => linarith [hc.1]
  have hRx : R x = f y - f x - f' x * (y - x) := rfl
  have hhy : h y = 0 := by simp [hh, hR]
  have hky : k y = 0 := by simp [hk, hR]
  -- Case on the order of x and y; in each case monotonicity of h and k pins R x.
  rcases le_total x y with hxy | hxy
  · -- x ≤ y : on [x,y], h' ≥ 0 so h is monotone, h x ≤ h y = 0
    have hhmono : ∀ t ∈ Set.Icc x y, 0 ≤ (y - t) * (β - f'' t) := by
      intro t ht
      exact mul_nonneg (by linarith [ht.2]) (hbnn t)
    have hkmono : ∀ t ∈ Set.Icc x y, -((y - t) * (β + f'' t)) ≤ 0 := by
      intro t ht
      have : 0 ≤ (y - t) * (β + f'' t) :=
        mul_nonneg (by linarith [ht.2]) (hbnn' t)
      linarith
    have hmono : MonotoneOn h (Set.Icc x y) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc x y)
        (fun t _ => (hhderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hhderiv t).differentiableAt.differentiableWithinAt) ?_
      intro t ht
      rw [(hhderiv t).deriv]
      exact hhmono t (interior_subset ht)
    have hh_le : h x ≤ h y :=
      hmono (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
    have hanti : AntitoneOn k (Set.Icc x y) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc x y)
        (fun t _ => (hkderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hkderiv t).differentiableAt.differentiableWithinAt) ?_
      intro t ht
      rw [(hkderiv t).deriv]
      exact hkmono t (interior_subset ht)
    have hk_ge : k y ≤ k x :=
      hanti (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
    rw [hhy] at hh_le
    rw [hky] at hk_ge
    simp only [hh, hk] at hh_le hk_ge
    rw [abs_le]
    constructor <;> [linarith; linarith]
  · -- y ≤ x : on [y,x], the same derivatives have the opposite sign pattern
    have hhmono : ∀ t ∈ Set.Icc y x, (y - t) * (β - f'' t) ≤ 0 := by
      intro t ht
      have h1 : y - t ≤ 0 := by linarith [ht.1]
      exact mul_nonpos_of_nonpos_of_nonneg h1 (hbnn t)
    have hkmono : ∀ t ∈ Set.Icc y x, 0 ≤ -((y - t) * (β + f'' t)) := by
      intro t ht
      have h1 : y - t ≤ 0 := by linarith [ht.1]
      have : (y - t) * (β + f'' t) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1 (hbnn' t)
      linarith
    have hanti : AntitoneOn h (Set.Icc y x) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc y x)
        (fun t _ => (hhderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hhderiv t).differentiableAt.differentiableWithinAt) ?_
      intro t ht
      rw [(hhderiv t).deriv]
      exact hhmono t (interior_subset ht)
    have hh_le : h x ≤ h y :=
      hanti (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
    have hmono : MonotoneOn k (Set.Icc y x) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc y x)
        (fun t _ => (hkderiv t).continuousAt.continuousWithinAt)
        (fun t _ => (hkderiv t).differentiableAt.differentiableWithinAt) ?_
      intro t ht
      rw [(hkderiv t).deriv]
      exact hkmono t (interior_subset ht)
    have hk_ge : k y ≤ k x :=
      hmono (Set.left_mem_Icc.mpr hxy) (Set.right_mem_Icc.mpr hxy) hxy
    rw [hhy] at hh_le
    rw [hky] at hk_ge
    simp only [hh, hk] at hh_le hk_ge
    rw [abs_le]
    constructor <;> [linarith; linarith]

/-- **Smoothness from a second-derivative bound, via the mean value theorem.**

`|f''| ≤ β` gives `SmoothAt f f' (2β)`.

The MVT bounds the remainder `g y - g x` (where `g t = f t + f' t (y - t)`, so
`g' t = f''(t)(y-t)`) by `sup|g'|·|y-x| ≤ β|y-x|²`, i.e. `SmoothAt f f' (2β)`.

The sharp constant `β` needs the *integral* form of the remainder — integrating
the linear factor `(y-t)` is what produces the `1/2`. We take the factor-of-two
loss rather than assume the sharp bound: `SmoothAt` is monotone in its constant
(`SmoothAt.mono`), so this is a genuine, if slightly lossy, derivation. -/
theorem smoothAt_two_of_abs_second_deriv_le {f f' f'' : ℝ → ℝ} {β : ℝ}
    (hβ : 0 ≤ β)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hderiv2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x, |f'' x| ≤ β) :
    SmoothAt f f' (2 * β) := by
  intro x y
  set g : ℝ → ℝ := fun t => f t + f' t * (y - t) with hg
  have hgderiv : ∀ t, HasDerivAt g (f'' t * (y - t)) t := by
    intro t
    have hsub : HasDerivAt (fun w : ℝ => y - w) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub y
    have h1 : HasDerivAt (fun w => f' w * (y - w))
        (f'' t * (y - t) + f' t * (-1)) t := (hderiv2 t).mul hsub
    have hsum := (hderiv t).add h1
    have harith : f' t + (f'' t * (y - t) + f' t * (-1)) = f'' t * (y - t) := by ring
    rw [harith] at hsum
    exact hsum
  have hgy : g y = f y := by simp [hg]
  have hgx : g x = f x + f' x * (y - x) := rfl
  have hlip : ∀ t ∈ Set.uIcc x y, ‖deriv g t‖ ≤ β * |y - x| := by
    intro t ht
    rw [(hgderiv t).deriv, Real.norm_eq_abs, abs_mul]
    have hyt : |y - t| ≤ |y - x| := by
      rcases Set.mem_uIcc.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases abs_cases (y - t) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
        rcases abs_cases (y - x) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rw [e1, e2] <;> linarith
    exact mul_le_mul (hbound t) hyt (abs_nonneg _) hβ
  have hmvt := (convex_uIcc x y).norm_image_sub_le_of_norm_deriv_le
    (f := g) (C := β * |y - x|)
    (fun t _ => (hgderiv t).differentiableAt) hlip
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [hgy, hgx] at hmvt
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  have hrw : |f y - (f x + f' x * (y - x))| = |f y - f x - f' x * (y - x)| := by
    congr 1; ring
  rw [hrw] at hmvt
  have habs : |y - x| * |y - x| = (y - x) ^ 2 := by rw [← sq, sq_abs]
  calc |f y - f x - f' x * (y - x)| ≤ β * |y - x| * |y - x| := hmvt
    _ = β * (y - x) ^ 2 := by rw [mul_assoc, habs]
    _ = 2 * β / 2 * (y - x) ^ 2 := by ring

/-- **The value function is `16/(1-γ)³`-smooth — derived, not assumed.**

Assembling everything:

* `abs_d2V_le_eight` bounds the second derivative by `8/(1-γ)³`;
* `smoothAt_two_of_abs_second_deriv_le` turns a second-derivative bound into
  `SmoothAt` at twice the constant, via the mean value theorem.

The factor of two is the MVT-versus-integral loss documented above; the paper's
sharp constant is `8/(1-γ)³`. Since `SmoothAt` is monotone in its constant, this
is a genuine derivation of a valid smoothness constant, and it discharges the
hypothesis that `ascent_step` and `domination_rate_abstract` consume. -/
theorem smoothAt_V_sixteen (dlocal : ℕ → S → ℝ) (m : ℕ) (s : S)
    (hdloc : ∀ (j : ℕ) (s' : S), |dlocal j s'| ≤ 3 / (1 - M.γ))
    (hscore : ∀ θ' s', ∑ a, |PF.dπ θ' s' a| ≤ 1)
    (hr : ∀ s' a, |M.r s' a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (hdlocal : ∀ (t : ℝ) (j : ℕ) (s' : S),
      HasDerivAt (fun u => localTerm M PF.toDiffPolicy u j s') (dlocal j s') t) :
    SmoothAt (fun t => V M (PF.toDiffPolicy.toPolicy t) m s)
      (fun t => dV M PF.toDiffPolicy t m s) (2 * (8 / (1 - M.γ) ^ 3)) := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hβ : (0:ℝ) ≤ 8 / (1 - M.γ) ^ 3 := by positivity
  -- both derivative facts are now theorems, not hypotheses
  have hderiv : ∀ t, HasDerivAt (fun u => V M (PF.toDiffPolicy.toPolicy u) m s)
      (dV M PF.toDiffPolicy t m s) t :=
    fun t => hasDerivAt_V M PF.toDiffPolicy t m s
  have hderiv2 : ∀ t, HasDerivAt (fun u => dV M PF.toDiffPolicy u m s)
      (d2V M PF t dlocal m s) t :=
    fun t => hasDerivAt_dV M PF t dlocal (hdlocal t) m s
  exact smoothAt_two_of_abs_second_deriv_le hβ hderiv hderiv2
    (fun t => abs_d2V_le_eight M PF t dlocal hdloc (hscore t) hr hγ₀ hγ₁ m s)

/-- **`d2V` at the canonical local derivative is the derivative of `dV`.**

Specialising `hasDerivAt_dV` to `dLocalTerm`, whose derivative property is
`hasDerivAt_localTerm` — no hypothesis required. Note `dLocalTerm M PF t` is
evaluated at the *same* `t` as the derivative, which is what makes this work
without assuming anything is constant. -/
theorem hasDerivAt_dV_canonical (m : ℕ) (s : S) :
    HasDerivAt (fun t => dV M PF.toDiffPolicy t m s)
      (d2V M PF θ (dLocalTerm M PF θ) m s) θ :=
  hasDerivAt_dV M PF θ (dLocalTerm M PF θ)
    (fun j s' => hasDerivAt_localTerm M PF θ j s') m s

/-- **The value function is `8/(1-γ)³`-smooth — AKM Lemma E.4's exact constant.**

VERBATIM, Mei, Xiao, Szepesvári & Schuurmans (arXiv:2005.06392) Lemma 7, which
is where the `@[paper "AKM2021" "Lemma E.4"]` tag's citation actually comes from:

> **Lemma 7 (Smoothness).** `V^{π_θ}(ρ)` is `8/(1 − γ)³`-smooth.
>
> *Proof.* See Agarwal et al. (2019, Lemma E.4). Our proof is for completeness.

and the standing assumption Mei's constant depends on, stated just above it:

> According to Assumption 1, `r(s, a) ∈ [0, 1]`, `Q(s, a) ∈ [0, 1/(1 − γ)]`, and
> hence the objective function is still smooth, as was also shown by Agarwal et
> al. (2019)

⚠ **CITATION MISMATCH — the tag points at a lemma number that does not exist in
the version on disk.** `/tmp/akm.txt` is arXiv:1908.00261 **v4** (23 Sep 2020),
whose Appendix E is titled *"Standard Optimization Results"* and contains only
Theorems E.1–E.3 (Beck; Ghadimi–Lan; Shalev-Shwartz–Ben-David). **There is no
Lemma E.4 in v4.** The `8/(1−γ)³` softmax result lives in Appendix D, inside the
proof of **Lemma D.4**, as displayed equation **(53)**:

> ```
> max_{‖u‖₂=1} d²Ṽ(α)/(dα)²|_{α=0} ≤ C₂/(1−γ)² + 2γC₁²/(1−γ)³
>                                   ≤ 6/(1−γ)² + 8γ/(1−γ)³ ≤ 8/(1−γ)³
> ```
> or equivalently for all starting states `s` and hence for all starting state
> distributions `μ`,
> ```
> ‖∇_θ V^{π_θ}(μ) − ∇_θ V^{π_θ'}(μ)‖₂ ≤ β ‖θ − θ'‖₂          (53)
> ```
> where `β = 8/(1−γ)³`.

"Lemma E.4" is Mei's citation of an **earlier arXiv version** of AKM (they cite
it as "Agarwal et al. (2019)"), which renumbered before v4. The constant and the
content are unchanged, so this is a **numbering defect in the tag, not a
statement defect** — but the tag as written cannot be checked against the source
the repo actually has. Either retag as `"AKM2021" "Lemma D.4 (eq. 53)"`, or keep
`E.4` and pin the citation to the AKM v1/v2 numbering that Mei used.

**Two further departures of the Lean statement from both sources.**

1. **Smoothness here is a two-sided Taylor bound, not a Lipschitz gradient.**
   AKM (53) and Mei both state `β`-smoothness as
   `‖∇f(θ) − ∇f(θ')‖ ≤ β‖θ − θ'‖`. `SmoothAt f f' β` is the *remainder* form
   `|f(y) − f(x) − f'(x)(y−x)| ≤ (β/2)|y−x|²`. These are equivalent for `C¹`
   functions up to the standard factor, and `MEI_NOTES.md` records that the
   remainder form is the one the rate machinery consumes; Mathlib has no
   ready-made predicate for either.
2. **Reward normalization differs.** Mei's Assumption 1 is `r(s,a) ∈ [0,1]`;
   `hr` here is `|r(s,a)| ≤ 1`, i.e. `r ∈ [−1,1]`. That is the *wider* range, so
   the bound is claimed over a strictly larger class of MDPs than Mei assume.
   The `8/(1−γ)³` derivation goes through `|Q| ≤ 1/(1−γ)`, which `|r| ≤ 1` also
   gives, so the generalization is sound — but it is a departure from the quote.

Verdict: **MATCHES** on the constant and the mathematical content;
**MISMATCHES on the citation label** (`E.4` is not present in AKM v4; the result
is Lemma D.4 / eq. (53) there).

The final form. Inputs are the paper's standing assumptions **plus an
undischarged bound on the local-term derivative** (`hdloc`, gap **G7**):

* `|dLocalTerm| ≤ 3/(1-γ)`,
* softmax score total variation `≤ 1` (`sum_abs_score_le_one`),
* `|r| ≤ 1`, `0 ≤ γ < 1`.

No `HasDerivAt` hypotheses: `hasDerivAt_V`, `hasDerivAt_localTerm` and
`hasDerivAt_dV_canonical` are all theorems. The constant is the paper's sharp
`8/(1-γ)³`, obtained from `smoothAt_of_abs_second_deriv_le_sharp`.

**Two caveats (see `GAPS.md`).** This theorem has *no callers*: `ascent_step`
and `domination_rate_abstract` take an abstract `SmoothAt f f' β` and are never
instantiated here, so AKM Theorem 4.1 is **not** currently instantiated for any
concrete MDP. And `hdloc` is undischarged (**G7**) while `hscore` is about the
abstract field `PF.dπ`, with no Lean-level link to `sum_abs_score_le_one`
(**G6**) — no concrete softmax `C2Policy` exists. -/
@[paper "AKM2021" "Lemma E.4"]
theorem smoothAt_V_final (m : ℕ) (s : S)
    (hdloc : ∀ (t : ℝ) (j : ℕ) (s' : S), |dLocalTerm M PF t j s'| ≤ 3 / (1 - M.γ))
    (hscore : ∀ θ' s', ∑ a, |PF.dπ θ' s' a| ≤ 1)
    (hr : ∀ s' a, |M.r s' a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) :
    SmoothAt (fun t => V M (PF.toDiffPolicy.toPolicy t) m s)
      (fun t => dV M PF.toDiffPolicy t m s) (8 / (1 - M.γ) ^ 3) := by
  refine smoothAt_of_abs_second_deriv_le_sharp
    (fun t => hasDerivAt_V M PF.toDiffPolicy t m s)
    (fun t => hasDerivAt_dV_canonical M PF t m s) ?_
  intro t
  exact abs_d2V_le_eight M PF t (dLocalTerm M PF t) (hdloc t) (hscore t) hr hγ₀ hγ₁ m s

end PolicyGradient
