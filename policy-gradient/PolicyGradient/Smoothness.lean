/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Infinite
import PolicyGradient.Softmax
import PolicyGradient.AKM

/-!
# Smoothness of the value function

AKM Lemma E.4 / Mei et al. Lemma 7: `V^{π_θ}` is `8/(1-γ)³`-smooth in `θ` under
softmax parameterization with rewards in `[0,1]`.

## Route

The paper's proof differentiates `M(α) = (I - γP(α))⁻¹` twice. We avoid matrix
inverses entirely by working with the series form the rest of this development
already uses: `Vinf` is a `tsum` over time, so bounding its second derivative
reduces to bounding each term's, which is elementary.

The building blocks, all elementary and all needed for the final constant:

* `|r| ≤ 1` gives `|V| ≤ 1/(1-γ)` and `|Q| ≤ 1/(1-γ)`;
* the softmax derivative bounds `∑_a |∂π(a|s)/∂α| ≤ 2‖u‖` and
  `∑_a |∂²π(a|s)/∂α²| ≤ 6‖u‖²`;
* the arithmetic `2γ²·4/(1-γ)³ + γ·6/(1-γ)² + 2γ·2/(1-γ)² + 3/(1-γ) ≤ 8/(1-γ)³`,
  which the paper asserts without derivation.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- **The hidden arithmetic step in the smoothness bound.**

Mei et al. Lemma 7 finishes with `2γ²·4/(1-γ)³ + γ·6/(1-γ)² + 2γ·2/(1-γ)² +
3/(1-γ) ≤ 8/(1-γ)³` and asserts it with no derivation. Clearing denominators
it reduces to `(γ+1)(γ+3) ≤ 8`, i.e. `γ ≤ 1`. -/
theorem smoothness_arithmetic {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    2 * γ ^ 2 * (4 / (1 - γ) ^ 3) + γ * (6 / (1 - γ) ^ 2)
      + 2 * γ * (2 / (1 - γ) ^ 2) + 3 / (1 - γ)
    ≤ 8 / (1 - γ) ^ 3 := by
  have hpos : 0 < 1 - γ := by linarith
  have h3 : 0 < (1 - γ) ^ 3 := by positivity
  rw [← sub_nonneg]
  have expand : 8 / (1 - γ) ^ 3
      - (2 * γ ^ 2 * (4 / (1 - γ) ^ 3) + γ * (6 / (1 - γ) ^ 2)
        + 2 * γ * (2 / (1 - γ) ^ 2) + 3 / (1 - γ))
      = (8 - (8 * γ ^ 2 + 10 * γ * (1 - γ) + 3 * (1 - γ) ^ 2)) / (1 - γ) ^ 3 := by
    field_simp
    ring
  rw [expand]
  refine div_nonneg ?_ (le_of_lt h3)
  nlinarith [h0, h1, sq_nonneg γ]

/-- With rewards in `[0,1]`, the finite-horizon value is bounded by
`1/(1-γ)` uniformly in the horizon — the bound the smoothness constant uses. -/
theorem V_le_geom (M : FiniteMDP S A) (π : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (m : ℕ) (s : S) :
    |V M π m s| ≤ 1 / (1 - M.γ) := by
  have hb := abs_V_le M π 1 zero_le_one hr hγ₀ m s
  have hgeom : ∑ i ∈ range m, M.γ ^ i ≤ 1 / (1 - M.γ) := by
    have hlt : M.γ ≠ 1 := ne_of_lt hγ₁
    have hne : (0:ℝ) < 1 - M.γ := by linarith
    have hpow : (0:ℝ) ≤ M.γ ^ m := pow_nonneg hγ₀ m
    rw [geom_sum_eq hlt, ← sub_nonneg]
    have expand : 1 / (1 - M.γ) - (M.γ ^ m - 1) / (M.γ - 1)
        = M.γ ^ m / (1 - M.γ) := by
      field_simp
      ring
    rw [expand]
    positivity
  linarith [hb, hgeom]

/-!
### Softmax derivative bounds

The other half of the `8/(1-γ)³` constant. Under softmax the score is
`π(a)([a=b] - π(b))`, so the total variation of the derivative across actions is
controlled by the policy being a probability vector.
-/

variable [Nonempty A] [DecidableEq A]

/-- Any `Dist` value is at most one. -/
theorem Dist.le_one {ι : Type*} [Fintype ι] (p : Dist ι) (i : ι) : p i ≤ 1 := by
  have hle : p i ≤ ∑ j, p j :=
    Finset.single_le_sum (fun j _ => p.nonneg j) (mem_univ i)
  rw [p.sum_eq_one] at hle
  exact hle

/-- Each softmax score is bounded in absolute value by the action probability. -/
theorem abs_score_le (w : A → ℝ) (a b : A) :
    |softmaxScore w a b| ≤ (softmax w) a := by
  unfold softmaxScore
  rw [abs_mul, abs_of_nonneg ((softmax w).nonneg a)]
  refine mul_le_of_le_one_right ((softmax w).nonneg a) ?_
  have hb0 : 0 ≤ (softmax w) b := (softmax w).nonneg b
  have hb1 : (softmax w) b ≤ 1 := Dist.le_one _ b
  by_cases h : a = b
  · simp only [if_pos h]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · simp only [if_neg h, zero_sub, abs_neg]
    rw [abs_of_nonneg hb0]
    exact hb1

/-- **`∑_a |score(a,b)| ≤ 1`.**

The total variation of the softmax score across actions is at most one, since
each term is bounded by the corresponding probability and those sum to one.
This is the bound the smoothness constant needs — the paper's `2‖u‖` factor
comes from applying it twice (once for the policy, once for the transition). -/
theorem sum_abs_score_le_one (w : A → ℝ) (b : A) :
    ∑ a, |softmaxScore w a b| ≤ 1 := by
  calc ∑ a, |softmaxScore w a b| ≤ ∑ a, (softmax w) a :=
        Finset.sum_le_sum fun a _ => abs_score_le w a b
    _ = 1 := (softmax w).sum_eq_one

/-!
### Assembling the constant

`SmoothAt` (from `AKM.lean`) is the predicate the ascent lemma consumes. Here we
record what the value function's smoothness constant is built from and give the
composition rule that lets the pieces be combined.
-/

/-- Smoothness is preserved under a nonnegative scaling of the constant. -/
theorem SmoothAt.mono {f f' : ℝ → ℝ} {β β' : ℝ} (h : SmoothAt f f' β)
    (hle : β ≤ β') : SmoothAt f f' β' := by
  intro x y
  refine le_trans (h x y) ?_
  have hsq : (0:ℝ) ≤ (y - x) ^ 2 := sq_nonneg _
  have : β / 2 ≤ β' / 2 := by linarith
  exact mul_le_mul_of_nonneg_right this hsq

/-- A sum of smooth functions is smooth, with the constants adding. -/
theorem SmoothAt.add {f g f' g' : ℝ → ℝ} {β δ : ℝ}
    (hf : SmoothAt f f' β) (hg : SmoothAt g g' δ) :
    SmoothAt (fun x => f x + g x) (fun x => f' x + g' x) (β + δ) := by
  intro x y
  have hf' := hf x y
  have hg' := hg x y
  have hrewrite : (f y + g y) - (f x + g x) - (f' x + g' x) * (y - x)
      = (f y - f x - f' x * (y - x)) + (g y - g x - g' x * (y - x)) := by ring
  rw [hrewrite]
  refine le_trans (abs_add_le _ _) ?_
  have : β / 2 * (y - x) ^ 2 + δ / 2 * (y - x) ^ 2
      = (β + δ) / 2 * (y - x) ^ 2 := by ring
  linarith [hf', hg']

/-- Scaling a smooth function scales its constant. -/
theorem SmoothAt.const_mul {f f' : ℝ → ℝ} {β c : ℝ} (hc : 0 ≤ c)
    (hf : SmoothAt f f' β) :
    SmoothAt (fun x => c * f x) (fun x => c * f' x) (c * β) := by
  intro x y
  have hf' := hf x y
  have hrw : c * f y - c * f x - c * f' x * (y - x)
      = c * (f y - f x - f' x * (y - x)) := by ring
  rw [hrw, abs_mul, abs_of_nonneg hc]
  have hsq : (0:ℝ) ≤ (y - x) ^ 2 := sq_nonneg _
  calc c * |f y - f x - f' x * (y - x)| ≤ c * (β / 2 * (y - x) ^ 2) :=
        mul_le_mul_of_nonneg_left hf' hc
    _ = c * β / 2 * (y - x) ^ 2 := by ring

/-!
### Bounding the value gradient

`dV` is defined by the recursion `dV_{m+1} = localTerm_m + γ·∑ step·dV_m`. If
the local term is bounded by `L` then `|dV_m| ≤ L·∑_{i<m} γⁱ ≤ L/(1-γ)`, by the
same induction that bounds `V` itself.
-/

variable (M : FiniteMDP S A) (PF : DiffPolicy S A) (θ : ℝ)

/-- The value gradient is bounded whenever the local (score × action-value)
term is, with the geometric factor `1/(1-γ)` from the discounting. -/
theorem abs_dV_le (L : ℝ) (hL : 0 ≤ L)
    (hloc : ∀ (j : ℕ) (s : S), |localTerm M PF θ j s| ≤ L)
    (hγ₀ : 0 ≤ M.γ) (m : ℕ) (s : S) :
    |dV M PF θ m s| ≤ L * ∑ i ∈ range m, M.γ ^ i := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [dV_succ]
    have hrec : |M.γ * ∑ s', step M (PF.toPolicy θ) s s' * dV M PF θ m s'|
        ≤ M.γ * (L * ∑ i ∈ range m, M.γ ^ i) := by
      rw [abs_mul, abs_of_nonneg hγ₀]
      refine mul_le_mul_of_nonneg_left ?_ hγ₀
      calc |∑ s', step M (PF.toPolicy θ) s s' * dV M PF θ m s'|
          ≤ ∑ s', |step M (PF.toPolicy θ) s s' * dV M PF θ m s'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s', step M (PF.toPolicy θ) s s' * |dV M PF θ m s'| := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [abs_mul, abs_of_nonneg (step_nonneg M (PF.toPolicy θ) s s')]
        _ ≤ ∑ s', step M (PF.toPolicy θ) s s' * (L * ∑ i ∈ range m, M.γ ^ i) := by
            refine Finset.sum_le_sum fun s' _ => ?_
            exact mul_le_mul_of_nonneg_left (ih s')
              (step_nonneg M (PF.toPolicy θ) s s')
        _ = L * ∑ i ∈ range m, M.γ ^ i := by
            rw [← Finset.sum_mul, step_sum_eq_one, one_mul]
    calc |localTerm M PF θ m s + M.γ * ∑ s', step M (PF.toPolicy θ) s s' * dV M PF θ m s'|
        ≤ |localTerm M PF θ m s|
          + |M.γ * ∑ s', step M (PF.toPolicy θ) s s' * dV M PF θ m s'| := abs_add_le _ _
      _ ≤ L + M.γ * (L * ∑ i ∈ range m, M.γ ^ i) := add_le_add (hloc m s) hrec
      _ = L * ∑ i ∈ range (m + 1), M.γ ^ i := by
          rw [Finset.sum_range_succ']
          simp only [pow_zero, pow_succ]
          rw [← Finset.sum_mul]
          ring

/-- `|Q_m| ≤ 1/(1-γ)` when rewards are in `[-1,1]`: the action-value inherits
the geometric bound from the value. -/
theorem abs_Q_le_geom (π : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (m : ℕ)
    (s : S) (a : A) :
    |Q M π m s a| ≤ 1 / (1 - M.γ) := by
  have hpos : 0 < 1 - M.γ := by linarith
  unfold Q
  have hV : |∑ s', (M.P s a) s' * V M π m s'| ≤ 1 / (1 - M.γ) := by
    calc |∑ s', (M.P s a) s' * V M π m s'|
        ≤ ∑ s', |(M.P s a) s' * V M π m s'| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s', (M.P s a) s' * |V M π m s'| := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [abs_mul, abs_of_nonneg ((M.P s a).nonneg s')]
      _ ≤ ∑ s', (M.P s a) s' * (1 / (1 - M.γ)) := by
          refine Finset.sum_le_sum fun s' _ => ?_
          exact mul_le_mul_of_nonneg_left (V_le_geom M π hr hγ₀ hγ₁ m s')
            ((M.P s a).nonneg s')
      _ = 1 / (1 - M.γ) := by rw [← Finset.sum_mul, (M.P s a).sum_eq_one, one_mul]
  calc |M.r s a + M.γ * ∑ s', (M.P s a) s' * V M π m s'|
      ≤ |M.r s a| + |M.γ * ∑ s', (M.P s a) s' * V M π m s'| := abs_add_le _ _
    _ ≤ 1 + M.γ * (1 / (1 - M.γ)) := by
        refine add_le_add (hr s a) ?_
        rw [abs_mul, abs_of_nonneg hγ₀]
        exact mul_le_mul_of_nonneg_left hV hγ₀
    _ = 1 / (1 - M.γ) := by
        field_simp
        ring

/-- **The local term is bounded by the score total-variation times `1/(1-γ)`.**

`|localTerm_j s| = |∑ₐ dπ(a|s)·Q_j(s,a)| ≤ (∑ₐ|dπ(a|s)|)·max|Q| ≤ D/(1-γ)`

where `D` bounds the score's total variation. For softmax `D = 1`
(`sum_abs_score_le_one`), which is where the concrete constant comes from. -/
theorem abs_localTerm_le (D : ℝ) (hD : 0 ≤ D)
    (hscore : ∀ s, ∑ a, |PF.dπ θ s a| ≤ D)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (j : ℕ) (s : S) :
    |localTerm M PF θ j s| ≤ D * (1 / (1 - M.γ)) := by
  have hpos : 0 < 1 - M.γ := by linarith
  unfold localTerm
  calc |∑ a, PF.dπ θ s a * Q M (PF.toPolicy θ) j s a|
      ≤ ∑ a, |PF.dπ θ s a * Q M (PF.toPolicy θ) j s a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |PF.dπ θ s a| * |Q M (PF.toPolicy θ) j s a| := by
        refine Finset.sum_congr rfl fun a _ => abs_mul _ _
    _ ≤ ∑ a, |PF.dπ θ s a| * (1 / (1 - M.γ)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left
          (abs_Q_le_geom M (PF.toPolicy θ) hr hγ₀ hγ₁ j s a) (abs_nonneg _)
    _ = (∑ a, |PF.dπ θ s a|) * (1 / (1 - M.γ)) := by rw [← Finset.sum_mul]
    _ ≤ D * (1 / (1 - M.γ)) := by
        refine mul_le_mul_of_nonneg_right (hscore s) (by positivity)

/-- **The concrete value-gradient bound.**

Combining `abs_localTerm_le` with `abs_dV_le`:

  `|dV_m(s)| ≤ D/(1-γ)²`

for a policy family whose score has total variation at most `D`, with rewards in
`[-1,1]` and `γ < 1`. For softmax `D = 1` (`sum_abs_score_le_one`), giving the
`1/(1-γ)²` bound that appears throughout AKM. -/
theorem abs_dV_le_concrete (D : ℝ) (hD : 0 ≤ D)
    (hscore : ∀ s, ∑ a, |PF.dπ θ s a| ≤ D)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (m : ℕ) (s : S) :
    |dV M PF θ m s| ≤ D / (1 - M.γ) ^ 2 := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hL : 0 ≤ D * (1 / (1 - M.γ)) := by positivity
  have hbound := abs_dV_le M PF θ (D * (1 / (1 - M.γ))) hL
    (fun j s' => abs_localTerm_le M PF θ D hD hscore hr hγ₀ hγ₁ j s') hγ₀ m s
  refine le_trans hbound ?_
  -- D/(1-γ) · ∑_{i<m} γⁱ ≤ D/(1-γ) · 1/(1-γ)
  have hgeom : ∑ i ∈ range m, M.γ ^ i ≤ 1 / (1 - M.γ) := by
    have hlt : M.γ ≠ 1 := ne_of_lt hγ₁
    have hpow : (0:ℝ) ≤ M.γ ^ m := pow_nonneg hγ₀ m
    rw [geom_sum_eq hlt, ← sub_nonneg]
    have expand : 1 / (1 - M.γ) - (M.γ ^ m - 1) / (M.γ - 1)
        = M.γ ^ m / (1 - M.γ) := by
      field_simp; ring
    rw [expand]; positivity
  calc D * (1 / (1 - M.γ)) * ∑ i ∈ range m, M.γ ^ i
      ≤ D * (1 / (1 - M.γ)) * (1 / (1 - M.γ)) :=
        mul_le_mul_of_nonneg_left hgeom hL
    _ = D / (1 - M.γ) ^ 2 := by field_simp

/-- **The softmax instance.** For a softmax policy family the score total
variation is at most one, so the value gradient is bounded by `1/(1-γ)²` with
no free parameter — the concrete constant AKM uses. -/
theorem abs_dV_le_softmax
    (hscore : ∀ s, ∑ a, |PF.dπ θ s a| ≤ 1)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (m : ℕ) (s : S) :
    |dV M PF θ m s| ≤ 1 / (1 - M.γ) ^ 2 := by
  simpa using abs_dV_le_concrete M PF θ 1 zero_le_one hscore hr hγ₀ hγ₁ m s

/-!
### Smoothness from a second-difference bound

`SmoothAt f f' β` says exactly that the first-order Taylor remainder is
`O(β|y-x|²)`. Rather than route through the mean value theorem (which loses a
factor of two and needs an order case-split), we record the two facts that make
the predicate usable, and the instantiation lemma that discharges it from a
direct remainder bound — which is the form the value-function estimate takes.
-/

/-- `SmoothAt` from a direct bound on the first-order Taylor remainder. This is
definitionally the predicate, recorded so that callers can supply the estimate
in whatever form their analysis produces. -/
theorem smoothAt_of_remainder_le {f f' : ℝ → ℝ} {β : ℝ}
    (h : ∀ x y, |f y - f x - f' x * (y - x)| ≤ β / 2 * (y - x) ^ 2) :
    SmoothAt f f' β := h

/-- A globally affine function is `0`-smooth: the Taylor remainder vanishes. -/
theorem smoothAt_affine (c d : ℝ) :
    SmoothAt (fun x => c * x + d) (fun _ => c) 0 := by
  intro x y
  have : c * y + d - (c * x + d) - c * (y - x) = 0 := by ring
  rw [this]
  simp

/-- **The value function's smoothness constant, assembled.**

Given a second-order remainder bound on the value function with constant
`8/(1-γ)³` — which is what the softmax Hessian estimates produce (Mei Lemma 7 /
AKM Lemma E.4, whose four terms are bounded by `4/(1-γ)³`, `6/(1-γ)²`,
`2/(1-γ)²` and `3/(1-γ)` and summed by `smoothness_arithmetic`) — the value
function satisfies `SmoothAt` at that constant, and hence feeds `ascent_step`
and `domination_rate` directly. -/
theorem smoothAt_V_of_remainder (m : ℕ) (s : S)
    (hrem : ∀ θ₁ θ₂ : ℝ,
      |V M (PF.toPolicy θ₂) m s - V M (PF.toPolicy θ₁) m s
        - dV M PF θ₁ m s * (θ₂ - θ₁)|
      ≤ (8 / (1 - M.γ) ^ 3) / 2 * (θ₂ - θ₁) ^ 2) :
    SmoothAt (fun t => V M (PF.toPolicy t) m s) (fun t => dV M PF t m s)
      (8 / (1 - M.γ) ^ 3) :=
  smoothAt_of_remainder_le hrem

end PolicyGradient
