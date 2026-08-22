/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.GradientDomination
import PolicyGradient.Rate

/-!
# Agarwal–Kakade–Lee–Mahajan: the ascent machinery

*On the Theory of Policy Gradient Methods: Optimality, Approximation, and
Distribution Shift*, JMLR 22(98), 2021.

This file develops the optimization-side machinery of the paper — the smoothness
predicate the ascent lemma needs, and the ascent lemma itself — in the form the
convergence theorems consume.

## Smoothness

AKM (and Mei et al.) use a **two-sided second-order Taylor bound**, not a
Lipschitz-gradient condition:

  `|f(θ') - f(θ) - ⟨∇f(θ), θ' - θ⟩| ≤ (β/2)‖θ' - θ‖²`

Mathlib has no predicate in this form, so we define it.
-/

open Finset

namespace PolicyGradient

/-- `β`-smoothness in the sense used by AKM: a two-sided second-order Taylor
bound. Stated for a one-dimensional parameter, which is what the `HasDerivAt`
development uses. -/
def SmoothAt (f : ℝ → ℝ) (f' : ℝ → ℝ) (β : ℝ) : Prop :=
  ∀ x y : ℝ, |f y - f x - f' x * (y - x)| ≤ β / 2 * (y - x) ^ 2

/-- **The ascent lemma.** One gradient-ascent step with stepsize `η = 1/β` on a
`β`-smooth function increases the value by at least `(1/(2β))·|f'|²`.

This is AKM's Lemma (and Mei et al.'s Lemma 17): the engine that converts a
lower bound on the gradient into per-step progress. -/
theorem ascent_step {f f' : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hs : SmoothAt f f' β)
    (x : ℝ) :
    f x + 1 / (2 * β) * (f' x) ^ 2 ≤ f (x + (1 / β) * f' x) := by
  set y := x + (1 / β) * f' x with hy
  have hdiff : y - x = (1 / β) * f' x := by rw [hy]; ring
  have h := hs x y
  rw [abs_le] at h
  have hlow := h.1
  rw [hdiff] at hlow
  have hβ' : β ≠ 0 := ne_of_gt hβ
  have expand : f' x * ((1 / β) * f' x) - β / 2 * ((1 / β) * f' x) ^ 2
      = 1 / (2 * β) * (f' x) ^ 2 := by
    field_simp
    ring
  nlinarith [hlow, expand]

/-!
### The convergence skeleton

Gradient domination gives `|f'(x)| ≥ c·(f* - f(x))`. The ascent lemma turns
that into a quadratic decrease of the suboptimality, and `quad_decrease_rate`
turns *that* into `O(1/T)`. This composition is the shape of AKM Theorem 4.1
and Corollary 5.1, and of Mei et al. Theorem 4.
-/

/-- **Gradient domination gives a quadratic decrease of the suboptimality.**

If `f` is `β`-smooth and satisfies the gradient-domination bound
`c·(fstar - f x) ≤ |f' x|`, then one ascent step decreases the suboptimality
`δ = fstar - f` by at least `(c²/(2β))·δ²`. -/
theorem quad_decrease_of_domination {f f' : ℝ → ℝ} {β c fstar : ℝ}
    (hβ : 0 < β) (hc : 0 ≤ c) (hs : SmoothAt f f' β) (x : ℝ)
    (hdom : c * (fstar - f x) ≤ |f' x|) (hle : f x ≤ fstar) :
    fstar - f (x + (1 / β) * f' x)
      ≤ (fstar - f x) - c ^ 2 / (2 * β) * (fstar - f x) ^ 2 := by
  have hasc := ascent_step hβ hs x
  -- |f' x|² ≥ c²(fstar - f x)²
  have hsq : c ^ 2 * (fstar - f x) ^ 2 ≤ (f' x) ^ 2 := by
    have h1 : 0 ≤ fstar - f x := by linarith
    have h2 : 0 ≤ c * (fstar - f x) := mul_nonneg hc h1
    calc c ^ 2 * (fstar - f x) ^ 2 = (c * (fstar - f x)) ^ 2 := by ring
      _ ≤ |f' x| ^ 2 := by nlinarith [hdom, h2]
      _ = (f' x) ^ 2 := sq_abs _
  have hpos : 0 < 2 * β := by linarith
  have : c ^ 2 / (2 * β) * (fstar - f x) ^ 2 ≤ 1 / (2 * β) * (f' x) ^ 2 := by
    have hinv : 0 < 1 / (2 * β) := by positivity
    have heq1 : c ^ 2 / (2 * β) * (fstar - f x) ^ 2
        = 1 / (2 * β) * (c ^ 2 * (fstar - f x) ^ 2) := by
      field_simp
    rw [heq1]
    exact mul_le_mul_of_nonneg_left hsq (le_of_lt hinv)
  linarith [hasc, this]

/-- **The full skeleton: gradient domination ⟹ `O(1/T)`.**

A `β`-smooth objective satisfying gradient domination with constant `c`,
optimized by gradient ascent with stepsize `1/β`, has suboptimality at most
`2β/(c²·T)` after `T` steps.

This is the shape of AKM Theorem 4.1 and Corollary 5.1. The constants there are
instantiations: `β` from the smoothness of the value function and `c` from the
distribution-mismatch coefficient. -/
theorem domination_rate_abstract {f f' : ℝ → ℝ} {β c fstar : ℝ}
    (hβ : 0 < β) (hc : 0 < c) (hs : SmoothAt f f' β)
    (x : ℕ → ℝ) (hx : ∀ t, x (t + 1) = x t + (1 / β) * f' (x t))
    (hdom : ∀ t, c * (fstar - f (x t)) ≤ |f' (x t)|)
    (hlt : ∀ t, f (x t) < fstar)
    (T : ℕ) (hT : 1 ≤ T) :
    fstar - f (x T) ≤ 1 / (c ^ 2 / (2 * β) * T) := by
  set δ : ℕ → ℝ := fun t => fstar - f (x t) with hδ
  have hpos : ∀ t, 0 < δ t := fun t => by simp only [hδ]; linarith [hlt t]
  have hstep : ∀ t, δ (t + 1) ≤ δ t - (c ^ 2 / (2 * β)) * (δ t) ^ 2 := by
    intro t
    simp only [hδ]
    rw [hx t]
    exact quad_decrease_of_domination hβ (le_of_lt hc) hs (x t) (hdom t)
      (le_of_lt (hlt t))
  have hK : 0 < c ^ 2 / (2 * β) := by positivity
  exact quad_decrease_rate hK δ hpos hstep T hT

/-!
### Approximation (AKM Section 6)

When the policy class cannot represent the optimum, the guarantee degrades by a
*transfer error* — how badly the best-in-class approximation does under the
comparison policy's state distribution — amplified by a *concentrability*
coefficient measuring the distribution shift between the two.

The structure of the paper's bound is: `suboptimality ≤ optimization error +
transfer error × concentrability`. The first term goes to zero with more
iterations; the other two are irreducible properties of the function class and
the MDP.

**Only the first term is modelled below.** Transfer error and concentrability
are undefined here (**G4**), so the results in this section are abstract
optimization statements, not AKM's Section 6.
-/

/-- **The approximate-domination rate.**

If gradient domination holds only up to an additive slack `ε` — the transfer
error — then gradient ascent drives the suboptimality to `ε/c` plus an `O(1/T)`
optimization term, rather than to zero.

This is the *shape* of AKM's Section 6 results. **Neither the transfer error
nor the concentrability coefficient is defined anywhere in this repo** (gap
**G4**): `ε` is an abstract slack, and nothing here connects it to function
approximation or to a distribution mismatch. In the paper the corresponding
floor does not shrink with more iterations. -/
theorem approx_domination_floor {f f' : ℝ → ℝ} {β c fstar ε : ℝ}
    (hβ : 0 < β) (hc : 0 < c) (hε : 0 ≤ ε) (hs : SmoothAt f f' β) (x : ℝ)
    (hdom : c * (fstar - f x) - ε ≤ |f' x|) (hle : f x ≤ fstar)
    (hfloor : ε / c ≤ fstar - f x) :
    fstar - f (x + (1 / β) * f' x)
      ≤ (fstar - f x)
        - (c ^ 2 / (2 * β)) * ((fstar - f x) - ε / c) ^ 2 := by
  have hasc := ascent_step hβ hs x
  have hδ : 0 ≤ fstar - f x := by linarith
  -- the domination slack still gives a usable lower bound on |f'|
  have hlow : c * ((fstar - f x) - ε / c) ≤ |f' x| := by
    have : c * ((fstar - f x) - ε / c) = c * (fstar - f x) - ε := by
      field_simp
    rw [this]; exact hdom
  have hnn : 0 ≤ (fstar - f x) - ε / c := by linarith
  have hsq : c ^ 2 * ((fstar - f x) - ε / c) ^ 2 ≤ (f' x) ^ 2 := by
    have h2 : 0 ≤ c * ((fstar - f x) - ε / c) := mul_nonneg (le_of_lt hc) hnn
    calc c ^ 2 * ((fstar - f x) - ε / c) ^ 2
        = (c * ((fstar - f x) - ε / c)) ^ 2 := by ring
      _ ≤ |f' x| ^ 2 := by nlinarith [hlow, h2]
      _ = (f' x) ^ 2 := sq_abs _
  have hpos : (0:ℝ) < 2 * β := by linarith
  have hstep : c ^ 2 / (2 * β) * ((fstar - f x) - ε / c) ^ 2
      ≤ 1 / (2 * β) * (f' x) ^ 2 := by
    have hinv : 0 < 1 / (2 * β) := by positivity
    have heq : c ^ 2 / (2 * β) * ((fstar - f x) - ε / c) ^ 2
        = 1 / (2 * β) * (c ^ 2 * ((fstar - f x) - ε / c) ^ 2) := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hsq (le_of_lt hinv)
  linarith [hasc, hstep]

/-!
### Asymptotic convergence (AKM Theorem 5.1)

Theorem 5.1 is asymptotic and carries no rate: softmax policy gradient with a
small enough stepsize drives `V^{(t)}(s) → V*(s)`. The mechanism is that the
suboptimality is monotonically non-increasing and bounded, hence convergent,
and the limit must satisfy the greedy condition — which `optimal_of_greedy`
then converts into optimality.

This is the theorem Mei et al. cite for their `c > 0`, and it is the reason
their `O(1/t)` rate is not self-contained.
-/

/-- A gradient-ascent trajectory on a smooth function has monotonically
non-decreasing value. -/
theorem ascent_monotone {f f' : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) (hs : SmoothAt f f' β)
    (x : ℕ → ℝ) (hx : ∀ t, x (t + 1) = x t + (1 / β) * f' (x t)) (t : ℕ) :
    f (x t) ≤ f (x (t + 1)) := by
  have h := ascent_step hβ hs (x t)
  rw [← hx t] at h
  have hgain : 0 ≤ 1 / (2 * β) * (f' (x t)) ^ 2 := by positivity
  linarith [h, hgain]

/-- The suboptimality along a gradient-ascent trajectory is non-increasing. -/
theorem subopt_antitone {f f' : ℝ → ℝ} {β fstar : ℝ} (hβ : 0 < β)
    (hs : SmoothAt f f' β) (x : ℕ → ℝ)
    (hx : ∀ t, x (t + 1) = x t + (1 / β) * f' (x t)) (t : ℕ) :
    fstar - f (x (t + 1)) ≤ fstar - f (x t) := by
  have := ascent_monotone hβ hs x hx t
  linarith

/-- **The value sequence converges.** Bounded above by `fstar` and monotone, the
value along a gradient-ascent trajectory converges.

This is the analytic content of AKM Theorem 5.1: the limit exists. Identifying
the limit as the optimum is then `optimal_of_greedy`, once one knows the limit
policy is greedy. -/
theorem ascent_converges {f f' : ℝ → ℝ} {β fstar : ℝ} (hβ : 0 < β)
    (hs : SmoothAt f f' β) (x : ℕ → ℝ)
    (hx : ∀ t, x (t + 1) = x t + (1 / β) * f' (x t))
    (hbdd : ∀ t, f (x t) ≤ fstar) :
    ∃ L : ℝ, L ≤ fstar ∧
      Filter.Tendsto (fun t => f (x t)) Filter.atTop (nhds L) := by
  have hmono : Monotone (fun t => f (x t)) :=
    monotone_nat_of_le_succ (fun t => ascent_monotone hβ hs x hx t)
  have hbdd' : BddAbove (Set.range fun t => f (x t)) :=
    ⟨fstar, fun y hy => by obtain ⟨t, rfl⟩ := hy; exact hbdd t⟩
  refine ⟨⨆ t, f (x t), ?_, tendsto_atTop_ciSup hmono hbdd'⟩
  exact ciSup_le hbdd

end PolicyGradient
