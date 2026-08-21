/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.SecondDeriv
import PolicyGradient.AKM

/-!
# Mei, Xiao, Szepesvári & Schuurmans (ICML 2020)

*On the Global Convergence Rates of Softmax Policy Gradient Methods*,
arXiv:2005.06392.

The paper's headline results:

* **Lemma 7** — `V^{π_θ}` is `8/(1-γ)³`-smooth. Already proved as
  `smoothAt_V_final`, with the paper's exact constant.
* **Lemma 8** — the *non-uniform Łojasiewicz* inequality: the gradient norm is
  bounded below by the suboptimality, times a coefficient that degrades as the
  policy's probability on optimal actions shrinks.
* **Theorem 4** — `O(1/t)` convergence, with a constant `c` the paper admits is
  non-explicit.

## The dependency the paper does not advertise

Mei's Lemma 9 (`c > 0`) is proved by citing *"the asymptotic convergence results
of Agarwal et al. [Theorem 5.1]"*. It is **not proved in their paper**. We have
that content (`ascent_converges`, `optimal_of_greedy`), so Theorem 4 is
reachable here in a way it is not from Mei alone.

Following the paper's own framing, `c` enters as an explicit hypothesis: their
theorem statement says "`c` the positive constant from Lemma 9", so carrying it
as a hypothesis is faithful, not a weakening.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [Nonempty A] [Nonempty S]
variable (M : FiniteMDP S A)

/-- **The Łojasiewicz coefficient.**

`min_s π(a*(s)|s)` — the smallest probability the policy assigns to an optimal
action, across states. Mei's Lemma 8 shows the gradient is bounded below by the
suboptimality times this quantity (divided by `√|S|` and the distribution
mismatch coefficient).

The whole difficulty of Theorem 4 lives here: this can be exponentially small,
which is why the `O(1/t)` rate hides an exponential constant. -/
noncomputable def lojaCoeff {S A : Type*} [Fintype S] [Fintype A] [Nonempty S]
    (π : Policy S A) (astar : S → A) : ℝ :=
  ⨅ s : S, (π s) (astar s)

/-- The coefficient is nonnegative. -/
theorem lojaCoeff_nonneg (π : Policy S A) (astar : S → A) :
    0 ≤ lojaCoeff π astar := by
  unfold lojaCoeff
  exact le_ciInf fun s => (π s).nonneg _

/-- The coefficient bounds every state's optimal-action probability from below. -/
theorem lojaCoeff_le (π : Policy S A) (astar : S → A) (s : S) :
    lojaCoeff π astar ≤ (π s) (astar s) :=
  ciInf_le (Finite.bddBelow_range _) s

/-- The deterministic policy that always takes `astar s` at state `s`. -/
noncomputable def detPolicy [DecidableEq A] (astar : S → A) : Policy S A :=
  fun s => ⟨fun a => if a = astar s then 1 else 0,
    fun a => by by_cases h : a = astar s <;> simp [h],
    by simp⟩

@[simp] theorem detPolicy_apply [DecidableEq A] (astar : S → A) (s : S) (a : A) :
    (detPolicy astar s) a = if a = astar s then 1 else 0 := rfl

/-- Under a deterministic policy the advantage gap collapses to a single
advantage: `∑ₐ [a = a*]·A(s,a) = A(s, a*(s))`. -/
theorem advGap_detPolicy [DecidableEq A] (π : Policy S A) (astar : S → A)
    (j : ℕ) (s : S) :
    advGap M (detPolicy astar) π j s = adv M π j s (astar s) := by
  unfold advGap
  simp only [detPolicy_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' univ (astar s) (fun a => adv M π j s a)]
  simp

/-- **The Łojasiewicz mechanism.**

The `π`-weighted advantage at a state is bounded below by the Łojasiewicz
coefficient times the optimal-action advantage, whenever that advantage is
nonnegative.

This is the inequality Mei's Lemma 8 turns into a gradient bound: the gradient
carries a factor `π(a|s)`, so the *policy's own probability* on the optimal
action controls how much signal the gradient has. When that probability is tiny
the gradient is tiny even though the suboptimality is large — which is exactly
why the constant `c` in Theorem 4 can be exponentially small. -/
theorem loja_pointwise [DecidableEq A] (π : Policy S A) (astar : S → A)
    (j : ℕ) (s : S) (hadv : 0 ≤ adv M π j s (astar s)) :
    lojaCoeff π astar * adv M π j s (astar s)
      ≤ (π s) (astar s) * adv M π j s (astar s) :=
  mul_le_mul_of_nonneg_right (lojaCoeff_le π astar s) hadv

/-!
### Suboptimality controlled by the optimal-action advantage

`performance_difference` says the value gap is the visitation-weighted advantage
gap. Against a deterministic optimal policy that gap is the optimal-action
advantage, so the suboptimality is a visitation-weighted sum of those.
-/

/-- **Suboptimality as a weighted sum of optimal-action advantages.**

`V^{π*}_m(s₀) - V^π_m(s₀) = ∑ₖ γᵏ ∑ₛ visit^{π*} k s₀ s · A^π_{m-1-k}(s, a*(s))`

The right-hand side is what the Łojasiewicz argument bounds: if every
optimal-action advantage is small then the policy is near-optimal, and the
Łojasiewicz coefficient says the gradient sees a `π(a*|s)` fraction of it. -/
theorem subopt_eq_weighted_adv [DecidableEq A] (π : Policy S A) (astar : S → A)
    (m : ℕ) (s₀ : S) :
    V M (detPolicy astar) m s₀ - V M π m s₀
      = ∑ k ∈ range m, M.γ ^ k *
          ∑ s, visit M (detPolicy astar) k s₀ s * adv M π (m - 1 - k) s (astar s) := by
  rw [performance_difference M (detPolicy astar) π m s₀]
  unfold pdSum
  refine Finset.sum_congr rfl fun k _ => ?_
  refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
  rw [advGap_detPolicy]

/-- **If every optimal-action advantage is nonpositive, the policy is optimal
against the deterministic comparison.**

The converse direction of the Łojasiewicz argument: no advantage means no
suboptimality. Combined with `optimal_of_greedy` this is how the limit of the
optimization is identified as optimal. -/
theorem le_of_adv_nonpos [DecidableEq A] (π : Policy S A) (astar : S → A)
    (m : ℕ) (s₀ : S) (hγ₀ : 0 ≤ M.γ)
    (hadv : ∀ (j : ℕ) (s : S), adv M π j s (astar s) ≤ 0) :
    V M (detPolicy astar) m s₀ ≤ V M π m s₀ := by
  have heq := subopt_eq_weighted_adv M π astar m s₀
  have hle : ∑ k ∈ range m, M.γ ^ k *
      ∑ s, visit M (detPolicy astar) k s₀ s * adv M π (m - 1 - k) s (astar s) ≤ 0 := by
    refine Finset.sum_nonpos fun k _ => ?_
    refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ₀ k) ?_
    refine Finset.sum_nonpos fun s _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos
      (visit_nonneg M (detPolicy astar) k s₀ s) (hadv (m - 1 - k) s)
  linarith

end PolicyGradient
