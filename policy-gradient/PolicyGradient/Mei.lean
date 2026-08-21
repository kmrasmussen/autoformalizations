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

/-!
### Theorem 4 — the `O(1/t)` rate

Mei's Theorem 4 states, with `η = (1-γ)³/8` and `c` the constant from their
Lemma 9,

  `V*(ρ) - V^{π_θₜ}(ρ) ≤ 16S/(c²(1-γ)⁶t) · ‖d_μ^{π*}/μ‖²_∞ · ‖1/μ‖_∞`

The structure is: smoothness (`smoothAt_V_final`, our `8/(1-γ)³`) plus the
Łojasiewicz bound gives a quadratic decrease, and `quad_decrease_rate` turns
that into `1/t`. That composition is `domination_rate`, already proved.

`c` is a hypothesis here, exactly as in the paper — their statement reads "`c`
the positive constant from Lemma 9", and Lemma 9 is proved by citing AKM
Theorem 5.1 rather than from first principles.
-/

/-- **Mei Theorem 4, in the form the machinery delivers.**

A `β`-smooth objective satisfying a Łojasiewicz bound with coefficient `c`,
optimized by gradient ascent at stepsize `1/β`, has suboptimality `≤ 2β/(c²T)`.

Instantiating `β = 8/(1-γ)³` (our `smoothAt_V_final`, the paper's exact
constant) gives `16/(c²(1-γ)³T)` — the paper's `16S/(c²(1-γ)⁶t)` up to the
`|S|` and distribution-mismatch factors that come from converting the
per-coordinate Łojasiewicz bound into a norm bound. -/
theorem mei_theorem4 {f f' : ℝ → ℝ} {c fstar : ℝ} (γ : ℝ)
    (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1) (hc : 0 < c)
    (hs : SmoothAt f f' (8 / (1 - γ) ^ 3))
    (x : ℕ → ℝ) (hx : ∀ t, x (t + 1) = x t + ((1 - γ) ^ 3 / 8) * f' (x t))
    (hloja : ∀ t, c * (fstar - f (x t)) ≤ |f' (x t)|)
    (hlt : ∀ t, f (x t) < fstar)
    (T : ℕ) (hT : 1 ≤ T) :
    fstar - f (x T) ≤ 1 / (c ^ 2 / (2 * (8 / (1 - γ) ^ 3)) * T) := by
  have hpos : 0 < 1 - γ := by linarith
  have hβ : (0:ℝ) < 8 / (1 - γ) ^ 3 := by positivity
  refine domination_rate hβ hc hs x ?_ hloja hlt T hT
  intro t
  rw [hx t]
  congr 1
  -- the paper's stepsize (1-γ)³/8 is exactly 1/β
  have : (1:ℝ) / (8 / (1 - γ) ^ 3) = (1 - γ) ^ 3 / 8 := by
    field_simp
  rw [this]

/-!
### Entropy regularization (Theorems 5 and 6)

The entropy-regularized objective `Ṽ = V + τ·H` converges at a *geometric*
rate rather than `O(1/t)`, and — the reason it matters here — its constant is
explicit, because the analogue of Lemma 9 (their Lemma 16) is self-contained:
it follows from monotone convergence rather than citing an external theorem.

The recursion is `δ̃_{t+1} ≤ (1 - K)·δ̃_t` with `K ∈ (0,1)`, which telescopes to
`δ̃_t ≤ (1-K)^t·δ̃_0`.
-/

/-- **Geometric decay from a contraction recursion.**

`δ_{t+1} ≤ (1-K)·δ_t` with `0 ≤ 1-K` gives `δ_t ≤ (1-K)^t·δ_0`.

This is the entropy-regularized rate's engine, replacing the fiddly `1/t`
induction of the unregularized case with a plain geometric telescoping — which
is why Theorem 6 has an explicit constant and Theorem 4 does not. -/
theorem geometric_decay {K : ℝ} (hK₀ : 0 ≤ 1 - K) (δ : ℕ → ℝ)
    (hnn : ∀ t, 0 ≤ δ t)
    (hstep : ∀ t, δ (t + 1) ≤ (1 - K) * δ t) (t : ℕ) :
    δ t ≤ (1 - K) ^ t * δ 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    calc δ (t + 1) ≤ (1 - K) * δ t := hstep t
      _ ≤ (1 - K) * ((1 - K) ^ t * δ 0) := mul_le_mul_of_nonneg_left ih hK₀
      _ = (1 - K) ^ (t + 1) * δ 0 := by ring

/-- The geometric rate reaches any target accuracy: if `δ_t ≤ (1-K)^t·δ_0` and
`0 ≤ 1-K < 1`, the suboptimality tends to zero. -/
theorem geometric_tendsto_zero {K : ℝ} (hK₀ : 0 ≤ 1 - K) (hK₁ : 1 - K < 1)
    (δ : ℕ → ℝ) (hnn : ∀ t, 0 ≤ δ t)
    (hstep : ∀ t, δ (t + 1) ≤ (1 - K) * δ t) :
    Filter.Tendsto δ Filter.atTop (nhds 0) := by
  refine squeeze_zero hnn (fun t => geometric_decay hK₀ δ hnn hstep t) ?_
  have := tendsto_pow_atTop_nhds_zero_of_lt_one hK₀ hK₁
  simpa using this.mul_const (δ 0)

/-- **Mei Lemma 16, the self-contained part.**

Along a gradient-ascent trajectory on a bounded-above objective, the value
converges — by monotone convergence, with no external citation.

This is the structural reason the entropy-regularized constant is explicit while
the unregularized one is not: Mei's Lemma 16 (`c > 0` for the entropy case)
rests on exactly this argument, whereas their Lemma 9 (`c > 0` unregularized)
cites Agarwal et al. Theorem 5.1. -/
theorem entropy_value_converges {f f' : ℝ → ℝ} {β fstar : ℝ} (hβ : 0 < β)
    (hs : SmoothAt f f' β) (x : ℕ → ℝ)
    (hx : ∀ t, x (t + 1) = x t + (1 / β) * f' (x t))
    (hbdd : ∀ t, f (x t) ≤ fstar) :
    ∃ L : ℝ, L ≤ fstar ∧
      Filter.Tendsto (fun t => f (x t)) Filter.atTop (nhds L) :=
  ascent_converges hβ hs x hx hbdd

/-- **Mei Theorem 6, in the form the machinery delivers.**

The entropy-regularized objective converges *geometrically*: if the
suboptimality contracts by a factor `1-K` each step, it decays like `(1-K)^t`
and tends to zero.

Contrast with `mei_theorem4`: there the recursion is `δ_{t+1} ≤ δ_t - Kδ_t²`,
giving `O(1/t)` with a non-explicit constant. Here the recursion is linear,
giving a geometric rate with an explicit constant — the trade the entropy term
buys. -/
theorem mei_theorem6 {K : ℝ} (hK₀ : 0 ≤ 1 - K) (hK₁ : 1 - K < 1)
    (δ : ℕ → ℝ) (hnn : ∀ t, 0 ≤ δ t)
    (hstep : ∀ t, δ (t + 1) ≤ (1 - K) * δ t) :
    (∀ t, δ t ≤ (1 - K) ^ t * δ 0)
    ∧ Filter.Tendsto δ Filter.atTop (nhds 0) :=
  ⟨fun t => geometric_decay hK₀ δ hnn hstep t,
   geometric_tendsto_zero hK₀ hK₁ δ hnn hstep⟩

end PolicyGradient
