# Policy Gradient Theorems in Lean 4

Machine-checked proofs, in Lean 4 + Mathlib, of

* the **policy gradient theorem** — finite horizon and **infinite horizon discounted**,
* the **performance difference lemma**,

for finite-state, finite-action Markov decision processes. No `sorry`; every
theorem rests on only the three standard Lean axioms.

```lean
theorem policy_gradient (M : FiniteMDP S A) (PF : DiffPolicy S A) (θ : ℝ) (m : ℕ) (s₀ : S) :
    HasDerivAt (fun t => V M (PF.toPolicy t) m s₀) (pgSum M PF θ m s₀) θ
```

where

```lean
pgSum M PF θ m s₀ = ∑ k ∈ range m, M.γ ^ k *
                      ∑ s, visit M (PF.toPolicy θ) k s₀ s * localTerm M PF θ (m - 1 - k) s
```

`localTerm j s = ∑ a, ∂π(a|s)/∂θ · Q_j(s,a)`, and `visit k s₀ s = Pr(sₖ = s | s₀)`.
The `∑ₖ γᵏ ∑ₛ visit k` is what the literature abbreviates as `∑ₛ d^π(s)`.

**What the theorem says.** The state visitation `visit` depends on θ, yet no
derivative of it appears on the right-hand side. That cancellation *is* the
theorem. Here it falls out of an induction on the horizon rather than being
assumed.

`lake build` exits 0, there is no `sorry`, and

```
#print axioms policy_gradient
  → [propext, Classical.choice, Quot.sound]
```

i.e. only the three standard axioms Mathlib itself rests on.

## Why this might be new

As far as three independent source-level searches could establish, the policy
gradient theorem had not been formalized in **any** proof assistant. Existing RL
formalization is value-based:

| Work | System | Content |
|---|---|---|
| Hölzl (JAR 2017) | Isabelle | discrete MC/MDP foundations |
| [CertRL](https://arxiv.org/abs/2009.11403) (CPP 2021) | Coq | value & policy **iteration**, Bellman optimality |
| [Schäffeler & Abdulaziz](https://arxiv.org/abs/2206.02169) | Isabelle | verified MDP solvers |
| [Zhang](https://arxiv.org/abs/2511.03618) (Nov 2025) | Lean 4 | Q-learning, linear TD a.s. convergence |

Two artifacts look like prior art and are not: `BasilRohner/MILib`'s
`RL/PolicyGradient.lean` is an empty stub (8 comment lines), and a Coq
`PerformanceDifference.v` states the lemma but leaves it `Admitted`.

Zhang's paper names policy gradient as future work, calling it challenging
because it needs time-inhomogeneous Markov chains — which the finite-horizon
formulation here sidesteps.

*Caveat:* GitHub code search was behind a login wall and the public Zulip
archive stops at Feb 2026, so "no public formalization exists" is well
evidenced; "nobody has ever attempted it" is not something those searches
can establish.

## Two gaps in the standard proof

1. **The unrolling step.** Sutton, McAllester, Singh & Mansour (NIPS 1999)
   dispatch the central step as *"after several steps of unrolling"* — no
   induction hypothesis, no remainder control. Here it is `hasDerivAt_V`, an
   induction on the horizon.
2. **Chapman–Kolmogorov, silently used.** Unfolding `visit (k+1)` gives
   `visit k s₀ s' * step s' s` (step *last*), while the step-weighted sum has
   step *first*. These are equal, but not syntactically — the proof needs
   `step_visit`, which no informal treatment states.

Also worth noting: in the start-state formulation `d^π(s) = ∑ₜ γᵗ Pr(sₜ=s)` is
**not** a probability distribution (it sums to `1/(1-γ)`), and sources differ on
whether to normalize. The finite-horizon form here keeps the sum explicit.

## Design decisions

- **Distributions as a `stdSimplex`-style subtype of `ι → ℝ`, not `PMF`.**
  Mathlib's `PMF` is `ℝ≥0∞`-valued: not a vector space, no differentiation API.
  The policy gradient theorem differentiates *through* the policy.
- **The policy is not a field of `FiniteMDP`.** It must vary while the MDP stays
  fixed, which is exactly what differentiating w.r.t. θ requires.
- **`V` by backward recursion on steps-remaining, not a trajectory expectation.**
  No product measures, no trajectory σ-algebra; the theorem becomes an induction.

## Grounding the definitions

Lean proves the theorem follows from the definitions. It cannot tell you the
definitions are the *right* ones — had `V` been defined wrongly, Lean would
happily verify a theorem about the wrong object.

`independent_check.py` closes that gap: it enumerates **every** trajectory of
the horizon, weights each by its probability, and sums the discounted rewards —
the definition of expected return, transcribed, with no Bellman recursion and no
visitation measure. It agrees with `V` to `5.6e-16`, and runs in CI.

Before the proof was written the statement was also checked against central
finite differences, against a sampled REINFORCE implementation (400k rollouts,
agreeing to `4e-3` — Monte Carlo noise), and for the `m-1-k` index bookkeeping
(`1.1e-16`). Those scripts are not kept: every property they tested is now
*implied* by the Lean proof, whereas the definitional check is not.

## Building

```sh
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

Lean 4.33.0, Mathlib `db584cd6`.

CI builds the project, greps for `sorry`, checks via `#print axioms` that every
theorem rests on only `[propext, Classical.choice, Quot.sound]`, and runs the
definitional check above.

## The infinite-horizon case

`Vinf s₀ = ∑'ₜ γᵗ · E[rₜ]` is defined as a `tsum` and proved well-defined by
geometric domination. The finite-horizon `V m` is exactly its `m`-th partial sum
(`V_eq_sum_stepReward`), so the two developments are one, not two.

| result | content |
|---|---|
| `Vinf_bellman` | `Vinf s₀ = r̄(s₀) + γ ∑_{s'} step s₀ s' · Vinf s'` |
| `dinf`, `dinf_eq` | the unnormalized discounted occupancy and its recursion |
| `hasDerivAt_Vinf` | **the `∂/∂θ ↔ ∑ₜ` interchange** |
| `grad_unfold` | the unrolling, **with the `γⁿ` remainder carried** |
| `remainder_le`, `tendsto_partial_grad` | the remainder vanishes |
| `policy_gradient_infinite` | the theorem |

The two hypotheses that informal proofs leave implicit are packaged as explicit
structures rather than hidden: `TermDerivBound` (a summable, θ-uniform bound on
the term derivatives — what legitimizes the interchange) and `GradSolution` (a
solution of the differentiated Bellman equation). Neither is vacuous: the `t`-th
term's derivative grows like `C·(t+1)·γᵗ`, measured in `pg_inf_stmt.py`.

## Agarwal–Kakade–Lee–Mahajan

Working through [*On the Theory of Policy Gradient Methods*](https://arxiv.org/abs/1908.00261)
(JMLR 22(98), 2021).

**Softmax** (`Softmax.lean`) — `softmax`, `softmax_pos` (every action keeps
strictly positive probability, the property the global-convergence argument
turns on), `softmaxScore`, `softmaxScore_sum_eq_zero` (scores sum to zero, so
the gradient is invariant to shifting all logits at a state).

**Gradient domination** (`GradientDomination.lean`) — AKM Lemma 4.1.
`suboptimality_eq` reads the performance difference lemma as a statement about
suboptimality; `le_of_advGap_nonpos` and `optimal_of_no_advantage` give the
local-to-global step: a purely local condition (no state has an improving
advantage) certifies global optimality. For a general non-convex objective that
implication is false — it holds here because of the MDP structure that
`performance_difference` encodes.

**Natural policy gradient** (`NPG.lean`) — Kakade (NeurIPS 2001); AKM Thm 5.3.
The structural fact: for softmax parameterization the Fisher inverse and the
occupancy weighting *cancel*, so the NPG step is exactly advantage-weighted
logit ascent.

| | |
|---|---|
| `npg_softmax_update` | `π_{t+1}(a\|s) ∝ exp(w + η·A)` |
| `npg_ratio` | `π_{t+1}(a\|s)·Z = π_t(a\|s)·exp(η·A)` — no occupancy measure appears |
| `npg_ratio_mono` | one step moves the probability *ratio* between any two actions toward the higher advantage |
| `softmax_add_const` | softmax quotients out constant logit shifts, so the advantage-form update is well defined |

### The optimization machinery (`AKM.lean`, `Rate.lean`)

| result | content |
|---|---|
| `SmoothAt` | AKM's smoothness: a **two-sided** second-order Taylor bound, not a Lipschitz-gradient condition (Mathlib has no such predicate) |
| `ascent_step` | one step with `η = 1/β` gains at least `\|f'\|²/(2β)` |
| `quad_decrease_of_domination` | smoothness + gradient domination ⟹ quadratic decrease of the suboptimality |
| `quad_decrease_rate` | `δ_{t+1} ≤ δ_t − Kδ_t²` ⟹ `δ_t ≤ 1/(Kt)` — the induction **no paper writes out** |
| `domination_rate_abstract` | the three composed: suboptimality `≤ 2β/(c²T)` after `T` steps |
| `approx_domination_floor` | Section 6: with transfer error `ε`, the decrease is toward an irreducible `ε/c` floor |
| `ascent_monotone`, `ascent_converges` | Theorem 5.1's asymptotic content — monotone + bounded ⟹ convergent |
| `optimal_of_greedy` | greedy ⟹ globally optimal, the conclusion Thm 5.1 reaches |

`domination_rate_abstract` is AKM Theorem 4.1 and Corollary 5.1 in skeleton form: their
constants (`64γ|S||A|/((1−γ)⁶ε²)`, `320|S|²|A|²/((1−γ)⁶ε²)`) are instantiations,
with `β` from the value function's smoothness and `c` from the
distribution-mismatch coefficient.

## Mei et al. — convergence rates (`Mei.lean`)

[*On the Global Convergence Rates of Softmax Policy Gradient Methods*](https://arxiv.org/abs/2005.06392)
(ICML 2020).

| result | content |
|---|---|
| `lojaCoeff` | `minₛ π(a*(s)\|s)` — the non-uniform Łojasiewicz coefficient |
| `loja_pointwise` | the coefficient bounds the weighted advantage below |
| `subopt_eq_weighted_adv` | suboptimality as a visitation-weighted sum of optimal-action advantages |
| **`smooth_loja_rate`** | **the `O(1/T)` rate**, with the paper's exact stepsize `(1−γ)³/8` and smoothness `8/(1−γ)³` |
| `geometric_decay` | `δ_{t+1} ≤ (1−K)δ_t ⟹ δ_t ≤ (1−K)ᵗδ_0` |
| **`geometric_rate`** | **the entropy-regularized geometric rate** |

**Why the constants differ.** Theorem 4's recursion is `δ_{t+1} ≤ δ_t − Kδ_t²`,
giving `O(1/t)` with a constant `c` the paper admits is non-explicit — and which
Li–Wei–Chi–Chen later showed can be exponentially small. Theorem 6's recursion is
linear, giving a geometric rate with an explicit constant. That is the trade the
entropy term buys.

**A dependency the paper does not advertise.** Mei's Lemma 9 (`c > 0`) is proved
by citing *"the asymptotic convergence results of Agarwal et al. [Theorem 5.1]"* —
it is not proved in their paper. We have that content (`ascent_converges`,
`optimal_of_greedy`), so `c` enters here as an explicit hypothesis exactly as
their theorem statement does ("`c` the positive constant from Lemma 9").

## Status / next

- [x] Finite-horizon episodic, finite S/A
- [x] Performance difference lemma (also unmechanized anywhere)
- [x] Infinite-horizon discounted, including the ∂/∂θ ↔ ∑ interchange
- [x] Softmax parameterization and its score
- [x] Gradient domination / local-to-global optimality (AKM Lemma 4.1)
- [x] NPG closed form and monotonicity (AKM Thm 5.3 machinery)
- [ ] The AKM Thm 5.1 / 5.3 rates themselves
- [ ] Mei et al. smoothness + non-uniform Łojasiewicz → the O(1/t) rate

Actor-critic is out of reach for now: it needs time-inhomogeneous chains and
the ODE method, neither in Mathlib.
