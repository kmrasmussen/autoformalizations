# Policy Gradient Theorem in Lean 4

A machine-checked proof of the **policy gradient theorem** for finite-horizon,
finite-state, finite-action Markov decision processes, in Lean 4 + Mathlib.

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

## Status / next

- [x] Finite-horizon episodic, finite S/A
- [ ] Performance difference lemma (also unmechanized anywhere)
- [ ] Infinite-horizon discounted — needs dominated convergence for the
      ∂/∂θ ↔ ∑ interchange; Mathlib's `ParametricIntegral` is the tool
- [ ] Softmax global convergence (Agarwal et al. Thm 5.1 / Mei et al. Thm 4)

Actor-critic is out of reach for now: it needs time-inhomogeneous chains and
the ODE method, neither in Mathlib.
