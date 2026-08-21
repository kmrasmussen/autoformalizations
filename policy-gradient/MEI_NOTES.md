# Mei, Xiao, Szepesvári & Schuurmans (ICML 2020), arXiv:2005.06392

Read from the arXiv LaTeX source. Recorded because several results are NOT
self-contained and the dependency structure decides what is worth proving.

## The dependency that matters

**Mei's Theorem 4 (the O(1/t) softmax rate) depends on AKM Theorem 5.1.**
Their Lemma 9 — that `c := inf_{s,t≥1} π_θₜ(a*(s)|s) > 0` — is proved by
citing *"the asymptotic convergence results of Agarwal et al. [Theorem 5.1]"*.
It is not proved in their paper.

So: proving AKM Thm 5.1 unlocks Mei Thm 4. The dependency runs in our favour.

Until then, Theorem 4 should be stated with `c` as an explicit hypothesis
(`0 < c` and `∀ s t, c ≤ π_θₜ(a*(s)|s)`). That is faithful — the theorem
itself says "`c` the positive constant from Lemma 9" — and isolates the one
externally-sourced piece.

## Constants (general-MDP track; do not mix with the γ=0 bandit track)

| result | statement |
|---|---|
| Lemma 7 | `V^{π_θ}(ρ)` is `8/(1-γ)³`-smooth. Rewards in `[0,1]`. Attributed to AKM Lemma E.4. |
| Lemma 8 | `‖∂V/∂θ‖₂ ≥ [minₛ π_θ(a*(s)\|s)] / (√S · ‖d_ρ^{π*}/d_μ^{π_θ}‖_∞) · [V*(ρ) − V^{π_θ}(ρ)]` |
| Theorem 4 | `V*(ρ) − V^{π_θₜ}(ρ) ≤ 16S/(c²(1−γ)⁶t) · ‖d_μ^{π*}/μ‖²_∞ · ‖1/μ‖_∞`, with `η = (1−γ)³/8` |

Smoothness there means a **two-sided second-order Taylor bound** w.r.t. `ℓ₂`,
`|f(θ') − f(θ) − ⟨∇f(θ), θ'−θ⟩| ≤ (β/2)‖θ'−θ‖²` — not a Lipschitz-gradient
condition, and Mathlib has no ready-made predicate for it.

## Cheapest high-value target: Lemma 8

Pure algebra: Cauchy–Schwarz (`‖x‖₁ ≤ √S‖x‖₂`), sign manipulations, `min` over
a `Fintype`, and the **performance difference lemma we already have**. No
limits, no derivatives beyond the softmax PG formula. Needs `μ(s) > 0`
(Assumption 2), NOT full support on `ρ`.

## Where the real analysis is

- Lemma 7 (smoothness): Neumann series `(I − γP)^{-1} = ∑ₜ γᵗPᵗ`, differentiating
  a matrix inverse in a parameter, second derivatives of a composite. Heaviest
  item in the unregularized track.
- The `1/t` induction: `δ_{t+1} ≤ δₜ − Kδₜ²` ⟹ `δₜ ≤ 1/(Kt)`. The paper
  **defers this to the bandit case with different constants** and never writes
  it out for the MDP; the bandit base case is "trivially holds up to t ≤ 5",
  unproved. The MDP analogue `δₜ ≤ 1/(1−γ)` is never stated at all.
- Lemma 7's final arithmetic is asserted without derivation. It reduces to
  `(γ+1)(γ+3) ≤ 8` for `γ ∈ [0,1)`. Easy, but hidden.

## Entropy-regularized track — a genuine alternative

Theorem 6 gives a **linear (geometric) rate**, and its constant `c` is
**explicit in closed form**. Crucially its Lemma 16 (`c > 0`) is
**self-contained** — monotone convergence plus a contradiction argument, no
external citation. So the entropy track removes the blocking dependency and
replaces the fiddly `1/t` induction with trivial geometric decay.

The cost: Lemma 14 (entropy smoothness, `(4+8logA)/(1−γ)³`) is called
"a somewhat lengthy calculation", and Lemma 15 (entropy Łojasiewicz, exponent
1/2) is substantially harder than Lemma 8 — it needs the soft greedy policy,
a KL-logit inequality, and Pinsker-type reasoning.

## Do not formalize

**Theorem 8 (decaying τ) is not a theorem.** The paper says outright:
*"While this is promising, the proof cannot be finished as before."* The rate
is only conjectured.

## Other external dependencies
- Lemma 21 (spectrum of `H(π) = diag(π) − ππᵀ`): interlacing cited to Golub
  1973, not proved, and Mathlib lacks rank-one-perturbation interlacing.
  Likely avoidable — the proofs only use `λ_min = 0` and an `ℓ₁` bound.
- Lemma 23 (soft sub-optimality): rests on path consistency, cited to
  Nachum et al. 2017.
