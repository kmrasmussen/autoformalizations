# Policy Gradient in Lean 4 — design notes

## Status: prior art confirmed clear (2026-08-21) — THREE independent searches
Verified at SOURCE level, not just from paper claims:
- mathlib4 @ master 0cd0480 cloned + grepped: `policy gradient`, `MarkovDecision`,
  `Bellman`, `Reward`, `ValueFunction`, occupancy => ALL ZERO. No MDP theory,
  no `MarkovChain` namespace at all.
- IBM/FormalML (CertRL's home) @ 8495ce1 cloned, all 110 .v files grepped => zero.
  NB "policy" in CertRL = policy ITERATION (dynamic programming), not policy gradient.
- Zhang's rl-theory-in-lean @ fec0b5d grepped => zero real hits.

### Two traps that LOOK like prior art but are not
- `BasilRohner/MILib/.../RL/PolicyGradient.lean` = EMPTY STUB, 8 comment lines.
- `sandguine/.../Certificates/PerformanceDifference.v` = states the lemma but the
  main theorem + both corollaries are `Admitted` (assumed, not proved).
Cite neither as prior art; flag both if a reviewer raises them.

### Honest caveats (could-not-check, NOT verified-absent)
- GitHub *code* search was behind a login wall; a private/unindexed repo would
  not have surfaced. Re-run logged in via `gh api /search/code` before claiming novelty.
- Zulip full-text search unavailable; public archive stops Feb 2026 (~6mo unindexed).
- Unverified claim that TorchLean (arXiv:2602.22631) covers MDPs/Bellman — a direct
  fetch did NOT corroborate. Check before any writeup.

### Competitive note
Zhang names policy gradient as HIS OWN future work => possible race. Argues for
getting a sorry-free M1 public rather than polishing.

## Prerequisites also unmechanized ANYWHERE
- performance difference lemma: only artifact on earth is the `Admitted` Coq file
- occupancy measures: zero hits in AFP, FormalML, mathlib

## STATEMENT NUMERICALLY VERIFIED (2026-08-21)
`verify_statement.py` compares central finite differences on V against the PG
formula, 3 states / 2 actions / horizon 4 / gamma .9 / softmax policy.
18/18 (start-state, param-index) combos match. Worst abs error 1.84e-10.
=> the horizon indexing (Q_{m-1-k} pairs with visit(k)) and the d^pi
   normalization are CORRECT. This is the check Lean canNOT do for us:
   Lean proves the theorem follows from the defs; it cannot tell us the defs
   are the right ones. Re-run this whenever a definition changes.

No policy gradient result has been formalized in ANY proof assistant.
- Isabelle: Hölzl (MC/MDP foundations), Schäffeler-Abdulaziz (MDP solvers)
- Coq: CertRL (value/policy iteration, Bellman optimality)
- Lean: Zhang arXiv:2511.03618 (Q-learning + linear TD a.s. convergence)
All value-based. Zhang names policy gradient + actor-critic as FUTURE WORK,
"challenging" because they need time-inhomogeneous Markov chains.

## Target (milestone 1): finite-horizon episodic, finite S/A
Everything is a finite sum => induction on horizon, no analysis.

## The two gaps in the literature this closes
1. **The unrolling hand-wave.** Sutton et al. (NIPS 1999) appendix says
   "after several steps of unrolling (7)" — no induction hypothesis, no
   remainder control, no proof the γ^k remainder vanishes. This IS the theorem.
2. **Illegal matrix inversion.** The popular matrix-form proof inverts (I − Π),
   which is singular (Π stochastic => eigenvalue 1). Discounted case (I − γΠ)
   IS invertible. Formalization separates these cleanly.

## Notational trap
Start-state d^π(s) = Σ_t γ^t Pr(s_t = s) is NOT a probability distribution.
It sums to 1/(1−γ). Sources differ on whether to normalize by (1−γ).
An off-by-(1−γ) makes the theorem FALSE as stated. Our finite-horizon
version keeps the sum explicit and unnormalized to sidestep this.

## Key design decisions
- **Dist as stdSimplex subtype, not PMF.** PMF is ℝ≥0∞-valued: not a vector
  space, no differentiation API. PG differentiates *through* the policy.
  (Same reasoning as lean-vnm-axioms/VNM/Lottery.lean.)
- **Policy NOT a field of FiniteMDP.** Zhang's FiniteMDP bakes in `pi` with
  irreducibility hypotheses attached to the induced chain — structurally
  hostile to varying π. We keep MDP (P, r, γ) and Policy separate.
- **V by backward recursion on steps-remaining**, not trajectory expectation.
  No product measures, no trajectory σ-algebra. Theorem = induction on horizon.

## Statement being proven (milestone 1)
  ∂V_m(s₀)/∂θ = Σ_{k=0}^{m-1} γ^k Σ_s Pr(s_k=s|s₀) Σ_a ∂π(a|s)/∂θ · Q_{m-1-k}(s,a)
The Σ_k Σ_s is exactly what the literature abbreviates as "Σ_s d^π(s)".

## Roadmap
- [x] Prior-art check (3 searches, source-level)
- [x] Numerical verification of the statement
- [ ] M1: finite-horizon PG theorem (this file's target)
- [ ] M1b: performance difference lemma (cheap, telescoping; workhorse of
      the modern literature — Agarwal et al. Lemma 3.2)
- [ ] M2: infinite-horizon discounted (needs dominated convergence for the
      derivative/tsum interchange — the genuinely new analytic content)
- [ ] M3 (later): softmax global convergence (Agarwal Thm 5.1 / Mei Thm 4).
      NB Mei's constant c is non-explicit and provably can be exponentially
      small (Li et al. arXiv:2102.11270) — formalizing makes that vacuity visible.
- [ ] NOT: actor-critic (needs time-inhomogeneous chains, ODE method; out of reach)

## Toolchain
elan (NOT pkgs.lean4) so `lake exe cache get` works — nixpkgs-built Lean isn't
bit-identical to official, so cache misses => hours compiling mathlib.
Lean v4.33.0, mathlib rev db584cd6 (same pin as lean-vnm-axioms = known good).

## Grounding strategy (Kasper, 2026-08-21) — TWO purposes, not one

### 1. Reference implementation as source of truth
A textbook REINFORCE (`reinforce_reference.py`) computes dJ/dtheta by the
score-function estimator from SAMPLED trajectories — no Bellman recursion, no
visitation matrix, just rollouts and log-probs. That is a genuinely independent
route to the same quantity. Cross-checked three ways:
  (A) sampled REINFORCE     — the practitioner's algorithm
  (B) finite differences on true J
  (C) our Lean formula      — visitation-weighted sum
(B)~(C) exactly; (A)~(B) up to Monte-Carlo noise.
NB the earlier scripts (verify_statement / pg_induction) only check our formula
against OUR V — self-consistency. The REINFORCE reference is the real ground
truth because it shares none of our assumptions.

### 2. (DEFERRED — Kasper 2026-08-21: "starting out with just really more mathy things")
Executable-in-Lean PG algorithms are a POSSIBLE LATER DIRECTION, not a current
constraint. We stay on ℝ + `noncomputable`, which is the right setting for the
proofs and gives frictionless access to mathlib's real-analysis API.
Recorded here so the option isn't forgotten: If the Lean model is to
support actual policy-gradient implementations in pure Lean, the definitions
must be COMPUTABLE / EXECUTABLE, not merely provable-about.

Current status: V, Q, visit, step are all `noncomputable` (real arithmetic on ℝ
is not decidable) => can be reasoned about, can NEVER be `#eval`'d or run.

If we ever pursue it, the architecture choice would be:
  - either make the core defs polymorphic in the scalar type (a `LinearOrderedField`
    or similar), instantiating at ℝ for proofs and at ℚ/Float for execution;
  - or maintain a computable ℚ-valued layer with a proved bridge to the ℝ layer.
The payoff would be a REINFORCE in Lean whose correctness is tied to the theorem.
But retrofitting ℝ-based proofs is far cheaper than fighting computability now.

Test that the executable layer is honest: `#eval` the Lean V/visit on the SAME
toy MDP as the Python reference and compare numbers.
