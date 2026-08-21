# Infinite-horizon extension — design

## Two numerical facts pinned first (`inf_horizon.py`)

1. **`V_m → V_∞` geometrically at rate exactly γ.** Measured ratio 0.9000 at
   m = 10, 20, 40, 80, 160 with γ = 0.9. So `‖V_m - V_∞‖ ≤ C·γ^m` — the
   summable dominating bound the calculus lemmas need.
2. **The infinite-horizon PG formula holds with the UNNORMALIZED occupancy**
   `d^π(s) = ∑_t γ^t Pr(s_t = s)` — no `1/(1-γ)`. This matches our existing
   `visit` convention, so the finite-horizon vocabulary carries over intact.
   (Sources that normalize `d^π` into a probability distribution must then
   carry the `1/(1-γ)`; ours does not. Getting this backwards makes the
   theorem false, so it is worth stating explicitly.)

## Design decision: `V_∞` as the limit of `V_m`, not as a Banach fixed point

Two options:

  (a) `V_∞ = lim_{m→∞} V_m`     — reuses everything; finite-horizon results
                                   become the approximating sequence.
  (b) `V_∞ = ContractingWith.fixedPoint bellman`  — cleaner algebraically but
                                   disconnects from the existing `V`.

Going with **(a)**. Fact 1 makes it well-defined, and it keeps the repo one
development rather than two. (b) stays available if a fixed-point
characterisation is wanted later; the two agree by uniqueness of the fixed
point, which would itself be a nice lemma to have.

## Where the difficulty actually is

The finite-horizon proofs are ~80% `Finset` manipulation, ~20% calculus. This
flips. Three genuinely new obligations:

1. **Well-definedness.** `V_∞` and `d^π` become `tsum`s; summability must come
   first, from `|r| ≤ R` and `γ < 1` by geometric domination.
2. **∂/∂θ ↔ ∑ interchange.** THE step Sutton et al. (NIPS 1999) perform
   silently. Needs a uniform summable dominating bound on the term derivatives.
3. **`d^π` as an infinite series.** `visit` extends to `∑_t γ^t Pr(s_t = s)`;
   the reindexing lemmas (`step_visit`, `step_pgSum`) need `tsum` analogues.

## What should carry over unchanged

- `Dist`, `FiniteMDP`, `Policy`, `DiffPolicy` — no change
- `step`, `visit` (per-step) — no change; only the *weighted sum* becomes infinite
- `step_visit` (Chapman–Kolmogorov) — already generalized to arbitrary `Policy`
- `adv`, `advGap` — no change
- The proof *skeletons*: induction on horizon becomes a limit argument, but the
  algebraic identities being proved are the same ones.

## Bounded rewards

`FiniteMDP` has no bound on `r` today. `S` and `A` are `Fintype`, so `r` is
automatically bounded — but the bound has to be *produced* (`Finset.exists_le`
over `univ`, or `Finite.exists_max`). Deciding whether to add an explicit
`R : ℝ` field with `hr : ∀ s a, |r s a| ≤ R`, or derive it, is the first
concrete choice. Deriving is cleaner for users; an explicit field is easier to
prove with. Leaning towards deriving, with a lemma `exists_reward_bound`.
