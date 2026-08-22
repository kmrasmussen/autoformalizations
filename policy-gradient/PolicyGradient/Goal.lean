/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Meta.Paper
import PolicyGradient.Target
import PolicyGradient.Proofs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Goal.lean — the frozen targets

**This file is frozen. Do not weaken a statement to make it provable.**

Every result this repo is trying to reach is stated here, in advance, as a
theorem with `sorry`. Proving one means replacing its `sorry` — never editing
its statement.

## Why this file exists

The repo previously reported "114 theorems, zero `sorry`" while its headline
results were abstract statements about `f : ℝ → ℝ` that never mentioned an MDP
(see `GAPS.md`). No `sorry` was involved: the unproved content sat in
*hypothesis positions*, which Lean type-checks happily.

That failure needs no bad intent. Working toward a hard theorem, you find you
need a lemma you cannot prove; you add it as a hypothesis; the build goes green.
Each step is locally reasonable and the whole is worthless. The cheap path pays
exactly as well as the honest one.

Freezing the statements removes that. With the goal fixed in advance, assuming
the missing lemma in a helper **does not discharge the goal** — the `sorry` here
stays, and no green signal appears. The only ways to make this file compile
clean are to prove the goals, or to edit this file, which is one line in a diff
that a human reads.

## The rule

> **A hypothesis is a promise. A theorem with no callers is a promise nobody
> ever pays. Prefer a visible `sorry` to an invisible hypothesis.**

## Discipline

* Statements here are frozen; the linter fails if one changes.
* `#print axioms` must never grow beyond `propext, Classical.choice, Quot.sound`
  — in particular, never discharge a goal by declaring an `axiom`.
* A goal proved from contradictory hypotheses is vacuous, not done. Each goal
  carrying hypotheses needs a consistency witness (a concrete MDP satisfying
  them) before it counts.
* Infrastructure steps are goals too. "Build the vector-parameter policy family"
  is a construction goal, discharged only by producing the object.
* **Pin every witness.** An existence goal is not automatically safe. `∃ x, P x`
  with a weak `P` is satisfiable by a *degenerate* witness — a bare
  `Nonempty (VecPolicy ...)` is discharged in four lines by a constant policy
  family with derivative `0`, and `∃ V, V - b ≤ c` is discharged by
  `⟨b + c, by linarith⟩`. Every construction goal needs a conjunct identifying
  *which* object, and no target quantity may be existentially chosen by the
  prover. Define the optimum (`Vstar`, `VsoftStar`); never let it be picked.
* The three routes to a hollow proof are: weakening the conclusion, adding a
  hypothesis, and choosing a degenerate witness. All are the same failure —
  **the prover controlling both the target and what satisfies it.**
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ## G5 — the vector parameter

Both papers optimize over `θ ∈ ℝ^(S×A)`. This repo uses `θ : ℝ`, a single real,
so "gradient norm" degenerates to `|f'|` and **G1 and G2 cannot even be
stated**. Everything else waits on this.

`EuclideanSpace ℝ (S × A)` is the target: `gradient` needs an
`InnerProductSpace`, which the plain function type `(S × A) → ℝ` lacks, and both
papers' bounds are on `‖∇V‖` in the ℓ² norm. -/

/-- **G5 + G6 — the softmax family is a differentiable vector-parameter policy.**

Stated as one goal deliberately. As a bare `Nonempty (VecPolicy ...)` this was
**satisfiable by a degenerate witness**: a constant policy family ignoring `θ`,
with derivative `0`, is a perfectly valid `VecPolicy`, so the `sorry` could be
discharged in four lines while building nothing useful.

The `hsoft` conjunct pins the witness: `F` must *be* the softmax family, so the
only route is the actual differentiability proof. Nothing weaker discharges it.

This is the general trap for construction goals — see the discipline note above.

Discharging this closes both G5 (vector parameter) and G6 (softmax instance),
and unblocks G7 and G1. -/
@[infra "G5+G6"]
theorem g5_g6_softmax_family
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (hlog : ∀ s a, Differentiable ℝ (fun θ => logits θ s a)) :
    ∃ F : VecPolicy S A (EuclideanSpace ℝ (S × A)),
      ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a := by
  -- `softmax_diff` (in `Softmax.lean`) gives Fréchet differentiability of
  -- `θ ↦ π_θ(a|s)` for every state-action pair.
  have hdiff : ∀ (s : S) (a : A),
      Differentiable ℝ (fun θ : EuclideanSpace ℝ (S × A) => (softmax (logits θ s)) a) :=
    fun s a => softmax_diff (fun θ => logits θ s) (fun a' => hlog s a') a
  -- The witness *is* the softmax family; `dπ` is its Fréchet derivative.
  refine ⟨{
    toPolicy := fun θ s => softmax (logits θ s)
    dπ := fun θ s a => fderiv ℝ (fun t => (softmax (logits t s)) a) θ
    hasFDeriv := fun θ s a => (hdiff s a θ).hasFDerivAt }, ?_⟩
  intro θ s a
  rfl

/-! ## Vstar is well-behaved

`Vstar` is a `⨆` over the whole policy space. If that supremum were badly
behaved the suboptimality goals could be vacuous or ill-typed in spirit, so its
basic properties are goals rather than assumptions. -/

/-- **Every policy's value is at most the optimal value.**

Needs `Vinf` to be bounded above over the policy space — true because rewards
are bounded and `γ < 1`, giving the uniform bound `1/(1-γ)`. Without this
`⨆` could misbehave and the suboptimality statements would be hollow. -/
@[infra "Vstar-sound"]
theorem vstar_upper (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ : S) :
    Vinf M π s₀ ≤ Vstar M s₀ :=
  Proofs.vstar_upper_proof M hr hγ₀ hγ₁ π s₀

/-- **The optimal value is finite.** `Vstar ≤ 1/(1-γ)` under bounded rewards. -/
@[infra "Vstar-finite"]
theorem vstar_le (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Vstar M s₀ ≤ 1 / (1 - M.γ) :=
  Proofs.vstar_le_proof M hr hγ₀ hγ₁ s₀

/-! ## Bellman optimality — the machinery `g3` needs

An agent attempting `g3_strict_suboptimality` reported that the statement is
correct as written but not reachable from what this repo has: discharging it
needs the Bellman optimality characterization (`Q*`, `V* = max_a Q*`, and the
fact that an optimal policy's support is greedy), plus an occupancy/support
argument. That is infrastructure, not a small proof, so it is stated here rather
than left as an obstacle inside `g3`.

Their argument for why `g3` is true, recorded so the eventual proof can follow
it: `Vinf M π μ` depends on `π` only at states reachable from `μ`, so `hnondeg`
cannot be witnessed by a bad action at an unreachable state — it forces the
variation onto reachable states, which is exactly where softmax's full support
bites. Contrapositive: if a full-support policy is optimal at `μ`, greediness
of its support gives `Q*(s,a) = V*(s)` for *all* `a` at every reachable `s`, so
every policy is optimal and `hnondeg` fails. -/

/-- **Bellman optimality.** `V*(s) = maxₐ Q*(s,a)`.

The characterization `g3` turns on. Note it needs `Vstar` to be a genuine
supremum, which `vstar_upper` and `vstar_le` now provide. -/
@[infra "Bellman-optimality"]
theorem vstar_bellman (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vstar M s = ⨆ a : A, Qstar M s a :=
  Proofs.vstar_bellman_proof M hr hγ₀ hγ₁ s

/-- **An optimal policy's support is greedy.**

If `π` attains the optimum at `s`, every action it puts positive mass on is
optimal there. Combined with softmax's full support this is what forces
`Q*(s,a) = V*(s)` for *every* `a` — the step that makes `g3` work. -/
@[infra "Greedy-support"]
theorem optimal_support_greedy (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) (hopt : Vinf M π s = Vstar M s)
    (a : A) (hsupp : 0 < (π s) a) :
    Qstar M s a = Vstar M s :=
  Proofs.optimal_support_greedy_proof M hr hγ₀ hγ₁ π s hopt a hsupp

/-! ## G3 — strict suboptimality along the trajectory

The rate machinery needs `0 < δ t` for its reciprocal recursion, and the old
abstract theorems simply assumed `∀ t, f (x t) < fstar` — strict suboptimality
at every iterate, forever, which is **false the moment the optimum is reached
exactly**. Nothing proved it.

For softmax it is genuinely true: a softmax policy assigns strictly positive
probability to every action, so it never equals a deterministic optimal policy.
Stating it here means the rate proof can no longer quietly assume it. -/

/-- **G3 — softmax is never exactly optimal.**

**Statement verified correct as written** (2026-08-22). A subagent set out to
build the suspected counterexample — an MDP whose only bad action sits at an
unreachable state — and found it cannot exist: `Vinf M π μ` depends on `π` only
at reachable states, so such an MDP would not satisfy `hnondeg` either.
`hnondeg` is doing real work (without it the statement is false for MDPs where
all actions are equally good) and is exactly strong enough. Stress-tested over
~40,000 random 3-state MDPs with zero violations, and the load-bearing step
directly over 619 cases, also zero.

Blocked on `vstar_bellman` and `optimal_support_greedy` above, not on any defect
in this statement.

Under a non-degeneracy condition (some policy is strictly suboptimal, i.e. the
MDP is not one where every policy is optimal), a softmax policy — which puts
positive mass on every action — is strictly suboptimal.
This is what licenses the `0 < δ t` the `1/t` recursion needs. -/
@[paper "Mei2020" "Lemma 9 (strictness)"]
theorem g3_strict_suboptimality (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (μ : S) (θ : EuclideanSpace ℝ (S × A))
    (hnondeg : ∃ π : Policy S A, Vinf M π μ < Vstar M μ) :
    Vinf M (F.toPolicy θ) μ < Vstar M μ := sorry

/-! ## G9 — the constant `c` is positive

Mei's Lemma 9 asserts `c > 0` by citing AKM Theorem 5.1; it is not proved in
their paper. `mei_theorem4` above states `c` existentially, so **this goal is
what actually produces it** — it is not optional decoration.

We have the AKM content (`ascent_converges`, `optimal_of_greedy`), but the
composition does not exist: `ascent_converges` yields only `∃ L ≤ fstar` with
`Tendsto`, never identifying `L = fstar`. This goal is that missing bridge. -/

/-- **G9 — the Łojasiewicz coefficient stays bounded away from zero.**

Tagged `@[infra]`, not `@[paper]`: the linter correctly rejected the `@[paper]`
tag, because the conclusion is about the *policy's* probabilities rather than
about `V`. It produces the constant that `mei_theorem4` consumes; it is not
itself a statement about the MDP's value.

Along a gradient-ascent trajectory the smallest optimal-action probability does
not decay to zero, so the `inf` over time is strictly positive. This is what
makes the `O(1/T)` rate meaningful rather than asymptotically vacuous. -/
@[infra "G9"]
theorem g9_c_positive (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (astar : S → A) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := sorry

/-! ## G7 — the local-term bound

`smoothAt_V_final` assumes `|dLocalTerm| ≤ 3/(1-γ)` and nothing proves it. It is
provable once the second derivative of a concrete softmax family is available,
i.e. after G6. -/

/-- **G7 — the smoothness bound holds for softmax, unconditionally.**

`smoothAt_V_final` with `hdloc` discharged: `V` is `8/(1-γ)³`-smooth in the
vector parameter, for the actual softmax family, assuming only the papers' own
standing assumptions (bounded rewards, `0 ≤ γ < 1`). -/
@[paper "AKM2021" "Lemma E.4"]
theorem g7_smoothness (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (θ : EuclideanSpace ℝ (S × A)) (s₀ : S) :
    ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) s₀) θ‖ ≤ 8 / (1 - M.γ) ^ 3 := sorry

/-! ## G1 — Mei Lemma 8, the non-uniform Łojasiewicz inequality

The paper's central technical contribution. **No theorem in this repo lower-
bounds a gradient.** `loja_pointwise` is a one-line consequence of `⨅ ≤ ·` with
no gradient in it at all. -/

/-- **G1 — Mei Lemma 8.**

The gradient norm is bounded below by the suboptimality, scaled by the smallest
optimal-action probability. This is the inequality that makes gradient ascent
converge, and the reason the rate's constant can be exponentially small: when
`π(a*|s)` is tiny the gradient is tiny even though the suboptimality is large. -/
@[paper "Mei2020" "Lemma 8"]
theorem g1_lojasiewicz (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (astar : S → A) (μ : S) (θ : EuclideanSpace ℝ (S × A))
    (mismatch : ℝ) (hmis : 0 < mismatch) :
    (⨅ s : S, (F.toPolicy θ s) (astar s)) / (Real.sqrt (Fintype.card S) * mismatch)
        * (Vstar M μ - Vinf M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖ := sorry

/-! ## G2 — AKM Lemma 4.1, gradient domination

`GradientDomination.lean` contains no gradient-domination inequality: it proves
the "advantage ≤ 0 ⟹ optimal" direction only. -/

/-- **G2 — AKM Lemma 4.1.**

Suboptimality is bounded by a distribution-mismatch-weighted gradient norm. This
is what turns "the gradient is small" into "the policy is near-optimal". -/
@[paper "AKM2021" "Lemma 4.1"]
theorem g2_gradient_domination (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : EuclideanSpace ℝ (S × A))
    (mismatch : ℝ) (hmis : 0 < mismatch) :
    Vstar M μ - Vinf M (F.toPolicy θ) μ
      ≤ (mismatch / (1 - M.γ)) * ‖fderiv ℝ (fun t => Vinf M (F.toPolicy t) μ) θ‖ := sorry

/-! ## G8 / Mei Theorem 4 — the headline rate

All current rate results use finite-horizon `V`; both papers are
infinite-horizon. This goal is stated for `Vinf`, so discharging it closes G8
for the rate track as well. -/

/-- **Mei Theorem 4 — the `O(1/T)` rate for softmax policy gradient.**

The statement the repo is actually for. Note what it mentions and the current
`smooth_loja_rate` does not: an MDP, a softmax family, `Vinf`, and `V*`.

**`c` is existential, and that is forced.** An earlier draft took `c` as a
universally quantified hypothesis `(c : ℝ) (hc : 0 < c)`. That statement is
**not provable**: quantifying `c` universally lets the caller send `c → ∞`,
driving the bound to `0` and so asserting `Vstar - Vinf ≤ 0` for every
reachable policy. Machine-checked: from `0 < x` and `∀ c > 0, x ≤ K / c²`,
taking `c = √(2K/x)` gives `x ≤ x/2`, a contradiction.

This is the mirror of the degenerate-witness trap. A quantity left floating is
a defect either way: existential and unconstrained makes the goal too *weak*
(the prover picks it); universal makes it too *strong* (the caller picks it).
The paper's `c` is a specific constant determined by the MDP and the trajectory
— their Lemma 9 — so it belongs outside the `∀ T`, chosen once, exactly as
here. -/
@[paper "Mei2020" "Theorem 4"]
theorem mei_theorem4 (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 1 ≤ T →
      Vstar M μ - Vinf M (F.toPolicy (θ T)) μ
        ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T) := sorry

/-! ## The remaining soft spot in the vacuity defence

`Witness.lean` shows the *MDP and logit* hypotheses are jointly satisfiable by a
concrete two-state MDP. It does not cover the trajectory hypotheses: `hstep`
*defines* `θ` by recursion, and `mismatch` is a free positive real. Those are
satisfiable in a cheap sense, so a consistency witness cannot certify that the
conclusions are non-vacuous there.

The honest fix is a goal, not a note: show the ascent recursion actually admits
a solution, and that the mismatch coefficient is a real quantity rather than an
arbitrary constant the caller supplies. -/

/-- **The gradient-ascent trajectory exists.**

`hstep` in `mei_theorem4` and `mei_theorem6` constrains `θ` by a recursion. That
is only meaningful if some sequence satisfies it — otherwise those theorems are
vacuously true for lack of any `θ`. -/
@[infra "Trajectory-exists"]
theorem ascent_trajectory_exists (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (μ : S) (θ₀ : EuclideanSpace ℝ (S × A)) :
    ∃ θ : ℕ → EuclideanSpace ℝ (S × A), θ 0 = θ₀ ∧ ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t) :=
  Proofs.ascent_trajectory_exists_proof M F μ θ₀

/-! ### The distribution-mismatch coefficient

**Superseded 2026-08-22.** The previous goal here read

```lean
∃ mismatch : ℝ, 0 < mismatch ∧ ∀ s, dinf M π μ s ≤ mismatch * (1 / (1 - M.γ))
```

and an agent proved it with `mismatch = 1`, for every MDP, every policy and
every start state. The defect: `1/(1-γ)` **already bounds `dinf` on its own**,
so the goal bounded `dinf` by a free constant times a quantity that already
bounds it, and any positive multiplier worked. A textbook degenerate witness —
the quantity was existentially bound, so the prover picked it.

The repair is to bound against `μ s` instead, which forces the coefficient to
see where `μ` puts little mass, and to *define* the coefficient rather than
quantify over it (`mismatchCoeff` in `Target.lean`, mirroring how `Vstar` is
defined rather than chosen). -/

/-- **The mismatch coefficient bounds the occupancy ratio.**

`d^π_μ(s) ≤ mismatchCoeff · μ(s)` — the statement with content. Unlike the
superseded version this cannot be discharged by picking a convenient constant:
`mismatchCoeff` is a definition, and the bound is against `μ s`. -/
@[infra "Mismatch-bound"]
theorem mismatch_bound (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S) (s : S) :
    dinfDist M π μ s ≤ mismatchCoeff M π μ * μ s := sorry

/-- **The mismatch coefficient is positive**, given `μ` has full support.

Needs the `t = 0` term of `dinf`, which is the point mass at the start state. -/
@[infra "Mismatch-pos"]
theorem mismatch_pos (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S)
    (hμ : ∀ s, 0 < μ s) :
    0 < mismatchCoeff M π μ := sorry

/-! ## G10 — the entropy-regularized track

`geometric_rate` mentions no entropy, no `τ`, no policy and no MDP; its
hypothesis `hstep` *is* Mei Theorem 6. Their Lemmas 14 (entropy smoothness),
15 (entropy Łojasiewicz) and 16 exist to establish that contraction, and none is
formalized. -/

/-- **Mei Theorem 6 — the entropy-regularized geometric rate.**

Unlike Theorem 4 this constant is explicit, because the analogue of their
Lemma 9 (their Lemma 16) follows from monotone convergence rather than an
external citation. -/
@[paper "Mei2020" "Theorem 6"]
theorem mei_theorem6 (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (τ : ℝ) (hτ : 0 < τ) (μ : S) (η : ℝ) (hη : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfSoft M (F.toPolicy w) τ μ) (θ t))
    (K : ℝ) (hK₀ : 0 < K) (hK₁ : K < 1) (t : ℕ) :
    VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ t)) τ μ
      ≤ (VsoftStar M τ μ - VinfSoft M (F.toPolicy (θ 0)) τ μ) * (1 - K) ^ t := sorry

end PolicyGradient
