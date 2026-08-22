/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Meta.Paper
import PolicyGradient.Infinite
import PolicyGradient.Softmax
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

/-! ### The optimal value

Both papers state their rates against `V*`, the supremum over policies. -/

/-- The optimal infinite-horizon value: the supremum over all policies. -/
noncomputable def Vstar (M : FiniteMDP S A) (s₀ : S) : ℝ :=
  ⨆ π : Policy S A, Vinf M π s₀

/-! ## G5 — the vector parameter

Both papers optimize over `θ ∈ ℝ^(S×A)`. This repo uses `θ : ℝ`, a single real,
so "gradient norm" degenerates to `|f'|` and **G1 and G2 cannot even be
stated**. Everything else waits on this.

`EuclideanSpace ℝ (S × A)` is the target: `gradient` needs an
`InnerProductSpace`, which the plain function type `(S × A) → ℝ` lacks, and both
papers' bounds are on `‖∇V‖` in the ℓ² norm. -/

/-- A policy family differentiable in a **vector** parameter.

The Fréchet derivative `dπ θ s a : E →L[ℝ] ℝ` replaces the scalar `dπ` of
`DiffPolicy`. -/
structure VecPolicy (S A : Type*) [Fintype A] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The policy at parameter `θ`. -/
  toPolicy : E → Policy S A
  /-- The Fréchet derivative of `θ ↦ π(a|s)`. -/
  dπ : E → S → A → (E →L[ℝ] ℝ)
  /-- `dπ` really is the derivative. -/
  hasFDeriv : ∀ θ s a, HasFDerivAt (fun t => (toPolicy t s) a) (dπ θ s a) θ

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
      ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a := sorry

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

`c` is a hypothesis exactly as in the paper — their statement reads "`c` the
positive constant from Lemma 9", and their Lemma 9 is proved by citing AKM
Theorem 5.1 rather than from first principles. -/
@[paper "Mei2020" "Theorem 4"]
theorem mei_theorem4 (M : FiniteMDP S A)
    (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t))
    (c : ℝ) (hc : 0 < c) (T : ℕ) (hT : 1 ≤ T) :
    Vstar M μ - Vinf M (F.toPolicy (θ T)) μ
      ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T) := sorry

/-! ## G10 — the entropy-regularized track

`geometric_rate` mentions no entropy, no `τ`, no policy and no MDP; its
hypothesis `hstep` *is* Mei Theorem 6. Their Lemmas 14 (entropy smoothness),
15 (entropy Łojasiewicz) and 16 exist to establish that contraction, and none is
formalized. -/

/-- The Shannon entropy of a distribution. -/
noncomputable def entropy (d : Dist A) : ℝ := -∑ a, d a * Real.log (d a)

/-- The entropy-regularized value `Ṽ = V + τ·H`. -/
noncomputable def VinfSoft (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ) (s₀ : S) : ℝ :=
  Vinf M π s₀ + τ * entropy (π s₀)

/-- The optimal entropy-regularized value: the supremum over policies.

Defined rather than existentially quantified. Stating Theorem 6 as
`∃ Vsoftstar, Vsoftstar - Ṽ ≤ C(1-K)^t` would be **dischargeable in one line**
by `⟨b + c, by linarith⟩` — pick a small enough number and the inequality is
free. The target must name the real optimum. -/
noncomputable def VsoftStar (M : FiniteMDP S A) (τ : ℝ) (s₀ : S) : ℝ :=
  ⨆ π : Policy S A, VinfSoft M π τ s₀

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
