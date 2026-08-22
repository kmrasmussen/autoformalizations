/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Defs
import PolicyGradient.Softmax
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Witness.lean — consistency witnesses for the frozen goals

**This file exists to defend against vacuous truth.**

`Goal.lean` freezes the repo's targets as theorems with `sorry`, which stops the
"unproved content hides in hypothesis positions" failure that `GAPS.md`
documents. It does not stop the *next* failure, which the discipline section of
`Goal.lean` names explicitly:

> A goal proved from contradictory hypotheses is vacuous, not done. Each goal
> carrying hypotheses needs a consistency witness (a concrete MDP satisfying
> them) before it counts.

The point is that `∀ M, H₁ M → H₂ M → C M` is trivially true — `sorry`-free,
axiom-clean, and completely worthless — whenever `H₁ ∧ H₂` is unsatisfiable.
Lean will not tell you. `#print axioms` will not tell you. The build stays
green. A reader sees a theorem whose hypotheses "are just the paper's standing
assumptions" and has no way to check that those assumptions can be met at once,
because nothing in the repo ever meets them.

So this file exhibits a concrete object and proves, as ordinary theorems about
that object, that every standing hypothesis of the frozen goals holds of it.
Nothing here is stated about a variable `M`, a variable `logits`, or a variable
anything: every statement below names `witnessMDP` or `tabularLogits`. That is
the whole content — a universally quantified claim about a hypothesis set is
worth nothing, since the vacuous case satisfies it too.

## What is witnessed

`g7_smoothness`, `mei_theorem4` and `mei_theorem6` all carry the same three MDP
hypotheses:

* `hr  : ∀ s a, |M.r s a| ≤ 1`
* `hγ₀ : 0 ≤ M.γ`
* `hγ₁ : M.γ < 1`

discharged here by `witnessMDP_reward_bound`, `witnessMDP_gamma_nonneg` and
`witnessMDP_gamma_lt_one`. `g1_lojasiewicz` and `g2_gradient_domination` carry
the two `γ` hypotheses, likewise covered.

`g5_g6_softmax_family` carries the logit hypothesis

* `hlog : ∀ s a, Differentiable ℝ (fun θ => logits θ s a)`

discharged by `tabularLogits_differentiable`. The tabular parameterization
`logits θ s a = θ (s, a)` is exactly the one both papers use, so this is the
intended instance rather than an evasion: it is a coordinate projection of
`EuclideanSpace ℝ (S × A)`, hence a continuous linear map, hence differentiable.

`witness_all_hypotheses` bundles the lot into a single statement, so the fact
that they hold **simultaneously** — not merely one at a time — is itself a
theorem.

## The discipline that applies to this file

A witness can be faked in the same way a goal can: by picking an MDP so
degenerate that the hypotheses are true for uninteresting reasons, or by quietly
adjusting the MDP until an awkward hypothesis goes away. Two guards:

* `witnessMDP` is fixed **before** the proofs and is not degenerate on the axes
  the hypotheses constrain: its rewards are not all zero (they range over
  `-1, 0, 1/2, 1`, and the bound `|r| ≤ 1` is *attained*, so `hr` is tight
  rather than slack), its discount `1/2` is strictly between the two bounds, and
  its transition kernel is genuinely state- and action-dependent.
* If some hypothesis had turned out **not** to be satisfiable, the correct
  response would have been to report the goal as wrong, not to edit the MDP.
  None did; see the note at the end of this file.
-/

open Finset

namespace PolicyGradient

/-! ## The witness MDP

Two states, two actions, `γ = 1/2`. -/

/-- The transition kernel of `witnessMDP`, as a probability vector on `Fin 2`.

`witnessTransition s a` puts mass `witnessP s a` on state `0` and the rest on
state `1`, where `witnessP` depends on both `s` and `a` — the kernel is not
constant, so the MDP is not a disguised bandit. -/
noncomputable def witnessP : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1
  | 0, 1 => 1 / 4
  | 1, 0 => 1 / 2
  | 1, 1 => 0

theorem witnessP_mem (s a : Fin 2) : 0 ≤ witnessP s a ∧ witnessP s a ≤ 1 := by
  fin_cases s <;> fin_cases a <;> norm_num [witnessP]

/-- Next-state distribution: mass `witnessP s a` on state `0`. -/
noncomputable def witnessTransition (s a : Fin 2) : Dist (Fin 2) where
  prob i := if i = 0 then witnessP s a else 1 - witnessP s a
  nonneg i := by
    rcases (witnessP_mem s a) with ⟨h0, h1⟩
    by_cases h : i = 0 <;> simp [h] <;> linarith
  sum_eq_one := by
    simp [Fin.sum_univ_two]

/-- The reward of `witnessMDP`. The four values `1, -1, 1/2, 0` all lie in
`[-1, 1]` and the bound is **attained** at `(0,0)` and `(0,1)`, so the
hypothesis `|r| ≤ 1` is tight for this witness, not vacuously slack. -/
noncomputable def witnessReward : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1
  | 0, 1 => -1
  | 1, 0 => 1 / 2
  | 1, 1 => 0

/-- **The witness MDP.** Two states, two actions, discount `1/2`.

Every hypothesis carried by the frozen goals in `Goal.lean` is proved below to
hold of *this* object. -/
noncomputable def witnessMDP : FiniteMDP (Fin 2) (Fin 2) where
  P := witnessTransition
  r := witnessReward
  γ := 1 / 2

@[simp] theorem witnessMDP_r (s a : Fin 2) : witnessMDP.r s a = witnessReward s a := rfl

@[simp] theorem witnessMDP_gamma : witnessMDP.γ = 1 / 2 := rfl

/-! ## The standing MDP assumptions hold of `witnessMDP` -/

/-- **Bounded rewards** — the `hr` hypothesis of `g7_smoothness`,
`mei_theorem4` and `mei_theorem6`. -/
theorem witnessMDP_reward_bound : ∀ s a, |witnessMDP.r s a| ≤ 1 := by
  intro s a
  fin_cases s <;> fin_cases a <;> norm_num [witnessMDP, witnessReward]

/-- The reward bound is **attained**: this witness does not satisfy `hr` merely
by having tiny rewards. -/
theorem witnessMDP_reward_bound_tight : |witnessMDP.r 0 0| = 1 := by
  norm_num [witnessMDP, witnessReward]

/-- **Nonnegative discount** — the `hγ₀` hypothesis. -/
theorem witnessMDP_gamma_nonneg : 0 ≤ witnessMDP.γ := by norm_num [witnessMDP]

/-- **Discount below one** — the `hγ₁` hypothesis. -/
theorem witnessMDP_gamma_lt_one : witnessMDP.γ < 1 := by norm_num [witnessMDP]

/-- The discount is strictly inside its allowed range: `hγ₀` is not met by
`γ = 0` (which would make the infinite-horizon objective a one-step bandit) and
`hγ₁` is not met at the boundary. -/
theorem witnessMDP_gamma_pos : 0 < witnessMDP.γ := by norm_num [witnessMDP]

/-! ## The logit witness

`g5_g6_softmax_family` assumes a differentiable logit map. The tabular
parameterization — one parameter per state–action pair, `logits θ s a = θ (s,a)`
— is the one both papers use, and it is differentiable because it is a
coordinate projection of `EuclideanSpace ℝ (S × A)`, i.e. a continuous linear
map. -/

section Logits

variable {S A : Type*} [Fintype S] [Fintype A]

/-- **The tabular logits.** `θ ↦ θ (s, a)`: the softmax parameterization of both
papers, where the parameter vector has one coordinate per state–action pair. -/
noncomputable def tabularLogits (θ : EuclideanSpace ℝ (S × A)) (s : S) (a : A) : ℝ :=
  θ (s, a)

omit [Fintype S] [Fintype A] in
/-- **Differentiability of the logits** — the `hlog` hypothesis of
`g5_g6_softmax_family`.

Proved, not assumed: `fun θ => θ (s, a)` *is* `EuclideanSpace.proj (s, a)`, a
continuous linear map, and continuous linear maps are differentiable. -/
theorem tabularLogits_differentiable :
    ∀ (s : S) (a : A), Differentiable ℝ (fun θ : EuclideanSpace ℝ (S × A) =>
      tabularLogits θ s a) :=
  fun s a => (EuclideanSpace.proj (𝕜 := ℝ) (s, a)).differentiable

omit [Fintype S] [Fintype A] in
/-- The tabular logits are not constant in `θ` — they genuinely depend on the
parameter, so the differentiability witness is not the trivial one (a constant
map is differentiable too, which is exactly why a bare `Differentiable` witness
would prove nothing). -/
theorem tabularLogits_nonconstant [DecidableEq S] [DecidableEq A] (s : S) (a : A) :
    tabularLogits (0 : EuclideanSpace ℝ (S × A)) s a
      ≠ tabularLogits (EuclideanSpace.single (s, a) (1 : ℝ)) s a := by
  simp [tabularLogits]

end Logits

/-! ## Everything at once

The individual theorems above would still be compatible with the hypothesis set
being jointly unsatisfiable, if they held of *different* objects. They do not:
they all hold of `witnessMDP` and `tabularLogits`, and this theorem says so in
one statement. -/

/-- **The consistency witness.** Every standing hypothesis of the frozen goals in
`Goal.lean` holds simultaneously, of one concrete MDP and one concrete logit
map. Therefore none of those goals is vacuously true. -/
theorem witness_all_hypotheses :
    (∀ s a, |witnessMDP.r s a| ≤ 1)
    ∧ 0 ≤ witnessMDP.γ
    ∧ witnessMDP.γ < 1
    ∧ (∀ (s a : Fin 2), Differentiable ℝ
        (fun θ : EuclideanSpace ℝ (Fin 2 × Fin 2) => tabularLogits θ s a)) :=
  ⟨witnessMDP_reward_bound, witnessMDP_gamma_nonneg, witnessMDP_gamma_lt_one,
    tabularLogits_differentiable⟩

/-! ## Axiom check

These print `[propext, Classical.choice, Quot.sound]` and nothing else, as
`Goal.lean`'s discipline requires. A witness discharged by an `axiom` would
witness nothing. -/

section AxiomCheck

#print axioms witnessMDP
#print axioms witnessMDP_reward_bound
#print axioms witnessMDP_reward_bound_tight
#print axioms witnessMDP_gamma_nonneg
#print axioms witnessMDP_gamma_lt_one
#print axioms witnessMDP_gamma_pos
#print axioms tabularLogits_differentiable
#print axioms tabularLogits_nonconstant
#print axioms witness_all_hypotheses

end AxiomCheck

/-! ## Finding

Every standing hypothesis carried by the frozen goals was in fact satisfiable,
and by the intended objects rather than by contrivances: a two-state two-action
discounted MDP with rewards in `[-1,1]` (bound attained) and `γ = 1/2`, and the
tabular softmax parameterization. No goal in `Goal.lean` is vacuous on account
of its MDP or logit hypotheses.

This does **not** certify the goals' remaining hypotheses. `mei_theorem4` and
`mei_theorem6` additionally assume a gradient-ascent recursion `hstep` and a
Łojasiewicz constant `c > 0` / contraction factor `K ∈ (0,1)`; `g1_lojasiewicz`
and `g2_gradient_domination` assume `0 < mismatch`. Those are satisfiable in the
cheap sense (`hstep` *defines* `θ` by recursion, and `c`, `K`, `mismatch` are
free reals), but whether the resulting conclusions are non-vacuous is the
mathematical content of the goals themselves, not something a witness settles.
-/

/-! ### The nonconstancy statement is not vacuous

Both sides of `tabularLogits_nonconstant` evaluate, so it really does say the
map varies with `θ`. -/

example : tabularLogits (0 : EuclideanSpace ℝ (Fin 2 × Fin 2)) 0 0 = 0 := by
  simp [tabularLogits]

example : tabularLogits (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℝ)) 0 0 = 1 := by
  simp [tabularLogits]

end PolicyGradient
