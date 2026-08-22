/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1

/-!
# Mei4 — Mei et al. Theorem 4, the `O(1/T)` rate

Work file for the frozen goal `Goal.mei_theorem4`.

**Verdict: the frozen statement is FALSE.** The defect is the one already
recorded twice in `Goal.lean` — for `g7_smoothness` ("Defect 1: `logits` was
universally quantified with no regularity hypothesis") and for `g1_lojasiewicz`
("Defect 2 — unconstrained `logits`"). `mei_theorem4` carries exactly the same
free parameter:

```lean
(logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
(hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
```

Nothing ties `logits` to `θ`. Mei's Theorem 4 is about the **tabular** softmax
parameterization `logits θ s a = θ (s,a)`; here any function at all is allowed,
including one that ignores `θ` entirely.

## The counterexample

Take `logits θ s a := 0` — constant in `θ`. Then:

* `F.toPolicy θ` is the **uniform** policy for every `θ`, so
  `w ↦ Vinf M (F.toPolicy w) μ` is a **constant function**;
* hence its `gradient` is `0` at every point, and `hstep` degenerates to
  `θ (t+1) = θ t`: gradient ascent never moves;
* the policy is frozen at uniform, which in `badMDP` (one state, two actions,
  `γ = 0`, rewards `1`/`0`) has value `1/2` against `Vstar = 1`.

So the left side is the **constant** `1/2` for every `T`, while the right side
`16 · |S| / (c² (1-γ)^6 T) = 16 / (c² T)` tends to `0` as `T → ∞`. No `c > 0`
survives: choosing `T > 32/c²` breaks the inequality.

This is *not* a quibble about the constant `16`, and it is not repaired by
making `c` small — `c` is existential and appears in the denominator, so
shrinking it inflates the right side, but the right side still decays like
`1/T` while the left side does not decay at all. The refutation is robust to
every numeric constant in the statement.

## Why this is a real defect and not a technicality

The same trick does **not** refute the tabular statement. Under
`logits θ s a = θ (s,a)` the objective is genuinely non-constant and the
trajectory genuinely moves; on the concrete `cMDP` of the `G9` section
(`r = (1,-1)`, `γ = 1/2`) numerical iteration of the exact recursion
`d_{t+1} = d_t + (1/32)·gc(d_t)` gives `sup_T (Vstar - Vinf(θ_T))·T / 1024 ≈
0.0419`, i.e. the frozen inequality holds there with `c ≈ 4.89`. The tabular
theorem is plausibly true; the frozen one is false for a reason orthogonal to
its mathematical content.

See the end of this file for what the statement should say instead, and for the
obstruction that remains even after the repair.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Mei4

/-! ## The degenerate family: constant logits

We reuse `badMDP` from `Proofs.lean` (one state `Unit`, two actions `Bool`,
`γ = 0`, `r true = 1`, `r false = 0`), for which `Vinf π () = π(true)`. -/

/-- The constant logits: `logits θ s a = 0`, ignoring `θ` completely.

This is a legal instantiation of `mei_theorem4`'s `logits` parameter — the
frozen statement imposes no hypothesis on it whatsoever. -/
noncomputable def constLogits :
    EuclideanSpace ℝ (Unit × Bool) → Unit → Bool → ℝ :=
  fun _ _ _ => 0

/-- The policy family induced by `constLogits`: uniform at every parameter. -/
noncomputable def Fconst : VecPolicy Unit Bool (EuclideanSpace ℝ (Unit × Bool)) where
  toPolicy := fun θ s => softmax (constLogits θ s)
  dπ := fun _ _ _ => 0
  hasFDeriv := fun θ s a => by
    have : (fun t : EuclideanSpace ℝ (Unit × Bool) =>
        ((softmax (constLogits t s) : Dist Bool)) a)
        = fun _ => ((softmax (constLogits θ s) : Dist Bool)) a := rfl
    rw [this]
    exact hasFDerivAt_const _ _

theorem Fconst_hF : ∀ θ s a, (Fconst.toPolicy θ s) a = softmax (constLogits θ s) a :=
  fun _ _ _ => rfl

/-- Under constant logits the uniform policy has `π(true) = 1/2`. -/
theorem Fconst_true (θ : EuclideanSpace ℝ (Unit × Bool)) :
    (Fconst.toPolicy θ ()) true = 1 / 2 := by
  show (softmax (constLogits θ ())) true = 1 / 2
  rw [softmax_apply]
  simp [constLogits]

/-- **The objective is constant.** This is the whole counterexample in one line:
the value does not depend on the parameter, because the policy does not. -/
theorem Vinf_Fconst_const :
    (fun w : EuclideanSpace ℝ (Unit × Bool) => Vinf badMDP (Fconst.toPolicy w) ())
      = fun _ => (1 / 2 : ℝ) := by
  funext w
  rw [Vinf_badMDP, Fconst_true]

/-- Hence the gradient vanishes identically. -/
theorem gradient_Fconst (θ : EuclideanSpace ℝ (Unit × Bool)) :
    gradient (fun w => Vinf badMDP (Fconst.toPolicy w) ()) θ = 0 := by
  rw [Vinf_Fconst_const]
  simpa using (hasGradientAt_const (𝕜 := ℝ) (F := EuclideanSpace ℝ (Unit × Bool))
    (1 / 2 : ℝ) θ).gradient

/-! ## `Vstar badMDP = 1`

Already available as `Proofs.Vstar_badMDP` in `Proofs.lean` (proved there via
`detPolicy (fun _ => true)`), so nothing new is needed here. -/

/-! ## The refutation -/

/-- **`Goal.mei_theorem4` is FALSE as frozen.**

The statement below is the frozen goal verbatim, negated: every hypothesis is
reproduced with the same type, and the conclusion is the exact conclusion of
`mei_theorem4`.

Witness: `badMDP`, `constLogits`, `Fconst`, and the *constant* trajectory
`θ t = 0`. Because the objective does not depend on the parameter, its gradient
is `0` everywhere, so `θ (t+1) = θ t + η • 0 = θ t` satisfies `hstep`, and the
policy stays uniform forever. The suboptimality is then `1 - 1/2 = 1/2` at
every `T`, while the claimed bound `16 / (c² T)` tends to `0`. -/
theorem mei4_is_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S)
        (_ : DecidableEq A) (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A)),
          (∀ t, θ (t + 1)
            = θ t + ((1 - M.γ) ^ 3 / 8)
                • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) →
          ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 1 ≤ T →
            Vstar M μ - Vinf M (F.toPolicy (θ T)) μ
              ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)) := by
  intro h
  -- the constant trajectory satisfies `hstep`, because the gradient vanishes
  have hstep : ∀ t : ℕ, (fun _ : ℕ => (0 : EuclideanSpace ℝ (Unit × Bool))) (t + 1)
      = (fun _ : ℕ => (0 : EuclideanSpace ℝ (Unit × Bool))) t
        + ((1 - badMDP.γ) ^ 3 / 8)
          • gradient (fun w => Vinf badMDP (Fconst.toPolicy w) ())
              ((fun _ : ℕ => (0 : EuclideanSpace ℝ (Unit × Bool))) t) := by
    intro t
    rw [gradient_Fconst]
    simp
  obtain ⟨c, hc, hbd⟩ :=
    h Unit Bool inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance badMDP constLogits Fconst Fconst_hF
      badMDP_r badMDP_γ₀ badMDP_γ₁ () (fun _ => 0) hstep
  -- the left side is the constant `1/2`
  have hlhs : ∀ T : ℕ,
      Vstar badMDP () - Vinf badMDP (Fconst.toPolicy ((fun _ : ℕ => (0 :
        EuclideanSpace ℝ (Unit × Bool))) T)) () = 1 / 2 := by
    intro T
    rw [Vstar_badMDP, Vinf_badMDP, Fconst_true]
    norm_num
  -- the right side is `16 / (c² T)`
  have hcard : (Fintype.card Unit : ℝ) = 1 := by simp
  have hγ : ((1 : ℝ) - badMDP.γ) ^ 6 = 1 := by norm_num [badMDP]
  -- pick `T` large enough to break it
  obtain ⟨T, hT⟩ := exists_nat_gt (32 / c ^ 2)
  have hTpos : (0 : ℝ) < 32 / c ^ 2 := by positivity
  have hT0 : (0 : ℝ) < T := lt_trans hTpos hT
  have hT1 : 1 ≤ T := by
    by_contra hcon
    push Not at hcon
    interval_cases T
    · simp at hT0
  have := hbd T hT1
  rw [hlhs T, hcard, hγ] at this
  -- `1/2 ≤ 16 / (c² · 1 · T)` contradicts `T > 32/c²`
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  rw [div_lt_iff₀ hc2] at hT
  have hden : (0 : ℝ) < c ^ 2 * 1 * T := by positivity
  rw [le_div_iff₀ hden] at this
  nlinarith [this, hT]

/-! ## What the statement should say instead

The minimal repair is the one already applied to `g1_lojasiewicz` and
`g7b_smoothness`: **pin the parameterization to tabular**, replacing

```lean
(logits : EuclideanSpace ℝ (S × A) → S → A → ℝ)
(hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (logits θ s) a)
```

by

```lean
(hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
```

That is the parameterization Mei's Theorem 4 is actually about, the one
`g7b_smoothness` is proved for, and the one `Witness.lean` records as "exactly
the one both papers use". With it, the constant-logits family is no longer a
legal instantiation and this refutation evaporates.

A second, independent repair is also needed: the frozen statement gives no
non-degeneracy hypothesis, so an MDP in which **every** policy is optimal makes
`Vstar - Vinf = 0` — harmless here, but `g3_strict_suboptimality` (which the
rate machinery's `hlt` hypothesis needs) carries
`hnondeg : ∃ π, Vinf M π μ < Vstar M μ`, and `domination_rate_abstract` cannot
be instantiated without it.

## The obstruction that survives the repair

Repairing the parameterization does **not** make the goal provable from what the
repo has. Three gaps remain, in increasing order of severity.

**(1) `domination_rate_abstract` is one-dimensional.** Its type is

```lean
{f f' : ℝ → ℝ} → SmoothAt f f' β → (x : ℕ → ℝ) →
  (∀ t, x (t+1) = x t + (1/β) * f' (x t)) → ...
```

with `SmoothAt f f' β : ∀ x y : ℝ, |f y - f x - f' x * (y - x)| ≤ β/2 * (y-x)^2`
— a scalar parameter. The goal's trajectory lives in
`EuclideanSpace ℝ (S × A)` and steps by `gradient`, not by a scalar derivative.
`AKM.lean` has no vector-valued analogue of `SmoothAt`, `ascent_step`,
`quad_decrease_of_domination`, or `domination_rate_abstract`. **New goal to
state:** the `EuclideanSpace` versions of all four, with `SmoothAt` replaced by
`∀ x y, |f y - f x - ⟪gradient f x, y - x⟫| ≤ β/2 * ‖y - x‖^2` and the ascent
step by `x + (1/β) • gradient f x`. `g7b_smoothness` proves the second-derivative
bound `‖fderiv (fderiv V)‖ ≤ 8/(1-γ)³`, so the bridge from that to the Taylor
form is the standard `norm_image_sub_le_of_norm_deriv_le_segment`-style estimate;
this gap is real work but not research.

**(2) The Łojasiewicz coefficient is trajectory-dependent, and that is the
crux.** After (1), instantiating the rate machinery needs

```lean
hdom : ∀ t, c * (Vstar M μ - Vinf M (F.toPolicy (θ t)) μ)
         ≤ ‖gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)‖
```

`g1_lojasiewicz` supplies the domination inequality, but its coefficient is
`(⨅ s, π_θ(a*|s)) / (√|S| · mismatchCoeff)` — it depends on `θ`, and it degrades
as the policy sharpens. To feed `domination_rate_abstract` one needs a **single**
`c` valid at every `t`, i.e.

```lean
0 < ⨅ t, ⨅ s, (F.toPolicy (θ t) s) (astar s)
```

which is precisely `g9_c_positive`. That goal is **open**, and the note in
`Goal.lean` records that the easy route is closed: `m(t) ≥ m(0)` fails in
66/400 random MDPs, so no monotonicity argument produces the infimum.

**(3) The infimum's positivity needs an asymptotic argument nobody here has
formalized, and it is not a compactness argument.** This is the honest answer to
"can `c` be produced non-constructively from finiteness + strict positivity of
softmax + compactness on the simplex?" — **no**, and the reason is structural,
not a missing lemma:

* Softmax gives `0 < π_θ(a|s)` at each *fixed* `θ`, and there are finitely many
  `(s,a)`, so `⨅ s, π_θ(a*|s) > 0` for each fixed `t`. But the infimum in
  question is over `t : ℕ` — an **infinite** index set — and a countable
  infimum of strictly positive reals is routinely `0`.
* Compactness does not rescue it, because the trajectory is **not** confined to
  a compact set: `‖θ t‖ → ∞` is exactly what gradient ascent does here (the
  `G9` counterexample computes the logit gap growing linearly under a standing
  lower bound). The closure of `{π_θ(t)}` in the simplex therefore meets the
  boundary, where probabilities vanish.
* So positivity of the infimum is genuinely an **asymptotic** claim about the
  trajectory: the optimal-action probabilities must not decay to `0` *along
  this particular sequence*. Mei's Lemma 9 asserts it by citing AKM Theorem 5.1;
  AKM Theorem 5.1 proves asymptotic convergence `V(θ_t) → V*`, and the
  optimal-action probabilities are bounded below only *because* of that
  convergence. The dependency is therefore:

  ```
  c > 0  ⟸  π_t(a*|s) ↛ 0  ⟸  V(θ_t) → V*   (asymptotic convergence)
  ```

  and the repo's `ascent_converges` gives only `∃ L ≤ fstar, Tendsto ... (𝓝 L)`
  — it does **not** identify `L = fstar`. That identification is the missing
  result, and it is not a corollary of anything present.

**New goals to state, to unblock this.** In dependency order:

```lean
-- (A) The vector-valued smoothness/ascent/rate chain (mechanical given g7b).
theorem smoothAtVec_of_second_deriv ... :
    ∀ x y, |f y - f x - ⟪gradient f x, y - x⟫| ≤ β/2 * ‖y - x‖^2
theorem ascent_step_vec ... ; theorem domination_rate_vec ...

-- (B) Asymptotic global convergence — the crux, AKM Theorem 5.1.
--     This is what `ascent_converges` stops short of.
theorem softmax_ascent_converges_to_optimum (M) (F) (hF : tabular) ... (θ) (hstep) :
    Filter.Tendsto (fun t => Vinf M (F.toPolicy (θ t)) μ) Filter.atTop
      (nhds (Vstar M μ))

-- (C) The optimal-action probabilities stay bounded away from zero,
--     DERIVED from (B) rather than assumed — this is the corrected `g9_c_positive`,
--     with `hastar : ∀ s, Qstar M s (astar s) = Vstar M s` (already added).
theorem g9_c_positive ... : ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s, (F.toPolicy (θ t) s) (astar s)
```

(B) is the genuinely hard one and is the single highest-value goal to state: it
is the gap `Goal.lean` already names ("`ascent_converges` yields only `∃ L ≤
fstar` ... never identifying `L = fstar`. This goal is that missing bridge"),
and every route to Theorem 4 passes through it. Note also that Li–Wei–Chi–Chen
show `c` can be as small as `|S|^(2^Ω(1/(1-γ)))`, so (C) cannot be strengthened
to an explicit constant — it must stay existential, which is consistent with the
frozen statement's shape once the parameterization is pinned. -/

end Mei4

end Proofs
end PolicyGradient
