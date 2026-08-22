/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1Agg

/-!
# G1c — the corrected aggregate bound is STILL FALSE

Work file for the frozen goals `g1_aggregate_bound` (`@[infra "G1-aggregate"]`)
and `g1_lojasiewicz` (`@[paper "Mei2020" "Lemma 8"]`) as restated on
2026-08-22, where `hastar` became `∀ s, 0 < (πstar s) (astar s)` — `astar`
selects an action the fixed optimal policy actually plays, per Mei Lemma 8's
"fix an arbitrary optimal policy `π*`".

**Result: `g1_aggregate_bound` is refuted a second time**, under the *new*
hypothesis.  `g1c_aggregate_bound_general_false` is machine-checked with axioms
`[propext, Classical.choice, Quot.sound]`.

## Why the fix does not close the hole

Pinning `astar` into `supp πstar` removes *one* freedom but not the one that
matters.  `hstar` makes `πstar` optimal at every state, so
`optimal_support_greedy` forces `Q*(s,a) = V*(s)` for **every** `a ∈ supp πstar`
— the support is a set of `Q*`-tied actions.  `hastar` says `astar s` lies in
that set; it does **not** say `astar s` maximizes `A^π(s,·)` over it.  The
performance-difference step

```
V*_μ - V^π_μ  ≤  ∑_s d^{πstar}_μ(s) · A^π(s, a*(s))                    (‡)
```

needs `A^π(s, a*(s)) ≥ ∑_a πstar(a|s)·A^π(s,a)`, i.e. `a*(s)` at the top of the
support, and a support with two `Q*`-tied actions carrying different `A^π` still
admits the bad choice.  Concretely on the witness below, at state `1` the
support is `{1, 3}` with `A^π(1,1) = 7/932 ≈ 0.0075` and
`A^π(1,3) = 107/466 ≈ 0.23` — a factor of thirty — and `astar 1 = 1` takes
the small one while `πstar` puts `5/6` of its mass on the large one.

So this is the **fourth** refutation in the `G1` family from the same tie
defect (`hgreedy`, `advantage_cross_state`, `g1_aggregate_bound` under
`Q*`-optimal `astar`, and now `g1_aggregate_bound` under support-membership
`astar`).  Membership in `supp πstar` is strictly weaker than what `(‡)` needs.

`g1_lojasiewicz` itself is **not** refuted — see the end of this file.

## The witness

`S = Fin 2`, `A = Fin 4`, `γ = 1/4`, deterministic transitions.

```
r = ![![1, 1, 0, -1], ![0, 1, 1, 1]]
P s a = δ_{t(s,a)},   t = ![![1, 0, 0, 1], ![1, 0, 1, 1]]
μ = (1/10, 9/10)
πstar = ![![1/2, 1/2, 0, 0], ![0, 1/6, 0, 5/6]]
astar = ![1, 1]
θ = log ![![5, 1, 3, 7], ![3, 2, 8, 2]]   so   π = ![![5,1,3,7]/16, ![3,2,8,2]/15]
```

`|r| ≤ 1` everywhere, `V^{πstar} = (4/3, 4/3) = V*`, and

```
Q* = ![![4/3, 4/3, 1/3, -2/3], ![1/3, 4/3, 4/3, 4/3]]
```

so `V* = max_a Q*` at both states and `supp πstar ⊆ argmax Q*` at both states —
every frozen hypothesis holds, including `hastar` with
`πstar(1|0) = 1/2 > 0` and `πstar(1|1) = 1/6 > 0`.

## The numbers

```
V^π         = (97/699, 718/699)
d^π_μ       = (104/699, 276/233)
d^{πstar}_μ = (28/165, 64/55)      mismatchCoeff = 56/33
A^π(s,a*(s)) = (835/932, 7/932)
π(a*(s)|s)   = (1/16, 2/15)        ⨅_s π(a*(s)|s) = 1/16
V*_μ = 4/3,  V^π_μ = 6559/6990
```

so the frozen conclusion reads

```
2761/111840  ≤  434021/26873055,    i.e.  0.024687 ≤ 0.016151,
```

false by a factor of `1.529` — larger than the `1.292` of the previous
refutation, so no constant repair in `1/(1-γ)` or `mismatchCoeff` survives
either.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section G1cCounterexample

open scoped BigOperators

/-- The deterministic successor: `t(s,a)`. -/
noncomputable def ccT (s : Fin 2) (a : Fin 4) : Fin 2 :=
  if s = 0 then (if a = 0 then 1 else if a = 1 then 0 else if a = 2 then 0 else 1)
  else (if a = 0 then 1 else if a = 1 then 0 else if a = 2 then 1 else 1)

/-- The reward. -/
noncomputable def ccR (s : Fin 2) (a : Fin 4) : ℝ :=
  if s = 0 then (if a = 0 then 1 else if a = 1 then 1 else if a = 2 then 0 else -1)
  else (if a = 0 then 0 else 1)

/-- The witness MDP: deterministic transitions, integer rewards, `γ = 1/4`. -/
noncomputable def ccMDP : FiniteMDP (Fin 2) (Fin 4) where
  P := fun s a => pointMass (ccT s a)
  r := ccR
  γ := 1/4

@[simp] theorem ccMDP_gamma : ccMDP.γ = 1/4 := rfl

theorem ccMDP_r (s : Fin 2) (a : Fin 4) : ccMDP.r s a = ccR s a := rfl

theorem ccMDP_P (s : Fin 2) (a : Fin 4) (s' : Fin 2) :
    (ccMDP.P s a) s' = if s' = ccT s a then 1 else 0 := rfl

theorem cc_γ₀ : (0:ℝ) ≤ ccMDP.γ := by norm_num [ccMDP]
theorem cc_γ₁ : ccMDP.γ < 1 := by norm_num [ccMDP]

theorem cc_hr : ∀ s a, |ccMDP.r s a| ≤ 1 := by
  intro s a
  show |ccR s a| ≤ 1
  unfold ccR
  fin_cases s <;> fin_cases a <;> norm_num [Fin.ext_iff]

/-! ### `πstar` — the optimal policy, with two-action support at both states -/

/-- `πstar 0 = (1/2, 1/2, 0, 0)`, `πstar 1 = (0, 1/6, 0, 5/6)`. -/
noncomputable def ccPistar : Policy (Fin 2) (Fin 4) := fun s =>
  { prob := fun a =>
      if s = 0 then (if a = 0 then 1/2 else if a = 1 then 1/2 else 0)
      else (if a = 1 then 1/6 else if a = 3 then 5/6 else 0)
    nonneg := by
      intro a
      by_cases h : s = 0 <;> simp only [h, if_true, if_false] <;>
        fin_cases a <;> norm_num [Fin.ext_iff]
    sum_eq_one := by
      rw [Fin.sum_univ_four]
      by_cases h : s = 0 <;> simp only [h, if_true, if_false] <;>
        norm_num [Fin.ext_iff] }

theorem ccPistar_apply (s : Fin 2) (a : Fin 4) :
    (ccPistar s) a =
      if s = 0 then (if a = 0 then 1/2 else if a = 1 then 1/2 else 0)
      else (if a = 1 then 1/6 else if a = 3 then 5/6 else 0) := rfl

/-- The start distribution `μ = (1/10, 9/10)`. -/
noncomputable def ccMu : Dist (Fin 2) := agD (1/10) (by norm_num) (by norm_num)

@[simp] theorem ccMu_apply (s : Fin 2) :
    ccMu s = if s = 0 then 1/10 else 9/10 := by
  show (if s = 0 then (1:ℝ)/10 else 1 - 1/10) = _
  by_cases h : s = 0 <;> simp [h] <;> norm_num

theorem cc_hmu : ∀ s, 0 < ccMu s := by
  intro s; rw [ccMu_apply]; by_cases h : s = 0 <;> simp [h] <;> norm_num

/-- `a* = ![1, 1]`.  Both lie in `supp πstar`, so the **new** `hastar` holds. -/
noncomputable def ccAstar : Fin 2 → Fin 4 := ![1, 1]

/-! ### `V^{πstar} = V* = (4/3, 4/3)` -/

theorem cc_Vinf_pistar (s : Fin 2) : Vinf ccMDP ccPistar s = 4/3 := by
  refine Vinf_eq_of_bellman ccMDP ccPistar cc_hr cc_γ₀ cc_γ₁ (fun _ => 4/3) ?_ s
  intro x
  show (4:ℝ)/3 = ∑ a, (ccPistar x) a * (ccMDP.r x a + ccMDP.γ * ∑ s', (ccMDP.P x a) s' * (4/3))
  rw [Fin.sum_univ_four]
  simp only [ccPistar_apply, Fin.sum_univ_two, ccMDP_P]
  show (4:ℝ)/3 = _
  simp only [ccMDP_r, ccMDP_gamma]
  unfold ccR ccT
  fin_cases x <;> norm_num [Fin.ext_iff]

theorem cc_Vstar (s : Fin 2) : Vstar ccMDP s = 4/3 := by
  have hb : ∀ π : Policy (Fin 2) (Fin 4), Vinf ccMDP π s ≤ 4/3 := by
    intro π
    have := abs_Vinf_le ccMDP π 1 zero_le_one cc_hr cc_γ₀ cc_γ₁ s
    have h2 : (1:ℝ) / (1 - ccMDP.γ) = 4/3 := by norm_num [ccMDP]
    rw [h2] at this
    exact (abs_le.mp this).2
  refine le_antisymm (ciSup_le hb) ?_
  have hbdd : BddAbove (Set.range fun π : Policy (Fin 2) (Fin 4) => Vinf ccMDP π s) :=
    ⟨4/3, by rintro y ⟨π, rfl⟩; exact hb π⟩
  have := le_ciSup hbdd ccPistar
  rwa [cc_Vinf_pistar s] at this

theorem cc_hstar : ∀ s, Vinf ccMDP ccPistar s = Vstar ccMDP s := by
  intro s; rw [cc_Vinf_pistar, cc_Vstar]

/-- **The new `hastar`**: `astar s` is an action `πstar` actually plays.
`πstar(1|0) = 1/2` and `πstar(1|1) = 1/6`. -/
theorem cc_hastar : ∀ s, 0 < (ccPistar s) (ccAstar s) := by
  intro s
  rw [ccPistar_apply]
  unfold ccAstar
  fin_cases s <;> norm_num [Fin.ext_iff]

/-! ### The tabular softmax family and the witness parameter -/

/-- The tabular softmax family on `Fin 2 × Fin 4`. -/
noncomputable def ccF : VecPolicy (Fin 2) (Fin 4) (E (Fin 2) (Fin 4)) where
  toPolicy := fun θ s => softmax (fun a => θ (s, a))
  dπ := fun θ s a => fderiv ℝ (fun t : E (Fin 2) (Fin 4) => (softmax (fun a' => t (s, a'))) a) θ
  hasFDeriv := fun θ s a => by
    refine (softmax_diff (E := E (Fin 2) (Fin 4)) (fun t a' => t (s, a')) ?_ a θ).hasFDerivAt
    intro a'
    exact (EuclideanSpace.proj (s, a') :
      E (Fin 2) (Fin 4) →L[ℝ] ℝ).differentiable

theorem cc_hF : ∀ θ s a, (ccF.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a :=
  fun _ _ _ => rfl

/-- The softmax weights: `π 0 = (5,1,3,7)/16`, `π 1 = (3,2,8,2)/15`. -/
noncomputable def ccW (s : Fin 2) (a : Fin 4) : ℝ :=
  if s = 0 then (if a = 0 then 5 else if a = 1 then 1 else if a = 2 then 3 else 7)
  else (if a = 0 then 3 else if a = 1 then 2 else if a = 2 then 8 else 2)

theorem ccW_pos (s : Fin 2) (a : Fin 4) : 0 < ccW s a := by
  unfold ccW; fin_cases s <;> fin_cases a <;> norm_num [Fin.ext_iff]

/-- The witness parameter: the logits are the logs of the weights. -/
noncomputable def ccTheta : E (Fin 2) (Fin 4) :=
  (EuclideanSpace.equiv (Fin 2 × Fin 4) ℝ).symm (fun p => Real.log (ccW p.1 p.2))

theorem ccTheta_apply (s : Fin 2) (a : Fin 4) : ccTheta (s, a) = Real.log (ccW s a) := by
  simp [ccTheta, EuclideanSpace.equiv]

theorem cc_exp_theta (s : Fin 2) (a : Fin 4) : Real.exp (ccTheta (s, a)) = ccW s a := by
  rw [ccTheta_apply, Real.exp_log (ccW_pos s a)]

/-- The normalizing constant: `16` at state `0`, `15` at state `1`. -/
noncomputable def ccZ (s : Fin 2) : ℝ := if s = 0 then 16 else 15

/-- The witness policy `π = softmax(ccTheta)`, exactly rational. -/
theorem cc_pi (s : Fin 2) (a : Fin 4) :
    (ccF.toPolicy ccTheta s) a = ccW s a / ccZ s := by
  rw [cc_hF, softmax_apply]
  have hden : ∑ a' : Fin 4, Real.exp (ccTheta (s, a')) = ccZ s := by
    rw [Fin.sum_univ_four]
    simp only [cc_exp_theta]
    unfold ccW ccZ
    fin_cases s <;> norm_num [Fin.ext_iff]
  rw [cc_exp_theta, hden]

/-! ### `V^π = (97/699, 718/699)` -/

noncomputable def ccV (s : Fin 2) : ℝ := if s = 0 then 97/699 else 718/699

theorem cc_Vinf_pi (s : Fin 2) : Vinf ccMDP (ccF.toPolicy ccTheta) s = ccV s := by
  refine Vinf_eq_of_bellman ccMDP _ cc_hr cc_γ₀ cc_γ₁ ccV ?_ s
  intro x
  rw [Fin.sum_univ_four]
  simp only [cc_pi, Fin.sum_univ_two, ccMDP_P]
  show ccV x = _
  simp only [ccMDP_r, ccMDP_gamma]
  unfold ccV ccW ccZ ccT ccR
  fin_cases x <;> norm_num [Fin.ext_iff]

/-! ### The occupancies -/

theorem cc_step_pi (x s' : Fin 2) :
    step ccMDP (ccF.toPolicy ccTheta) x s'
      = if x = 0 then (if s' = 0 then 1/4 else 3/4)
        else (if s' = 0 then 2/15 else 13/15) := by
  unfold step
  rw [Fin.sum_univ_four]
  simp only [cc_pi, ccMDP_P]
  unfold ccW ccZ ccT
  fin_cases x <;> fin_cases s' <;> norm_num [Fin.ext_iff]

/-- `d^π(s₀, s)`. -/
noncomputable def ccDinfPi (s₀ s : Fin 2) : ℝ :=
  if s = 0 then (if s₀ = 0 then 752/699 else 32/699)
  else (if s₀ = 0 then 60/233 else 300/233)

theorem cc_dinf_pi (s₀ s : Fin 2) :
    dinf ccMDP (ccF.toPolicy ccTheta) s₀ s = ccDinfPi s₀ s := by
  refine dinf_eq_of_fix ccMDP _ cc_γ₀ cc_γ₁ s (fun x => ccDinfPi x s) ?_ s₀
  intro x
  rw [Fin.sum_univ_two]
  simp only [cc_step_pi]
  unfold ccDinfPi ccMDP
  fin_cases x <;> fin_cases s <;> norm_num

theorem cc_dinfDist_pi (s : Fin 2) :
    dinfDist ccMDP (ccF.toPolicy ccTheta) ccMu s
      = if s = 0 then 104/699 else 276/233 := by
  unfold dinfDist
  rw [Fin.sum_univ_two, cc_dinf_pi, cc_dinf_pi, ccMu_apply, ccMu_apply]
  unfold ccDinfPi
  fin_cases s <;> norm_num

theorem cc_step_pistar (x s' : Fin 2) :
    step ccMDP ccPistar x s'
      = if x = 0 then (if s' = 0 then 1/2 else 1/2)
        else (if s' = 0 then 1/6 else 5/6) := by
  unfold step
  rw [Fin.sum_univ_four]
  simp only [ccPistar_apply, ccMDP_P]
  unfold ccT
  fin_cases x <;> fin_cases s' <;> norm_num [Fin.ext_iff]

/-- `d^{πstar}(s₀, s)`. -/
noncomputable def ccDinfStar (s₀ s : Fin 2) : ℝ :=
  if s = 0 then (if s₀ = 0 then 38/33 else 2/33)
  else (if s₀ = 0 then 2/11 else 14/11)

theorem cc_dinf_pistar (s₀ s : Fin 2) :
    dinf ccMDP ccPistar s₀ s = ccDinfStar s₀ s := by
  refine dinf_eq_of_fix ccMDP _ cc_γ₀ cc_γ₁ s (fun x => ccDinfStar x s) ?_ s₀
  intro x
  rw [Fin.sum_univ_two]
  simp only [cc_step_pistar]
  unfold ccDinfStar ccMDP
  fin_cases x <;> fin_cases s <;> norm_num

theorem cc_dinfDist_pistar (s : Fin 2) :
    dinfDist ccMDP ccPistar ccMu s = if s = 0 then 28/165 else 64/55 := by
  unfold dinfDist
  rw [Fin.sum_univ_two, cc_dinf_pistar, cc_dinf_pistar, ccMu_apply, ccMu_apply]
  unfold ccDinfStar
  fin_cases s <;> norm_num

/-! ### `mismatchCoeff = 56/33` -/

theorem cc_mismatch : mismatchCoeff ccMDP ccPistar ccMu = 56/33 := by
  have hval : ∀ s : Fin 2, dinfDist ccMDP ccPistar ccMu s / ccMu s
      = if s = 0 then 56/33 else 128/99 := by
    intro s
    rw [cc_dinfDist_pistar, ccMu_apply]
    fin_cases s <;> norm_num
  unfold mismatchCoeff
  refine le_antisymm (ciSup_le fun s => ?_) ?_
  · rw [hval s]; fin_cases s <;> norm_num
  · have := le_ciSup (bddAbove_mismatch ccMDP ccPistar ccMu) (0 : Fin 2)
    rw [hval 0] at this; simpa using this

/-! ### The advantages at `a*` -/

theorem cc_advInf_astar (s : Fin 2) :
    advInf ccMDP (ccF.toPolicy ccTheta) s (ccAstar s)
      = if s = 0 then 835/932 else 7/932 := by
  show ccMDP.r s (ccAstar s)
      + ccMDP.γ * (∑ s', (ccMDP.P s (ccAstar s)) s' * Vinf ccMDP (ccF.toPolicy ccTheta) s')
      - Vinf ccMDP (ccF.toPolicy ccTheta) s = _
  rw [Fin.sum_univ_two, cc_Vinf_pi, cc_Vinf_pi, cc_Vinf_pi]
  simp only [ccMDP_P, ccMDP_r, ccMDP_gamma]
  unfold ccV ccAstar ccT ccR
  fin_cases s <;> norm_num [Fin.ext_iff]

/-! ### `⨅_s π(a*(s)|s) = 1/16` -/

theorem cc_pi_astar (s : Fin 2) :
    (ccF.toPolicy ccTheta s) (ccAstar s) = if s = 0 then 1/16 else 2/15 := by
  rw [cc_pi]
  unfold ccW ccZ ccAstar
  fin_cases s <;> norm_num [Fin.ext_iff]

theorem cc_iInf : (⨅ s : Fin 2, (ccF.toPolicy ccTheta s) (ccAstar s)) = 1/16 := by
  have hbdd : BddBelow (Set.range fun s : Fin 2 => (ccF.toPolicy ccTheta s) (ccAstar s)) :=
    ⟨0, by rintro y ⟨s, rfl⟩; exact (ccF.toPolicy ccTheta s).nonneg _⟩
  refine le_antisymm ?_ ?_
  · have := ciInf_le hbdd (0 : Fin 2)
    rw [cc_pi_astar 0] at this; simpa using this
  · refine le_ciInf fun s => ?_
    rw [cc_pi_astar]; fin_cases s <;> norm_num

/-! ### The two sides -/

theorem cc_VstarDist : VstarDist ccMDP ccMu = 4/3 := by
  unfold VstarDist
  rw [Fin.sum_univ_two, cc_Vstar, cc_Vstar, ccMu_apply, ccMu_apply]
  norm_num

theorem cc_VinfDist : VinfDist ccMDP (ccF.toPolicy ccTheta) ccMu = 6559/6990 := by
  unfold VinfDist
  rw [Fin.sum_univ_two, cc_Vinf_pi, cc_Vinf_pi, ccMu_apply, ccMu_apply]
  unfold ccV
  norm_num

theorem cc_lhs :
    (⨅ s : Fin 2, (ccF.toPolicy ccTheta s) (ccAstar s))
        * (VstarDist ccMDP ccMu - VinfDist ccMDP (ccF.toPolicy ccTheta) ccMu)
      = 2761/111840 := by
  rw [cc_iInf, cc_VstarDist, cc_VinfDist]; norm_num

theorem cc_rhs :
    mismatchCoeff ccMDP ccPistar ccMu
        * ∑ s, |dinfDist ccMDP (ccF.toPolicy ccTheta) ccMu s
            * ((ccF.toPolicy ccTheta s) (ccAstar s)
              * advInf ccMDP (ccF.toPolicy ccTheta) s (ccAstar s))|
      = 434021/26873055 := by
  rw [cc_mismatch, Fin.sum_univ_two, cc_dinfDist_pi, cc_dinfDist_pi,
    cc_pi_astar, cc_pi_astar, cc_advInf_astar, cc_advInf_astar]
  norm_num [abs_of_nonneg]

/-- **The witness refutes the corrected aggregate bound.** -/
theorem cc_refutes_instance :
    ¬ ((⨅ s : Fin 2, (ccF.toPolicy ccTheta s) (ccAstar s))
          * (VstarDist ccMDP ccMu - VinfDist ccMDP (ccF.toPolicy ccTheta) ccMu)
        ≤ mismatchCoeff ccMDP ccPistar ccMu
            * ∑ s, |dinfDist ccMDP (ccF.toPolicy ccTheta) ccMu s
                * ((ccF.toPolicy ccTheta s) (ccAstar s)
                  * advInf ccMDP (ccF.toPolicy ccTheta) s (ccAstar s))|) := by
  rw [cc_lhs, cc_rhs]
  norm_num

/-- **`g1_aggregate_bound`, as frozen in `Goal.lean` on 2026-08-22, is FALSE.**

The hypothesis is the frozen statement universally closed over its binders,
**with the corrected `hastar : ∀ s, 0 < (πstar s) (astar s)`**.  No lemma of
that type can exist.

Every frozen hypothesis holds on the witness: `hF` (`cc_hF`, tabular softmax),
`hr` (`cc_hr`), `hγ₀`/`hγ₁`, `hμ` (`cc_hmu`), `hstar` (`cc_hstar`), and the new
`hastar` (`cc_hastar`).  The conclusion reads

    2761/111840  ≤  434021/26873055,

i.e. `0.024687 ≤ 0.016151`, false by a factor of `1.529`. -/
theorem g1c_aggregate_bound_general_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A)
        (_ : DecidableEq S) (_ : DecidableEq A) (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (μ : Dist S), (∀ s, 0 < μ s) →
        ∀ (πstar : Policy S A), (∀ s, Vinf M πstar s = Vstar M s) →
        ∀ (astar : S → A), (∀ s, 0 < (πstar s) (astar s)) →
        ∀ (θ : EuclideanSpace ℝ (S × A)),
          (⨅ s : S, (F.toPolicy θ s) (astar s))
              * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
            ≤ mismatchCoeff M πstar μ
                * ∑ s, |dinfDist M (F.toPolicy θ) μ s
                    * ((F.toPolicy θ s) (astar s)
                      * advInf M (F.toPolicy θ) s (astar s))|) := by
  intro h
  exact cc_refutes_instance
    (h (Fin 2) (Fin 4) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance ccMDP ccF cc_hF cc_hr cc_γ₀ cc_γ₁
      ccMu cc_hmu ccPistar cc_hstar ccAstar cc_hastar ccTheta)

#print axioms g1c_aggregate_bound_general_false

/-! ### The tie that does it

The support of `πstar` at state `1` is `{1, 3}`, both `Q*`-optimal
(`Q*(1,1) = Q*(1,3) = 4/3 = V*(1)`), but their `π`-advantages differ by two
orders of magnitude. -/

theorem cc_advInf_one_three :
    advInf ccMDP (ccF.toPolicy ccTheta) 1 3 = 107/466 := by
  show ccMDP.r 1 3
      + ccMDP.γ * (∑ s', (ccMDP.P 1 3) s' * Vinf ccMDP (ccF.toPolicy ccTheta) s')
      - Vinf ccMDP (ccF.toPolicy ccTheta) 1 = _
  rw [Fin.sum_univ_two]
  rw [cc_Vinf_pi 0, cc_Vinf_pi 1]
  simp only [ccMDP_P, ccMDP_r, ccMDP_gamma]
  unfold ccV ccT ccR
  norm_num [Fin.ext_iff]

/-- The frozen `astar` sits on the *small* advantage of a `Q*`-tied pair:
`A^π(1, a*(1)) = 7/932` while `A^π(1,3) = 107/466 = 214/932`, thirty times
larger, and `πstar` puts `5/6` of its mass there. -/
theorem cc_tie_gap :
    advInf ccMDP (ccF.toPolicy ccTheta) 1 (ccAstar 1)
      < advInf ccMDP (ccF.toPolicy ccTheta) 1 3 := by
  rw [cc_advInf_astar, cc_advInf_one_three]
  norm_num

end G1cCounterexample

/-! ## Goal B (`g1_lojasiewicz`) is NOT refuted by this

The reduction `g1_lojasiewicz_of_aggregate` only ever *weakens* toward the
gradient: it composes the aggregate bound with `sum_abs_adv_le_norm` and a
division by `√|S| · mism`.  So a false aggregate bound does not make G1 false —
it makes the route through it unavailable.

On this very witness G1 holds with a factor-of-24 margin:

```
c/(√2 · mism) · (V*_μ - V^π_μ) = 0.01029     vs.     ‖∇V‖ = 0.24849
```

and a 100 000-MDP tie-seeded sweep (integer reward grids, exact-tie optimal
policies, `astar` drawn from `supp πstar`, `μ` skewed to a ninth power, softmax
temperatures over two decades) found a maximum `lhs/rhs` of `0.76` with zero
violations.  G1 is left **open**, not refuted.

### What the refutation costs the G1 proof

`g1_lojasiewicz_of_aggregate` is now dead as a route, and so are the four
factorizations `G1b.lean` catalogues.  What survives from `G1Agg.lean` is the
change-of-measure half (`iInf_mul_dinfDist_le`,
`iInf_mul_sum_dinfDistStar_adv_le`), which is unconditional and does not depend
on the aggregate bound.  The obstruction is unchanged and now confirmed to be
*independent of how `astar` is constrained*, short of constraining it to
maximize `A^π` over `supp πstar`:

```
V*_μ - V^π_μ  ≤  ∑_s d^{πstar}_μ(s) · A^π(s, a*(s))                    (‡)
```

`(‡)` was checked directly under the corrected `hastar` and is **also false** —
a 30 000-MDP sweep found violations up to `2.44` in absolute terms, and the
per-state form `∑_a πstar(a|s)·A^π(s,a) ≤ A^π(s,a*(s))` fails by up to `0.85`.
So the correction to `hastar` does not restore `(‡)`, which is why the aggregate
bound falls again.

### What a true statement in this family looks like

Numerically, three aggregate right-hand sides survive the same 30 000-MDP sweep
where the frozen one fails (max violation `≤ 4e-14` each):

* `c · sub ≤ mism · ∑_s ∑_a |d^π_μ(s)·π(a|s)·A^π(s,a)|` — the full `ℓ¹` norm of
  the gradient.  True, but `‖g‖₁ ≤ √(|S||A|)·‖g‖₂`, so it buys `√(|S||A|)`, not
  the `√|S|` the frozen G1 needs.
* `c · sub ≤ mism · ∑_s |d^π_μ(s)·π(b(s)|s)·A^π(s,b(s))|` with
  `b(s) = argmax_a π(a|s)·A^π(s,a)` — one action per state, so
  `sum_abs_adv_le_norm` applies verbatim and this **does** give `√|S|`.  It is
  the frozen statement with `astar` replaced by the `π`-weighted-advantage
  maximizer rather than a `πstar`-support member.
* `sub ≤ mism · ∑_s d^π_μ(s)·max_a A^π(s,a)`.

The second is the natural repair: it is exactly what Mei's proof needs and what
`hastar` was trying and failing to encode.  Its per-state form is false (checked:
violations up to `0.59`), so proving it is still a genuinely cross-state
argument — but unlike the frozen `astar` version it is not refutable by a tie,
because `b` is defined from `π` and `A^π` directly. -/


/-! ## The replacement reduction: G1 from a `π`-weighted-advantage selector

`g1_lojasiewicz_of_aggregate` is dead as a route (its hypothesis is
`g1_aggregate_bound`, refuted above).  What replaces it is the observation that
`sum_abs_adv_le_norm` in `Proofs.G1` is stated for an **arbitrary**
`astar : S → A` — it never uses `hastar`, only that one action is picked per
state, which is what makes the test vector's norm `√|S|`.

So G1 reduces to the same aggregate inequality with the frozen `astar` replaced
by *any* selector `b : S → A` of the prover's choosing.  Unlike the frozen
version this cannot be refuted by a `Q*` tie: `b` is chosen from `π` and `A^π`
rather than constrained through `πstar`.

Numerically the right choice is `b(s) ∈ argmax_a π(a|s)·A^π(s,a)`, for which

```
c · (V*_μ - V^π_μ)  ≤  mism · ∑_s |d^π_μ(s)·π(b(s)|s)·A^π(s,b(s))|          (R)
```

held over 75 000 tie-seeded MDPs with a maximum violation of `1.7e-13` (zero),
and is **tight** — the observed `lhs/rhs` reaches `0.9999999999`.  The frozen
`astar` version of the same inequality is exactly what
`g1c_aggregate_bound_general_false` refutes, and the two differ only in which
action each state contributes.

`(R)` is still a genuinely cross-state statement: its per-state form
`c·d^{πstar}_μ(s)·∑_a πstar(a|s)·A^π(s,a) ≤ mism·|d^π_μ(s)·π(b(s)|s)·A^π(s,b(s))|`
is false (violations up to `0.59`).  So this reduction moves the obstruction to
a statement that is at least *not refutable by the tie defect*, which the frozen
one demonstrably is. -/

section Reduction

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

open scoped BigOperators

/-- **G1 reduced to a free-selector aggregate bound.**

The frozen `g1_lojasiewicz` statement, with the corrected
`hastar : ∀ s, 0 < (πstar s) (astar s)`, follows from the aggregate inequality
for **any** selector `b : S → A` — not necessarily the frozen `astar`.

This supersedes `g1_lojasiewicz_of_aggregate`, whose hypothesis
(`b = astar`) is refuted by `g1c_aggregate_bound_general_false` above.  The
gradient step `sum_abs_adv_le_norm` is indifferent to which action each state
contributes, so the extra freedom is free. -/
theorem g1_lojasiewicz_of_selector (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (θ : E S A)
    (b : S → A)
    (hsel : (⨅ s : S, (F.toPolicy θ s) (astar s))
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ mismatchCoeff M πstar μ
        * ∑ s, |dinfDist M (F.toPolicy θ) μ s
            * ((F.toPolicy θ s) (b s) * advInf M (F.toPolicy θ) s (b s))|) :
    (⨅ s : S, (F.toPolicy θ s) (astar s))
        / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖ := by
  classical
  set π := F.toPolicy θ with hπ
  set c : ℝ := ⨅ s : S, (π s) (astar s) with hc
  set mism : ℝ := mismatchCoeff M πstar μ with hmism
  have hmpos : 0 < mism := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hSpos : 0 < Real.sqrt (Fintype.card S) := by
    have : 0 < (Fintype.card S : ℝ) := by
      have := Fintype.card_pos_iff.mpr ‹Nonempty S›
      exact_mod_cast this
    exact Real.sqrt_pos.mpr this
  -- `sum_abs_adv_le_norm` is stated for an arbitrary selector; apply it at `b`.
  have hgrad := sum_abs_adv_le_norm M F hF hr hγ₀ hγ₁ μ θ b
  have hchain : c * (VstarDist M μ - VinfDist M π μ)
      ≤ mism * (Real.sqrt (Fintype.card S)
          * ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖) :=
    le_trans hsel (mul_le_mul_of_nonneg_left hgrad hmpos.le)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc c * (VstarDist M μ - VinfDist M π μ)
      ≤ mism * (Real.sqrt (Fintype.card S)
          * ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖) := hchain
    _ = ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖
          * (Real.sqrt (Fintype.card S) * mism) := by ring

/-- The frozen `astar` is one admissible selector, so the old reduction is the
`b = astar` instance of the new one.  Recorded to make the strengthening
explicit: `g1_lojasiewicz_of_selector` is strictly more permissive, and its
`b = astar` instance is precisely the hypothesis just refuted. -/
theorem g1_lojasiewicz_of_selector_at_astar (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (θ : E S A)
    (hagg : (⨅ s : S, (F.toPolicy θ s) (astar s))
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ mismatchCoeff M πstar μ
        * ∑ s, |dinfDist M (F.toPolicy θ) μ s
            * ((F.toPolicy θ s) (astar s) * advInf M (F.toPolicy θ) s (astar s))|) :
    (⨅ s : S, (F.toPolicy θ s) (astar s))
        / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖ :=
  g1_lojasiewicz_of_selector M F hF hr hγ₀ hγ₁ μ hμ πstar hstar astar hastar θ astar hagg

#print axioms g1_lojasiewicz_of_selector

end Reduction

end Proofs
end PolicyGradient
