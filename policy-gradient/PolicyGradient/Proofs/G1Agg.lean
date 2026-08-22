/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1b

/-!
# G1Agg — the aggregate Łojasiewicz bound is FALSE

Work file for the frozen goal `g1_aggregate_bound` (`@[infra "G1-aggregate"]`),
the inequality `g1_lojasiewicz_of_aggregate` reduces G1 to.

**Result: refuted.**  `g1_aggregate_bound_general_false` is machine-checked with
axioms `[propext, Classical.choice, Quot.sound]`.

## The witness

`S = Fin 2`, `A = Fin 4`, `γ = 1/5`.

```
r = ![![0, 1/2, 1, 1], ![1, 0, -1, 1]]
P s a = the two-point distribution with mass agP0 s a on state 0, where
agP0 = ![![1, 1/4, 0, 1], ![2/5, 1/2, 1/10, 1/4]]
μ = (9/10, 1/10)
θ = log ![![1, 5, 2, 12], ![2, 12, 5, 1]]   so   π = ![![1,5,2,12], ![2,12,5,1]]/20
πstar = δ₃ everywhere,   astar = ![2, 0]
```

Every reward is `± 1` or `± 1/2`, so `hr` holds; `1/(1-γ) = 5/4` and `πstar`
attains it, so `V* = (5/4, 5/4)` and `hstar` holds.  Because `V*` is *constant*
across states, `Q*(s,a) = r(s,a) + γ·(5/4)` depends only on the reward, so

```
Q* = ![![1/4, 3/4, 5/4, 5/4], ![5/4, 1/4, -3/4, 5/4]]
```

has a **genuine tie at state `0`** between actions `2` and `3` (both carry
`r = 1`), and another at state `1` between `0` and `3`.  `hastar` therefore
holds for `astar = ![2, 0]` even though `πstar` sits on action `3`.

Constant `V*` is the cleanest source of exact `Q*` ties, and it is why random
MDPs never find this: generic rewards give no ties at all.  The counterexample
was found by first locating a floating-point violation in a tie-seeded sweep,
then reading off which structural feature produced it (`V*` constant) and
re-searching over small exact rationals with that structure imposed.

The witness policy `π` is exactly the tabular softmax at
`θ(s,a) = log(w s a)`: `exp` and `log` cancel (`Real.exp_log`, weights
positive), the denominators are `20` at both states, so `π` is exactly rational
and `hF` holds by `rfl`.

## The numbers

```
V^π       = (57323/59712, -1877/59712)
d^π_μ     = (7955/7464, 1375/7464)
d^{πstar}_μ = (77/68, 2/17)          mismatchCoeff = 385/306
A^π(s,a*(s)) = (839/24880, 27479/24880)
π(a*(s)|s)   = (1/10, 1/10)          ⨅_s π(a*(s)|s) = 1/10
```

so the frozen conclusion reads

```
23237/597120  ≤  114108533/3788368128,    i.e.  0.03892 ≤ 0.03012,
```

false by a factor of `1.292`.

## Why it fails, and what that says about G1

The intended AKM chain has two steps.  The **change of measure** is fine and is
proved here unconditionally (`iInf_mul_dinfDist_le`, `iInf_mul_sum_dinfDistStar_adv_le`):
`c ≤ π(a*(s)|s)`, `d^{πstar}_μ(s) ≤ mism·μ(s)`, `μ(s) ≤ d^π_μ(s)` compose to

```
c · ∑_s d^{πstar}_μ(s)·A^π(s,a*(s))  ≤  mism · ∑_s |d^π_μ(s)·π(a*(s)|s)·A^π(s,a*(s))|
```

termwise (negative-advantage states have a nonpositive left term).  So the whole
remaining gap is the **performance-difference step**

```
V*_μ - V^π_μ  ≤  ∑_s d^{πstar}_μ(s) · A^π(s, a*(s)),
```

which is the exact performance-difference identity with `∑_a πstar(a|s)·A^π(s,a)`
replaced by `A^π(s, a*(s))`.  Under a `Q*` tie those are different numbers.  On
the witness, at state `0` the tie gives `A^π(0, a*(0)) = A^π(0,2) = 839/24880
≈ 0.034` while `A^π(0, 3) = 17317/74640 ≈ 0.232` — a factor of thirteen — and
state `0` carries `d^{πstar}_μ(0) = 77/68`, almost all of the occupancy.

This is the **same defect for the third time**: it already refuted the per-state
`hgreedy` (`g1_lojasiewicz_of_greedy`) and the cross-state form
(`advantage_cross_state_general_false`).  Aggregation does not repair it, and
neither does the absolute value, because the loss is at a state where the
advantage is *positive but too small*, not one where a sign flips.

Two natural repairs are **also refuted by this same witness**: replacing `mism`
by `mism/(1-γ)` gives `0.03765 < 0.03892`, and by `mism²` gives
`0.03790 < 0.03892`.  Both fall short because the needed factor over `mism` is
`1.292`, larger than `1/(1-γ) = 1.25` and than `mism = 1.258`.

A statement in this family can only be true if it constrains `astar` and
`πstar` to agree on ties — e.g. requiring `πstar s = δ_{astar s}`, or
`A^π(s, astar s) = ⨆ {A^π(s,a) : Q*(s,a) = V*(s)}`.  With `astar` free, the tie
always admits a choice that hides the suboptimality behind a small advantage.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section AggCounterexample

open scoped BigOperators

/-- A two-point distribution: mass `p` on `0`, `1 - p` on `1`. -/
noncomputable def agD (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Dist (Fin 2) where
  prob j := if j = 0 then p else 1 - p
  nonneg j := by by_cases h : j = 0 <;> simp [h] <;> linarith
  sum_eq_one := by rw [Fin.sum_univ_two]; norm_num

@[simp] theorem agD_apply (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (j : Fin 2) :
    agD p hp hp1 j = if j = 0 then p else 1 - p := rfl

/-- The transition probability of landing in state `0`. -/
noncomputable def agP0 (s : Fin 2) (a : Fin 4) : ℝ :=
  if s = 0 then (if a = 0 then 1 else if a = 1 then 1/4 else if a = 2 then 0 else 1)
  else (if a = 0 then 2/5 else if a = 1 then 1/2 else if a = 2 then 1/10 else 1/4)

/-- The reward. -/
noncomputable def agR (s : Fin 2) (a : Fin 4) : ℝ :=
  if s = 0 then (if a = 0 then 0 else if a = 1 then 1/2 else 1)
  else (if a = 0 then 1 else if a = 1 then 0 else if a = 2 then -1 else 1)

@[simp] theorem agR_three (s : Fin 2) : agR s 3 = 1 := by
  unfold agR; by_cases h : s = 0 <;> simp [h] <;> norm_num

theorem agP0_nonneg (s : Fin 2) (a : Fin 4) : 0 ≤ agP0 s a := by
  unfold agP0; fin_cases s <;> fin_cases a <;> norm_num [Fin.ext_iff]

theorem agP0_le_one (s : Fin 2) (a : Fin 4) : agP0 s a ≤ 1 := by
  unfold agP0; fin_cases s <;> fin_cases a <;> norm_num [Fin.ext_iff]

/-- The witness MDP. -/
noncomputable def agMDP : FiniteMDP (Fin 2) (Fin 4) where
  P := fun s a => agD (agP0 s a) (agP0_nonneg s a) (agP0_le_one s a)
  r := agR
  γ := 1/5

@[simp] theorem agMDP_gamma : agMDP.γ = 1/5 := rfl

theorem agMDP_P (s : Fin 2) (a : Fin 4) (s' : Fin 2) :
    (agMDP.P s a) s' = if s' = 0 then agP0 s a else 1 - agP0 s a := rfl

theorem ag_γ₀ : (0:ℝ) ≤ agMDP.γ := by norm_num [agMDP]
theorem ag_γ₁ : agMDP.γ < 1 := by norm_num [agMDP]

theorem ag_hr : ∀ s a, |agMDP.r s a| ≤ 1 := by
  intro s a
  show |agR s a| ≤ 1
  unfold agR
  fin_cases s <;> fin_cases a <;> norm_num [Fin.ext_iff]

/-- `πstar` — the deterministic policy taking action `3` everywhere. -/
noncomputable def agPistar : Policy (Fin 2) (Fin 4) := fun _ => pointMass 3

/-- The start distribution `μ = (9/10, 1/10)`. -/
noncomputable def agMu : Dist (Fin 2) := agD (9/10) (by norm_num) (by norm_num)

@[simp] theorem agMu_apply (s : Fin 2) :
    agMu s = if s = 0 then 9/10 else 1/10 := by
  show (if s = 0 then (9:ℝ)/10 else 1 - 9/10) = _
  by_cases h : s = 0 <;> simp [h] <;> norm_num

theorem ag_hmu : ∀ s, 0 < agMu s := by
  intro s; rw [agMu_apply]; by_cases h : s = 0 <;> simp [h] <;> norm_num

/-- `a*` — the `Q*`-tied action `2` at state `0`, action `0` at state `1`. -/
noncomputable def agAstar : Fin 2 → Fin 4 := ![2, 0]


theorem agPistar_apply (s : Fin 2) (a : Fin 4) :
    (agPistar s) a = if a = 3 then 1 else 0 := rfl

/-! ### `V^{πstar} = (5/4, 5/4)` -/

theorem ag_Vinf_pistar (s : Fin 2) : Vinf agMDP agPistar s = 5/4 := by
  refine Vinf_eq_of_bellman agMDP agPistar ag_hr ag_γ₀ ag_γ₁ (fun _ => 5/4) ?_ s
  intro x
  show (5:ℝ)/4 = ∑ a, (agPistar x) a * (agMDP.r x a + agMDP.γ * ∑ s', (agMDP.P x a) s' * (5/4))
  rw [Fin.sum_univ_four]
  simp only [agPistar_apply, Fin.sum_univ_two, agMDP_P]
  norm_num [Fin.ext_iff]
  have hr3 : agMDP.r x 3 = 1 := agR_three x
  rw [hr3]; ring

/-! ### `V* = (5/4, 5/4)` — the reward bound `1/(1-γ) = 5/4` is attained. -/

theorem ag_Vstar (s : Fin 2) : Vstar agMDP s = 5/4 := by
  have hb : ∀ π : Policy (Fin 2) (Fin 4), Vinf agMDP π s ≤ 5/4 := by
    intro π
    have := abs_Vinf_le agMDP π 1 zero_le_one ag_hr ag_γ₀ ag_γ₁ s
    have h2 : (1:ℝ) / (1 - agMDP.γ) = 5/4 := by norm_num [agMDP]
    rw [h2] at this
    exact (abs_le.mp this).2
  refine le_antisymm (ciSup_le hb) ?_
  have hbdd : BddAbove (Set.range fun π : Policy (Fin 2) (Fin 4) => Vinf agMDP π s) :=
    ⟨5/4, by rintro y ⟨π, rfl⟩; exact hb π⟩
  have := le_ciSup hbdd agPistar
  rwa [ag_Vinf_pistar s] at this

theorem ag_hstar : ∀ s, Vinf agMDP agPistar s = Vstar agMDP s := by
  intro s; rw [ag_Vinf_pistar, ag_Vstar]

/-- `Q*(s, a*(s)) = V*(s)` — at state `0` this uses the tie between actions `2`
and `3`, at state `1` the tie between actions `0` and `3`. -/
theorem ag_hastar : ∀ s, Qstar agMDP s (agAstar s) = Vstar agMDP s := by
  intro s
  rw [ag_Vstar]
  show agMDP.r s (agAstar s) + agMDP.γ * ∑ s', (agMDP.P s (agAstar s)) s' * Vstar agMDP s' = 5/4
  rw [Fin.sum_univ_two, ag_Vstar, ag_Vstar]
  simp only [agMDP_P]
  have key : agMDP.r s (agAstar s) = 1 := by
    show agR s (agAstar s) = 1
    unfold agR agAstar
    fin_cases s <;> norm_num [Fin.ext_iff]
  norm_num [key]
  ring


/-! ### The tabular softmax family and the witness parameter `θ` -/

/-- The tabular softmax family on `Fin 2 × Fin 4`. -/
noncomputable def agF : VecPolicy (Fin 2) (Fin 4) (E (Fin 2) (Fin 4)) where
  toPolicy := fun θ s => softmax (fun a => θ (s, a))
  dπ := fun θ s a => fderiv ℝ (fun t : E (Fin 2) (Fin 4) => (softmax (fun a' => t (s, a'))) a) θ
  hasFDeriv := fun θ s a => by
    refine (softmax_diff (E := E (Fin 2) (Fin 4)) (fun t a' => t (s, a')) ?_ a θ).hasFDerivAt
    intro a'
    exact (EuclideanSpace.proj (s, a') :
      E (Fin 2) (Fin 4) →L[ℝ] ℝ).differentiable

theorem ag_hF : ∀ θ s a, (agF.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a :=
  fun _ _ _ => rfl

/-- The softmax **weights**: `exp θ (s,a)`.  Integer weights make the resulting
policy exactly rational. -/
noncomputable def agW (s : Fin 2) (a : Fin 4) : ℝ :=
  if s = 0 then (if a = 0 then 1 else if a = 1 then 5 else if a = 2 then 2 else 12)
  else (if a = 0 then 2 else if a = 1 then 12 else if a = 2 then 5 else 1)

theorem agW_pos (s : Fin 2) (a : Fin 4) : 0 < agW s a := by
  unfold agW; fin_cases s <;> fin_cases a <;> norm_num [Fin.ext_iff]

/-- The witness parameter: the logits are the logs of the weights. -/
noncomputable def agTheta : E (Fin 2) (Fin 4) :=
  (EuclideanSpace.equiv (Fin 2 × Fin 4) ℝ).symm (fun p => Real.log (agW p.1 p.2))

theorem agTheta_apply (s : Fin 2) (a : Fin 4) : agTheta (s, a) = Real.log (agW s a) := by
  simp [agTheta, EuclideanSpace.equiv]

theorem ag_exp_theta (s : Fin 2) (a : Fin 4) : Real.exp (agTheta (s, a)) = agW s a := by
  rw [agTheta_apply, Real.exp_log (agW_pos s a)]

/-- The witness policy `π = softmax(agTheta)`, exactly rational. -/
theorem ag_pi (s : Fin 2) (a : Fin 4) :
    (agF.toPolicy agTheta s) a = agW s a / 20 := by
  rw [ag_hF, softmax_apply]
  have hden : ∑ a' : Fin 4, Real.exp (agTheta (s, a')) = 20 := by
    rw [Fin.sum_univ_four]
    simp only [ag_exp_theta]
    unfold agW
    fin_cases s <;> norm_num [Fin.ext_iff]
  rw [ag_exp_theta, hden]


/-! ### `V^π = (57323/59712, -1877/59712)` -/

/-- The witness value function, as an explicit vector. -/
noncomputable def agV (s : Fin 2) : ℝ := if s = 0 then 57323/59712 else -1877/59712

theorem ag_Vinf_pi (s : Fin 2) : Vinf agMDP (agF.toPolicy agTheta) s = agV s := by
  refine Vinf_eq_of_bellman agMDP _ ag_hr ag_γ₀ ag_γ₁ agV ?_ s
  intro x
  rw [Fin.sum_univ_four]
  simp only [ag_pi, Fin.sum_univ_two, agMDP_P]
  show agV x = _
  unfold agV agW agP0 agMDP agR
  fin_cases x <;> norm_num [Fin.ext_iff]

/-! ### The occupancies -/

theorem ag_step_pi (x s' : Fin 2) :
    step agMDP (agF.toPolicy agTheta) x s'
      = if x = 0 then (if s' = 0 then 57/80 else 23/80)
        else (if s' = 0 then 151/400 else 249/400) := by
  unfold step
  rw [Fin.sum_univ_four]
  simp only [ag_pi, agMDP_P]
  unfold agW agP0
  fin_cases x <;> fin_cases s' <;> norm_num [Fin.ext_iff]

/-- `d^π(s₀, s)`. -/
noncomputable def agDinfPi (s₀ s : Fin 2) : ℝ :=
  if s = 0 then (if s₀ = 0 then 8755/7464 else 755/7464)
  else (if s₀ = 0 then 575/7464 else 8575/7464)

theorem ag_dinf_pi (s₀ s : Fin 2) :
    dinf agMDP (agF.toPolicy agTheta) s₀ s = agDinfPi s₀ s := by
  refine dinf_eq_of_fix agMDP _ ag_γ₀ ag_γ₁ s (fun x => agDinfPi x s) ?_ s₀
  intro x
  rw [Fin.sum_univ_two]
  simp only [ag_step_pi]
  unfold agDinfPi agMDP
  fin_cases x <;> fin_cases s <;> norm_num

theorem ag_dinfDist_pi (s : Fin 2) :
    dinfDist agMDP (agF.toPolicy agTheta) agMu s
      = if s = 0 then 7955/7464 else 1375/7464 := by
  unfold dinfDist
  rw [Fin.sum_univ_two, ag_dinf_pi, ag_dinf_pi, agMu_apply, agMu_apply]
  unfold agDinfPi
  fin_cases s <;> norm_num

theorem ag_step_pistar (x s' : Fin 2) :
    step agMDP agPistar x s'
      = if x = 0 then (if s' = 0 then 1 else 0)
        else (if s' = 0 then 1/4 else 3/4) := by
  unfold step
  rw [Fin.sum_univ_four]
  simp only [agPistar_apply, agMDP_P]
  unfold agP0
  fin_cases x <;> fin_cases s' <;> norm_num [Fin.ext_iff]

/-- `d^{πstar}(s₀, s)`. -/
noncomputable def agDinfStar (s₀ s : Fin 2) : ℝ :=
  if s = 0 then (if s₀ = 0 then 5/4 else 5/68) else (if s₀ = 0 then 0 else 20/17)

theorem ag_dinf_pistar (s₀ s : Fin 2) :
    dinf agMDP agPistar s₀ s = agDinfStar s₀ s := by
  refine dinf_eq_of_fix agMDP _ ag_γ₀ ag_γ₁ s (fun x => agDinfStar x s) ?_ s₀
  intro x
  rw [Fin.sum_univ_two]
  simp only [ag_step_pistar]
  unfold agDinfStar agMDP
  fin_cases x <;> fin_cases s <;> norm_num

theorem ag_dinfDist_pistar (s : Fin 2) :
    dinfDist agMDP agPistar agMu s = if s = 0 then 77/68 else 2/17 := by
  unfold dinfDist
  rw [Fin.sum_univ_two, ag_dinf_pistar, ag_dinf_pistar, agMu_apply, agMu_apply]
  unfold agDinfStar
  fin_cases s <;> norm_num


/-! ### `mismatchCoeff = 385/306` -/

theorem ag_mismatch : mismatchCoeff agMDP agPistar agMu = 385/306 := by
  have hval : ∀ s : Fin 2, dinfDist agMDP agPistar agMu s / agMu s
      = if s = 0 then 385/306 else 20/17 := by
    intro s
    rw [ag_dinfDist_pistar, agMu_apply]
    fin_cases s <;> norm_num
  unfold mismatchCoeff
  refine le_antisymm (ciSup_le fun s => ?_) ?_
  · rw [hval s]; fin_cases s <;> norm_num
  · have := le_ciSup (bddAbove_mismatch agMDP agPistar agMu) (0 : Fin 2)
    rw [hval 0] at this; simpa using this

/-! ### The advantages at `a*` -/

theorem ag_advInf_astar (s : Fin 2) :
    advInf agMDP (agF.toPolicy agTheta) s (agAstar s)
      = if s = 0 then 839/24880 else 27479/24880 := by
  show agMDP.r s (agAstar s)
      + agMDP.γ * (∑ s', (agMDP.P s (agAstar s)) s' * Vinf agMDP (agF.toPolicy agTheta) s')
      - Vinf agMDP (agF.toPolicy agTheta) s = _
  rw [Fin.sum_univ_two, ag_Vinf_pi, ag_Vinf_pi, ag_Vinf_pi]
  simp only [agMDP_P]
  unfold agV agAstar agP0 agMDP agR
  fin_cases s <;> norm_num [Fin.ext_iff]

/-! ### `⨅_s π(a*(s)|s) = 1/10` — both states give exactly `1/10`. -/

theorem ag_pi_astar (s : Fin 2) : (agF.toPolicy agTheta s) (agAstar s) = 1/10 := by
  rw [ag_pi]
  unfold agW agAstar
  fin_cases s <;> norm_num [Fin.ext_iff]

theorem ag_iInf : (⨅ s : Fin 2, (agF.toPolicy agTheta s) (agAstar s)) = 1/10 := by
  have : (fun s : Fin 2 => (agF.toPolicy agTheta s) (agAstar s)) = fun _ => (1:ℝ)/10 :=
    funext ag_pi_astar
  rw [this]
  exact ciInf_const

/-! ### The two sides -/

theorem ag_VstarDist : VstarDist agMDP agMu = 5/4 := by
  unfold VstarDist
  rw [Fin.sum_univ_two, ag_Vstar, ag_Vstar, agMu_apply, agMu_apply]
  norm_num

theorem ag_VinfDist : VinfDist agMDP (agF.toPolicy agTheta) agMu = 51403/59712 := by
  unfold VinfDist
  rw [Fin.sum_univ_two, ag_Vinf_pi, ag_Vinf_pi, agMu_apply, agMu_apply]
  unfold agV
  norm_num

theorem ag_lhs :
    (⨅ s : Fin 2, (agF.toPolicy agTheta s) (agAstar s))
        * (VstarDist agMDP agMu - VinfDist agMDP (agF.toPolicy agTheta) agMu)
      = 23237/597120 := by
  rw [ag_iInf, ag_VstarDist, ag_VinfDist]; norm_num

theorem ag_rhs :
    mismatchCoeff agMDP agPistar agMu
        * ∑ s, |dinfDist agMDP (agF.toPolicy agTheta) agMu s
            * ((agF.toPolicy agTheta s) (agAstar s)
              * advInf agMDP (agF.toPolicy agTheta) s (agAstar s))|
      = 114108533/3788368128 := by
  rw [ag_mismatch, Fin.sum_univ_two, ag_dinfDist_pi, ag_dinfDist_pi,
    ag_pi_astar, ag_pi_astar, ag_advInf_astar, ag_advInf_astar]
  norm_num [abs_of_nonneg]

/-- **The witness refutes the frozen aggregate bound.** -/
theorem ag_refutes_instance :
    ¬ ((⨅ s : Fin 2, (agF.toPolicy agTheta s) (agAstar s))
          * (VstarDist agMDP agMu - VinfDist agMDP (agF.toPolicy agTheta) agMu)
        ≤ mismatchCoeff agMDP agPistar agMu
            * ∑ s, |dinfDist agMDP (agF.toPolicy agTheta) agMu s
                * ((agF.toPolicy agTheta s) (agAstar s)
                  * advInf agMDP (agF.toPolicy agTheta) s (agAstar s))|) := by
  rw [ag_lhs, ag_rhs]
  norm_num


/-- **`g1_aggregate_bound`, as frozen in `Goal.lean`, is FALSE.**

The hypothesis below is the frozen statement universally closed over its
binders.  No lemma of that type can exist.

Every frozen hypothesis holds on the witness: `hF` (`ag_hF`, tabular softmax),
`hr` (`ag_hr`), `hγ₀`/`hγ₁`, `hastar` (`ag_hastar`), `hμ` (`ag_hmu`), `hstar`
(`ag_hstar`).  The conclusion reads

    23237/597120  ≤  114108533/3788368128,

i.e. `0.0389 ≤ 0.0301`, which is false by a factor of `1.29`. -/
theorem g1_aggregate_bound_general_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A)
        (_ : DecidableEq S) (_ : DecidableEq A) (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A)
        (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (astar : S → A), (∀ s, Qstar M s (astar s) = Vstar M s) →
        ∀ (μ : Dist S), (∀ s, 0 < μ s) →
        ∀ (πstar : Policy S A), (∀ s, Vinf M πstar s = Vstar M s) →
        ∀ (θ : EuclideanSpace ℝ (S × A)),
          (⨅ s : S, (F.toPolicy θ s) (astar s))
              * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
            ≤ mismatchCoeff M πstar μ
                * ∑ s, |dinfDist M (F.toPolicy θ) μ s
                    * ((F.toPolicy θ s) (astar s)
                      * advInf M (F.toPolicy θ) s (astar s))|) := by
  intro h
  exact ag_refutes_instance
    (h (Fin 2) (Fin 4) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance agMDP agF ag_hF ag_hr ag_γ₀ ag_γ₁
      agAstar ag_hastar agMu ag_hmu agPistar ag_hstar agTheta)


/-! ### Two natural repairs fall to the same witness

Weakening the constant is not enough: the needed factor over `mismatchCoeff` is
`1.292`, while `1/(1-γ) = 5/4` and `mismatchCoeff = 385/306 ≈ 1.258`. -/

/-- Replacing `mism` by `mism/(1-γ)` does not repair the bound. -/
theorem ag_refutes_over_one_sub_gamma :
    ¬ ((⨅ s : Fin 2, (agF.toPolicy agTheta s) (agAstar s))
          * (VstarDist agMDP agMu - VinfDist agMDP (agF.toPolicy agTheta) agMu)
        ≤ mismatchCoeff agMDP agPistar agMu / (1 - agMDP.γ)
            * ∑ s, |dinfDist agMDP (agF.toPolicy agTheta) agMu s
                * ((agF.toPolicy agTheta s) (agAstar s)
                  * advInf agMDP (agF.toPolicy agTheta) s (agAstar s))|) := by
  have hR : ∑ s, |dinfDist agMDP (agF.toPolicy agTheta) agMu s
        * ((agF.toPolicy agTheta s) (agAstar s)
          * advInf agMDP (agF.toPolicy agTheta) s (agAstar s))|
      = 1481929/61901440 := by
    have h := ag_rhs
    rw [ag_mismatch] at h
    linarith
  rw [ag_lhs, hR, ag_mismatch]
  norm_num [agMDP]

/-- Replacing `mism` by `mism ^ 2` does not repair the bound either. -/
theorem ag_refutes_mism_sq :
    ¬ ((⨅ s : Fin 2, (agF.toPolicy agTheta s) (agAstar s))
          * (VstarDist agMDP agMu - VinfDist agMDP (agF.toPolicy agTheta) agMu)
        ≤ (mismatchCoeff agMDP agPistar agMu) ^ 2
            * ∑ s, |dinfDist agMDP (agF.toPolicy agTheta) agMu s
                * ((agF.toPolicy agTheta s) (agAstar s)
                  * advInf agMDP (agF.toPolicy agTheta) s (agAstar s))|) := by
  have hR : ∑ s, |dinfDist agMDP (agF.toPolicy agTheta) agMu s
        * ((agF.toPolicy agTheta s) (agAstar s)
          * advInf agMDP (agF.toPolicy agTheta) s (agAstar s))|
      = 1481929/61901440 := by
    have h := ag_rhs
    rw [ag_mismatch] at h
    linarith
  rw [ag_lhs, hR, ag_mismatch]
  norm_num

#print axioms g1_aggregate_bound_general_false
#print axioms ag_refutes_over_one_sub_gamma
#print axioms ag_refutes_mism_sq

end AggCounterexample

/-! ## What survives: the pointwise change-of-measure

The refutation above kills the aggregate bound, but one ingredient of the
intended AKM route is unconditionally true and is proved here, because any
repair of G1 will want it:

    c · d^{πstar}_μ(s)  ≤  mism · d^π_μ(s) · π(a*(s)|s)      for every `s`,

with `c = ⨅_s π(a*(s)|s)` and `mism = mismatchCoeff M πstar μ`.  The chain is
three one-line steps: `c ≤ π(a*(s)|s)` by `ciInf_le`, then
`d^{πstar}_μ(s) ≤ mism · μ(s)` (`mismatch_bound_proof_of_support`), then
`μ(s) ≤ d^π_μ(s)` (`mu_le_dinfDist`, the `t = 0` term of the occupancy).

Multiplying it by `A^π(s, a*(s))` and summing gives, **termwise**,

    c · ∑_s d^{πstar}_μ(s) · A^π(s,a*(s))
      ≤ mism · ∑_s |d^π_μ(s) · π(a*(s)|s) · A^π(s,a*(s))|,   (†)

since at states with `A^π(s,a*(s)) < 0` the left term is already `≤ 0`.  `(†)`
is exactly the frozen right-hand side, so the *entire* remaining gap in G1 is

    V*_μ - V^π_μ  ≤  ∑_s d^{πstar}_μ(s) · A^π(s, a*(s)).     (‡)

`(‡)` is the classical performance-difference identity **with `∑_a πstar(a|s)
A^π(s,a)` replaced by `A^π(s, a*(s))`**, and under a `Q*` tie those differ.
That substitution is where the witness above breaks the chain: at its state `0`
the tie lets `a* = 2` while `πstar` sits on action `3`, and
`A^π(0,2) = 839/24880 ≈ 0.034` is thirteen times smaller than
`A^π(0,3) = 17317/74640 ≈ 0.232`, so `(‡)` loses the bulk of the suboptimality
at the state carrying `d^{πstar}_μ(0) = 77/68`, most of the occupancy.

So `(‡)` — not the change of measure, not the aggregation — is the false step,
and it fails for exactly the tie reason that already killed `hgreedy`
(`g1_lojasiewicz_of_greedy`) and `advantage_cross_state`
(`advantage_cross_state_general_false`).  This is the third statement in the
`G1` family refuted by the same defect. -/

section Salvage

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **The pointwise change of measure**, unconditionally true. -/
theorem iInf_mul_dinfDist_le (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (astar : S → A)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (s : S) :
    (⨅ x : S, (π x) (astar x)) * dinfDist M πstar μ s
      ≤ mismatchCoeff M πstar μ * (dinfDist M π μ s * (π s) (astar s)) := by
  classical
  have hbdd : BddBelow (Set.range fun x : S => (π x) (astar x)) :=
    ⟨0, by rintro y ⟨x, rfl⟩; exact (π x).nonneg _⟩
  have hc : (⨅ x : S, (π x) (astar x)) ≤ (π s) (astar s) := ciInf_le hbdd s
  have hc0 : 0 ≤ ⨅ x : S, (π x) (astar x) := le_ciInf fun x => (π x).nonneg _
  have hstar : dinfDist M πstar μ s ≤ mismatchCoeff M πstar μ * μ s :=
    mismatch_bound_proof_of_support M hγ₀ hγ₁ πstar μ hμ s
  have hd0 : 0 ≤ dinfDist M πstar μ s := by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ πstar s₀ s)
  have hmu : μ s ≤ dinfDist M π μ s := mu_le_dinfDist M hγ₀ hγ₁ π μ s
  have hm0 : 0 < mismatchCoeff M πstar μ := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  calc (⨅ x : S, (π x) (astar x)) * dinfDist M πstar μ s
      ≤ (⨅ x : S, (π x) (astar x)) * (mismatchCoeff M πstar μ * μ s) :=
        mul_le_mul_of_nonneg_left hstar hc0
    _ ≤ (π s) (astar s) * (mismatchCoeff M πstar μ * μ s) :=
        mul_le_mul_of_nonneg_right hc
          (mul_nonneg hm0.le (μ.nonneg s))
    _ ≤ (π s) (astar s) * (mismatchCoeff M πstar μ * dinfDist M π μ s) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmu hm0.le) ((π s).nonneg _)
    _ = mismatchCoeff M πstar μ * (dinfDist M π μ s * (π s) (astar s)) := by ring

/-- **`(†)`** — the frozen right-hand side dominates the `d^{πstar}`-weighted
`a*`-advantage.  Proved termwise from `iInf_mul_dinfDist_le`, splitting on the
sign of `A^π(s, a*(s))`. -/
theorem iInf_mul_sum_dinfDistStar_adv_le (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (astar : S → A)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) :
    (⨅ x : S, (π x) (astar x))
        * ∑ s, dinfDist M πstar μ s * advInf M π s (astar s)
      ≤ mismatchCoeff M πstar μ
          * ∑ s, |dinfDist M π μ s * ((π s) (astar s) * advInf M π s (astar s))| := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  set c : ℝ := ⨅ x : S, (π x) (astar x) with hc
  set m : ℝ := mismatchCoeff M πstar μ with hm
  have hm0 : 0 < m := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hd : 0 ≤ dinfDist M π μ s := by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ π s₀ s)
  have hds : 0 ≤ dinfDist M πstar μ s := by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ πstar s₀ s)
  have hc0 : 0 ≤ c := le_ciInf fun x => (π x).nonneg _
  have hkey := iInf_mul_dinfDist_le M hγ₀ hγ₁ π πstar astar μ hμ s
  have habs : |dinfDist M π μ s * ((π s) (astar s) * advInf M π s (astar s))|
      = dinfDist M π μ s * (π s) (astar s) * |advInf M π s (astar s)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_nonneg ((π s).nonneg _)]
    ring
  rw [habs]
  rcases le_or_gt (advInf M π s (astar s)) 0 with hA | hA
  · have hL : c * (dinfDist M πstar μ s * advInf M π s (astar s)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc0 (mul_nonpos_of_nonneg_of_nonpos hds hA)
    have hR : 0 ≤ m * (dinfDist M π μ s * (π s) (astar s) * |advInf M π s (astar s)|) :=
      mul_nonneg hm0.le
        (mul_nonneg (mul_nonneg hd ((π s).nonneg _)) (abs_nonneg _))
    linarith
  · rw [abs_of_pos hA]
    calc c * (dinfDist M πstar μ s * advInf M π s (astar s))
        = (c * dinfDist M πstar μ s) * advInf M π s (astar s) := by ring
      _ ≤ (m * (dinfDist M π μ s * (π s) (astar s))) * advInf M π s (astar s) :=
          mul_le_mul_of_nonneg_right hkey hA.le
      _ = m * (dinfDist M π μ s * (π s) (astar s) * advInf M π s (astar s)) := by ring

#print axioms iInf_mul_sum_dinfDistStar_adv_le

end Salvage


end Proofs
end PolicyGradient
