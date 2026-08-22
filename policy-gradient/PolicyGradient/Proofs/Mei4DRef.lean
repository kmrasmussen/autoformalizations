/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Mei4D

/-!
# Mei4DRef — the interface condition `(†)` is not implied by optimality of `πstar`

`Mei4D` closes `mei_theorem4` modulo one extra hypothesis, `hdom`, the
*interface condition* that module's docstring calls `(†)`:

```
advGapInf M π πstar s ≤ advInf M π s (astar s)                       (†)
```

`Mei4D`'s prose asserts, without exhibiting a witness, that `(†)` is **not**
derivable from `mei_theorem4`'s own hypotheses — that `hastar` (`astar s` lies
in the support of `πstar(·|s)`) together with optimality of `πstar` leaves
`(†)` open, because `advInf` is the *current* policy's advantage, so which
support action maximises it moves with the iterate.  This file discharges that
claim with an explicit finite witness: `hdom_not_implied`.

## The witness

Two states, three actions, `γ = 1/2`.

* `s₁` is **absorbing and reward-free**: every action loops to `s₁` with reward
  `0`.  Hence `V^π(s₁) = 0` for *every* `π`, and `V*(s₁) = 0`.  Making `s₁`'s
  dynamics policy-independent is what keeps the values below computable in
  closed form, and it is what lets `V*` be pinned without a search over
  policies at `s₁`.
* From `s₀`: `a₀` loops to `s₀` with reward `1/2`; `a₁` escapes to `s₁` with
  reward `1`; `a₂` loops to `s₀` with reward `-1`.

`V*(s₀) = 1`, and

```
Q*(s₀,a₀) = 1/2 + (1/2)·1 = 1  =  Q*(s₀,a₁) = 1 + (1/2)·0 = 1  >  Q*(s₀,a₂) = -1/2 .
```

So `a₀` and `a₁` are **tied under `Q*`** — the same tie structure that refuted
`g9_c_positive` (`Proofs.g9_c_positive_frozen_is_false`) — and the policy
`refPistar` that splits `s₀`'s mass evenly over `{a₀, a₁}` is genuinely
optimal: `V^{refPistar} = V*` (`refMDP_hstar`).  Both tied actions therefore sit
in `supp refPistar(·|s₀)`, so `refAstar := fun _ => a₀` satisfies `hastar`
(`refMDP_hastar`) — `hastar` cannot tell `a₀` from `a₁`.

Now take the *current* policy `refPi` to be `a₂` everywhere: legal, merely bad.
Then `V^{refPi}(s₀) = -1 + (1/2)·V^{refPi}(s₀) = -2`, and the two `Q*`-tied
actions come apart under `refPi`'s own advantage:

```
A^{refPi}(s₀,a₀) = (1/2 + (1/2)(-2)) - (-2) = 3/2 ,
A^{refPi}(s₀,a₁) = (1   + (1/2)·0)   - (-2) = 3 .
```

The gap between them is exactly the discounted difference between looping back
into a state `refPi` ruins and escaping to one it cannot touch.  Averaging over
`refPistar` (`a₂` gets mass `0`, so its advantage never enters):

```
advGapInf refMDP refPi refPistar s₀ = (1/2)(3/2) + (1/2)(3) = 9/4
                                    > 3/2 = advInf refMDP refPi s₀ (refAstar s₀) ,
```

i.e. `(†)` **fails** (`ref_dagger_fails`), while `hr`, `0 ≤ γ`, `γ < 1`,
`hstar` and `hastar` all hold.  `hdom_not_implied` packages the five facts
existentially, in the shape `Mei4D`'s `hdom` binder would have to be discharged
from.

## Why `γ = 0` and one state cannot witness this

`Mei4D`'s reading is confirmed by the shape of the counterexample.  At `γ = 0`,
`Qinf M π s a = M.r s a = Qstar M s a` for every `π`, so all of
`supp πstar(·|s)` shares one `advInf` value and `(†)` holds with *equality* —
no `γ = 0` instance can refute it.  With a single state, an action's successor
carries no information the current state does not already have, and the two
`Q*`-tied actions again cannot be separated by `π`'s advantage.  Both `γ > 0`
and the second state are therefore load-bearing, and both are used above: the
`3/2` versus `3` split is precisely `γ · (V^π(s₀) − V^π(s₁)) = (1/2)(−2 − 0)`.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Mei4DRef

open scoped BigOperators

/-! ## The MDP -/

/-- The point mass at `i` on `Fin 2`. -/
noncomputable def refDelta (i : Fin 2) : Dist (Fin 2) where
  prob j := if j = i then 1 else 0
  nonneg j := by by_cases h : j = i <;> simp [h]
  sum_eq_one := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> norm_num

@[simp] theorem refDelta_apply (i j : Fin 2) : refDelta i j = if j = i then 1 else 0 := rfl

/-- Transitions: from `s₀` action `a₁` escapes to `s₁` and every other action
loops back to `s₀`; `s₁` is absorbing under every action. -/
noncomputable def refP : Fin 2 → Fin 3 → Dist (Fin 2)
  | 0, 1 => refDelta 1
  | 0, _ => refDelta 0
  | 1, _ => refDelta 1

/-- Rewards: `r(s₀,·) = (1/2, 1, -1)`, and `s₁` is reward-free. -/
noncomputable def refR : Fin 2 → Fin 3 → ℝ
  | 0, 0 => 1/2
  | 0, 1 => 1
  | 0, 2 => -1
  | 1, _ => 0

/-- **The witness MDP.**  Two states, three actions, `γ = 1/2`. -/
noncomputable def refMDP : FiniteMDP (Fin 2) (Fin 3) where
  P := refP
  r := refR
  γ := 1/2

@[simp] theorem refMDP_P (s : Fin 2) (a : Fin 3) : refMDP.P s a = refP s a := rfl

/-! `refP` and `refR` are defined by pattern matching, so their defining
equations are recorded explicitly: after `fin_cases` the scrutinee is a
`Fin.mk` application that `norm_num` will not reduce through the `match` on its
own. -/

@[simp] theorem refP_zero_zero : refP 0 0 = refDelta 0 := rfl
@[simp] theorem refP_zero_one : refP 0 1 = refDelta 1 := rfl
@[simp] theorem refP_zero_two : refP 0 2 = refDelta 0 := rfl
@[simp] theorem refP_one (a : Fin 3) : refP 1 a = refDelta 1 := rfl

@[simp] theorem refR_zero_zero : refR 0 0 = 1/2 := rfl
@[simp] theorem refR_zero_one : refR 0 1 = 1 := rfl
@[simp] theorem refR_zero_two : refR 0 2 = -1 := rfl
@[simp] theorem refR_one (a : Fin 3) : refR 1 a = 0 := rfl
@[simp] theorem refMDP_r (s : Fin 2) (a : Fin 3) : refMDP.r s a = refR s a := rfl
@[simp] theorem refMDP_gamma : refMDP.γ = 1/2 := rfl

theorem refMDP_hγ₀ : (0:ℝ) ≤ refMDP.γ := by norm_num [refMDP]
theorem refMDP_hγ₁ : refMDP.γ < 1 := by norm_num [refMDP]

/-- Every reward is bounded by `1` in absolute value — `mei_theorem4`'s `hr`. -/
theorem refMDP_hr : ∀ s a, |refMDP.r s a| ≤ 1 := by
  intro s a
  show |refR s a| ≤ 1
  fin_cases s <;> (fin_cases a <;> norm_num [refR])

/-! ## The policies -/

/-- The probability vector `refPistar` uses at `s₀`: even mass on the two
`Q*`-tied actions `a₀, a₁`, and nothing on the bad action `a₂`. -/
noncomputable def refPistarProb : Fin 2 → Fin 3 → ℝ
  | 0, 0 => 1/2
  | 0, 1 => 1/2
  | 0, 2 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 0

/-- **The optimal policy.**  It splits `s₀`'s mass evenly over the `Q*`-tied
actions `a₀` and `a₁`; at the absorbing state the choice is immaterial. -/
noncomputable def refPistar : Policy (Fin 2) (Fin 3) := fun s =>
  ⟨refPistarProb s,
    by intro a; fin_cases s <;> (fin_cases a <;> norm_num [refPistarProb]),
    by rw [Fin.sum_univ_three]; fin_cases s <;> norm_num [refPistarProb]⟩

@[simp] theorem refPistar_apply (s : Fin 2) (a : Fin 3) :
    (refPistar s) a = refPistarProb s a := rfl

/-- The optimal-action selector: `a₀`.  The `Q*` tie makes this a legitimate
choice, and `refPistar` puts strictly positive mass on it. -/
noncomputable def refAstar : Fin 2 → Fin 3 := fun _ => 0

/-- **The current policy**: play the bad action `a₂` everywhere.  Legal, and
nothing in `mei_theorem4`'s hypotheses forbids the trajectory from sitting
here. -/
noncomputable def refPi : Policy (Fin 2) (Fin 3) := detPolicy (fun _ => (2 : Fin 3))

@[simp] theorem refPi_apply (s : Fin 2) (a : Fin 3) :
    (refPi s) a = if a = 2 then 1 else 0 := rfl

/-! ## Values under `refPistar`: `V^{refPistar} = (1, 0)` -/

/-- The value vector of `refPistar`, as a plain function. -/
noncomputable def refVstarVec : Fin 2 → ℝ
  | 0 => 1
  | 1 => 0

theorem ref_Vinf_pistar (s : Fin 2) : Vinf refMDP refPistar s = refVstarVec s := by
  refine Vinf_eq_of_bellman refMDP refPistar refMDP_hr refMDP_hγ₀ refMDP_hγ₁
    refVstarVec ?_ s
  intro x
  rw [Fin.sum_univ_three]
  simp only [refPistar_apply, refMDP_r, refMDP_P, refMDP_gamma]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases x <;>
    norm_num [refPistarProb, refR, refP, refDelta, refVstarVec]

/-! ## `V* = (1, 0)`

The absorbing state is easy: every policy scores exactly `0` from `s₁`, so
`V*(s₁) = 0`.  For `s₀` the crude `1/(1-γ) = 2` bound is *not* tight, so the
supremum needs a real argument: bound an arbitrary policy's value at `s₀` by
`1` using the Bellman equation and the fact that `Vinf · s₁ = 0`. -/

/-- Every policy is worth exactly `0` from the absorbing, reward-free state. -/
theorem ref_Vinf_one (π : Policy (Fin 2) (Fin 3)) : Vinf refMDP π 1 = 0 := by
  have hb := Vinf_bellman refMDP π 1 zero_le_one refMDP_hr refMDP_hγ₀ refMDP_hγ₁ 1
  -- at `s₁` the immediate reward is `0` and every action returns to `s₁`
  have hrew : (∑ a, (π 1) a * refMDP.r 1 a) = 0 := by
    rw [Fin.sum_univ_three]
    simp only [refMDP_r]
    norm_num [refR]
  have hstep : ∀ s', step refMDP π 1 s' = if s' = 1 then 1 else 0 := by
    intro s'
    have h : ∀ a : Fin 3, (refMDP.P 1 a) s' = if s' = 1 then 1 else 0 := by
      intro a; fin_cases a <;> rfl
    have hsum : ∑ a, (π 1) a = 1 := (π 1).sum_eq_one
    show ∑ a, (π 1) a * (refMDP.P 1 a) s' = _
    rw [Finset.sum_congr rfl (fun a _ => by rw [h a] :
      ∀ a ∈ (univ : Finset (Fin 3)),
        (π 1) a * (refMDP.P 1 a) s' = (π 1) a * (if s' = 1 then 1 else 0))]
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [hrew] at hb
  simp only [hstep] at hb
  rw [Fin.sum_univ_two] at hb
  norm_num [refMDP_gamma] at hb
  linarith

/-- **No policy beats `1` at `s₀`.**

The crude `|V| ≤ 1/(1-γ) = 2` bound is not tight enough to pin `V*(s₀) = 1`, so
this is argued from the Bellman equation directly.  Writing `v = V^π(s₀)` and
using `V^π(s₁) = 0`, the three action-brackets are `1/2 + v/2`, `1` and
`-1 + v/2`.  If `v > 1` then *every* one of them is `< v`, yet `v` is their
convex combination — a contradiction. -/
theorem ref_Vinf_le_one (π : Policy (Fin 2) (Fin 3)) : Vinf refMDP π 0 ≤ 1 := by
  by_contra hcon
  have hgt : (1:ℝ) < Vinf refMDP π 0 := lt_of_not_ge hcon
  set v : ℝ := Vinf refMDP π 0 with hv
  have h1 : Vinf refMDP π 1 = 0 := ref_Vinf_one π
  have hb := Vinf_bellman refMDP π 1 zero_le_one refMDP_hr refMDP_hγ₀ refMDP_hγ₁ 0
  -- the Bellman right-hand side, expanded over the three actions
  have hexp : v = ∑ a, (π 0) a
      * (refMDP.r 0 a + refMDP.γ * ∑ s', (refMDP.P 0 a) s' * Vinf refMDP π s') := by
    rw [hv, hb]
    have : ∀ a : Fin 3, (π 0) a
        * (refMDP.r 0 a + refMDP.γ * ∑ s', (refMDP.P 0 a) s' * Vinf refMDP π s')
        = (π 0) a * refMDP.r 0 a
          + refMDP.γ * ((π 0) a * ∑ s', (refMDP.P 0 a) s' * Vinf refMDP π s') := by
      intro a; ring
    rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_add_distrib,
      ← Finset.mul_sum]
    congr 1
    congr 1
    unfold step
    rw [Finset.sum_congr rfl (fun a _ => by rw [Finset.mul_sum] :
      ∀ a ∈ (univ : Finset (Fin 3)),
        (π 0) a * ∑ s', (refMDP.P 0 a) s' * Vinf refMDP π s'
          = ∑ s', (π 0) a * ((refMDP.P 0 a) s' * Vinf refMDP π s'))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- with `v > 1`, every action's bracket is at most `1/2 + v/2`
  have hbr : ∀ a : Fin 3,
      refMDP.r 0 a + refMDP.γ * ∑ s', (refMDP.P 0 a) s' * Vinf refMDP π s'
        ≤ 1/2 + v/2 := by
    intro a
    have hz : ∀ (d : Dist (Fin 2)),
        (∑ s', d s' * Vinf refMDP π s') = d 0 * v := by
      intro d
      rw [Fin.sum_univ_two, h1, ← hv]
      ring
    fin_cases a <;>
      · simp only [refMDP_r, refMDP_P, refMDP_gamma, hz]
        norm_num [refR, refP, refDelta]
        linarith
  -- `v` is their `π`-convex combination, hence `v ≤ 1/2 + v/2`, hence `v ≤ 1`
  have hle : ∑ a, (π 0) a
      * (refMDP.r 0 a + refMDP.γ * ∑ s', (refMDP.P 0 a) s' * Vinf refMDP π s')
      ≤ ∑ a : Fin 3, (π 0) a * (1/2 + v/2) :=
    Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (hbr a) ((π 0).nonneg a)
  rw [← Finset.sum_mul, (π 0).sum_eq_one, one_mul] at hle
  linarith [hexp, hle]

/-- `V* = (1, 0)`.  The upper bounds are `ref_Vinf_le_one` and `ref_Vinf_one`;
both are attained by `refPistar`, so the suprema are exactly these values. -/
theorem ref_Vstar (s : Fin 2) : Vstar refMDP s = refVstarVec s := by
  have hbnd : ∀ (π : Policy (Fin 2) (Fin 3)), Vinf refMDP π s ≤ refVstarVec s := by
    intro π
    fin_cases s
    · exact ref_Vinf_le_one π
    · exact le_of_eq (ref_Vinf_one π)
  refine le_antisymm (ciSup_le hbnd) ?_
  have hbdd : BddAbove (Set.range fun π : Policy (Fin 2) (Fin 3) => Vinf refMDP π s) :=
    ⟨refVstarVec s, by rintro y ⟨π, rfl⟩; exact hbnd π⟩
  have := le_ciSup hbdd refPistar
  rwa [ref_Vinf_pistar s] at this

/-- **`hstar`**: `refPistar` is optimal. -/
theorem refMDP_hstar : ∀ s, Vinf refMDP refPistar s = Vstar refMDP s := by
  intro s; rw [ref_Vinf_pistar, ref_Vstar]

/-- **`hastar`**: `refAstar s` lies in the support of `refPistar(·|s)`. -/
theorem refMDP_hastar : ∀ s, 0 < (refPistar s) (refAstar s) := by
  intro s
  show (0:ℝ) < refPistarProb s (refAstar s)
  fin_cases s <;> norm_num [refPistarProb, refAstar]

/-- The `Q*` tie that makes `refAstar` a legitimate optimal selector:
`Q*(s₀,a₀) = Q*(s₀,a₁) = V*(s₀) = 1`, so no hypothesis of `mei_theorem4` can
prefer one over the other. -/
theorem ref_Qstar_tie :
    Qstar refMDP 0 0 = Vstar refMDP 0 ∧ Qstar refMDP 0 1 = Vstar refMDP 0 := by
  have hQ : ∀ a : Fin 3, Qstar refMDP 0 a
      = refMDP.r 0 a + refMDP.γ * ∑ s', (refMDP.P 0 a) s' * Vstar refMDP s' :=
    fun _ => rfl
  rw [hQ, hQ, ref_Vstar]
  constructor <;>
    · rw [Fin.sum_univ_two, ref_Vstar, ref_Vstar]
      norm_num [refR, refP, refDelta, refVstarVec]

/-! ## Values under the current policy `refPi`: `V^{refPi} = (-2, 0)` -/

/-- The value vector of `refPi`. -/
noncomputable def refViVec : Fin 2 → ℝ
  | 0 => -2
  | 1 => 0

theorem ref_Vinf_pi (s : Fin 2) : Vinf refMDP refPi s = refViVec s := by
  refine Vinf_eq_of_bellman refMDP refPi refMDP_hr refMDP_hγ₀ refMDP_hγ₁
    refViVec ?_ s
  intro x
  rw [Fin.sum_univ_three]
  have h0 : (refPi x) 0 = 0 := by rw [refPi_apply]; simp
  have h1 : (refPi x) 1 = 0 := by rw [refPi_apply]; simp
  have h2 : (refPi x) 2 = 1 := by rw [refPi_apply]; simp
  rw [h0, h1, h2, zero_mul, zero_mul, one_mul, zero_add, zero_add]
  show refViVec x = refMDP.r x 2 + refMDP.γ * ∑ s', (refMDP.P x 2) s' * refViVec s'
  rw [Fin.sum_univ_two]
  fin_cases x
  · simp only [refMDP_r, refMDP_P, refMDP_gamma]
    norm_num [refViVec]
  · simp only [refMDP_r, refMDP_P, refMDP_gamma]
    norm_num [refViVec]

/-! ## The advantages of `refPi`, and the failure of `(†)` -/

/-- `A^{refPi}(s₀,·) = (3/2, 3, 0)`.  The `Q*`-tied actions `a₀` and `a₁` are
**separated** by the current policy's advantage — `3/2` versus `3` — which is
the whole point: `hastar` picked `a₀`, but under `refPi` the other tied action
is strictly better. -/
theorem ref_advInf_zero (a : Fin 3) :
    advInf refMDP refPi 0 a = ![3/2, 3, 0] a := by
  have hA : advInf refMDP refPi 0 a
      = refMDP.r 0 a + refMDP.γ * (∑ s', (refMDP.P 0 a) s' * Vinf refMDP refPi s')
        - Vinf refMDP refPi 0 := rfl
  rw [hA, Fin.sum_univ_two]
  simp only [ref_Vinf_pi]
  fin_cases a <;> norm_num [refR, refP, refDelta, refViVec]

/-- `A^{refPi}(s₀, a*(s₀)) = 3/2`. -/
theorem ref_advInf_astar : advInf refMDP refPi 0 (refAstar 0) = 3/2 := by
  rw [show refAstar 0 = (0 : Fin 3) from rfl, ref_advInf_zero]
  norm_num

/-- `advGapInf refMDP refPi refPistar s₀ = (1/2)(3/2) + (1/2)(3) + 0·0 = 9/4`. -/
theorem ref_advGapInf : advGapInf refMDP refPi refPistar 0 = 9/4 := by
  unfold advGapInf
  rw [Fin.sum_univ_three, ref_advInf_zero, ref_advInf_zero, ref_advInf_zero]
  simp only [refPistar_apply]
  norm_num [refPistarProb]

/-- **The interface condition `(†)` fails at `s₀`**: `3/2 < 9/4`. -/
theorem ref_dagger_fails :
    advInf refMDP refPi 0 (refAstar 0) < advGapInf refMDP refPi refPistar 0 := by
  rw [ref_advInf_astar, ref_advGapInf]
  norm_num

/-! ## The conclusion -/

/-- **`(†)` is not implied by optimality of `πstar` plus `astar ∈ supp πstar`.**

Every hypothesis `Mei4D`'s `mei_theorem4_of_astar_compat` carries about the MDP,
the optimal policy and the selector holds for this witness — bounded rewards,
`0 ≤ γ < 1`, `πstar` optimal, `astar s` in the support of `πstar(·|s)` — and yet
the interface condition

```
advGapInf M π πstar s ≤ advInf M π s (astar s)
```

is violated at `s₀`, where it reads `9/4 ≤ 3/2`.  So `hdom` is a genuine extra
assumption: it cannot be discharged from `mei_theorem4`'s own signature, and
`Mei4D`'s claim to that effect is correct. -/
theorem hdom_not_implied :
    ∃ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S) (_ : DecidableEq A)
      (_ : Nonempty S) (_ : Nonempty A) (M : FiniteMDP S A) (πstar π : Policy S A)
      (astar : S → A),
      (∀ s a, |M.r s a| ≤ 1) ∧ 0 ≤ M.γ ∧ M.γ < 1 ∧
      (∀ s, Vinf M πstar s = Vstar M s) ∧ (∀ s, 0 < (πstar s) (astar s)) ∧
      ∃ s, advInf M π s (astar s) < advGapInf M π πstar s :=
  ⟨Fin 2, Fin 3, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, refMDP, refPistar, refPi, refAstar,
    refMDP_hr, refMDP_hγ₀, refMDP_hγ₁, refMDP_hstar, refMDP_hastar,
    0, ref_dagger_fails⟩

end Mei4DRef

end Proofs
end PolicyGradient

#print axioms PolicyGradient.Proofs.hdom_not_implied
#print axioms PolicyGradient.Proofs.ref_dagger_fails
#print axioms PolicyGradient.Proofs.refMDP_hstar
#print axioms PolicyGradient.Proofs.refMDP_hastar
#print axioms PolicyGradient.Proofs.ref_Qstar_tie
#print axioms PolicyGradient.Proofs.ref_Vstar
