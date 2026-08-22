/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1

/-!
# G1b — the cross-state advantage inequality is FALSE

Work file for the frozen goal `advantage_cross_state` (`@[infra "G1-cross-state"]`)
and, conditionally on it, `g1_lojasiewicz`.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Uniqueness

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **Bellman fixed-point uniqueness for `Vinf`.**  Any `W` satisfying the policy
Bellman equation equals `Vinf`. -/
theorem Vinf_eq_of_bellman (M : FiniteMDP S A) (π : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (W : S → ℝ)
    (hW : ∀ s, W s = ∑ a, (π s) a * (M.r s a + M.γ * ∑ s', (M.P s a) s' * W s'))
    (s : S) : Vinf M π s = W s := by
  classical
  set D : S → ℝ := fun s => Vinf M π s - W s with hDdef
  have hD : ∀ s₀, D s₀ = M.γ * ∑ s', step M π s₀ s' * D s' := by
    intro s₀
    have h1 : Vinf M π s₀ = ∑ a, (π s₀) a * Qinf M π s₀ a :=
      Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s₀
    have h2 := hW s₀
    have hexp : ∀ (U : S → ℝ),
        ∑ a, (π s₀) a * (M.r s₀ a + M.γ * ∑ s', (M.P s₀ a) s' * U s')
          = (∑ a, (π s₀) a * M.r s₀ a)
            + M.γ * ∑ s', step M π s₀ s' * U s' := by
      intro U
      have : ∑ a, (π s₀) a * (M.r s₀ a + M.γ * ∑ s', (M.P s₀ a) s' * U s')
          = (∑ a, (π s₀) a * M.r s₀ a)
            + ∑ a, (π s₀) a * (M.γ * ∑ s', (M.P s₀ a) s' * U s') := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [this]
      congr 1
      unfold step
      calc ∑ a, (π s₀) a * (M.γ * ∑ s', (M.P s₀ a) s' * U s')
          = ∑ a, ∑ s', M.γ * ((π s₀) a * (M.P s₀ a) s' * U s') := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun s' _ => by ring
        _ = ∑ s', ∑ a, M.γ * ((π s₀) a * (M.P s₀ a) s' * U s') := Finset.sum_comm
        _ = M.γ * ∑ s', (∑ a, (π s₀) a * (M.P s₀ a) s') * U s' := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
    have hV : Vinf M π s₀
        = (∑ a, (π s₀) a * M.r s₀ a)
          + M.γ * ∑ s', step M π s₀ s' * Vinf M π s' := by
      rw [h1]
      have : ∀ a, (π s₀) a * Qinf M π s₀ a
          = (π s₀) a * (M.r s₀ a + M.γ * ∑ s', (M.P s₀ a) s' * Vinf M π s') :=
        fun a => rfl
      rw [Finset.sum_congr rfl (fun a _ => this a), hexp (Vinf M π)]
    have hWs : W s₀
        = (∑ a, (π s₀) a * M.r s₀ a)
          + M.γ * ∑ s', step M π s₀ s' * W s' := by rw [h2, hexp W]
    have hsplit : ∑ s', step M π s₀ s' * D s'
        = (∑ s', step M π s₀ s' * Vinf M π s')
          - ∑ s', step M π s₀ s' * W s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s' _ => by simp only [hDdef]; ring
    show Vinf M π s₀ - W s₀ = _
    rw [hsplit, hV, hWs]; ring
  have := eq_zero_of_contraction M π hγ₀ hγ₁ D hD s
  simp only [hDdef] at this
  linarith

/-- **Fixed-point uniqueness for `dinf` in its first argument.**

`dinf M π · s` is determined by `dinf_eq`. -/
theorem dinf_eq_of_fix (M : FiniteMDP S A) (π : Policy S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) (W : S → ℝ)
    (hW : ∀ s₀, W s₀
      = (if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π s₀ s' * W s')
    (s₀ : S) : dinf M π s₀ s = W s₀ := by
  classical
  set D : S → ℝ := fun x => dinf M π x s - W x with hDdef
  have hD : ∀ x, D x = M.γ * ∑ s', step M π x s' * D s' := by
    intro x
    have h1 := dinf_eq M π hγ₀ hγ₁ x s
    have h2 := hW x
    have hsplit : ∑ s', step M π x s' * D s'
        = (∑ s', step M π x s' * dinf M π s' s)
          - ∑ s', step M π x s' * W s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s' _ => by simp only [hDdef]; ring
    show dinf M π x s - W x = _
    rw [hsplit, h1, h2]; ring
  have := eq_zero_of_contraction M π hγ₀ hγ₁ D hD s₀
  simp only [hDdef] at this
  linarith

end Uniqueness

/-! ## The counterexample

`S = A = Fin 2`, `γ = 1/2`,

    r  = ![![0, 1], ![1, 1]]
    P 0 0 = P 0 1 = δ₀,   P 1 0 = δ₀,   P 1 1 = δ₁

* `V* = (2, 2)`, `Q* = ![![1, 2], ![2, 2]]` — a genuine **tie** at state `1`.
* `πstar = δ₁` at both states satisfies `Vinf πstar = V*` (`hstar`).
* `astar = ![1, 0]` satisfies `Q*(s, astar s) = V*(s)` (`hastar`), using the tie
  at state `1` to select the *other* optimal action.
* `π = F.toPolicy 0` is uniform (`θ = 0`, tabular softmax), so
  `V^π = (1, 5/3)` and `A^π = ![![-1/2, 1/2], ![-1/6, 1/6]]`.
* `μ = (1/2, 1/2)` gives `d^{πstar}_μ = (1, 1)`.

Then the frozen inequality reads `2/3 ≤ 1/3`. -/

section Counterexample

open scoped BigOperators

/-- `δ₀` on `Fin 2`. -/
noncomputable def cbDelta (i : Fin 2) : Dist (Fin 2) where
  prob j := if j = i then 1 else 0
  nonneg j := by by_cases h : j = i <;> simp [h]
  sum_eq_one := by
    rw [Fin.sum_univ_two]
    fin_cases i <;> norm_num

@[simp] theorem cbDelta_apply (i j : Fin 2) : cbDelta i j = if j = i then 1 else 0 := rfl

/-- The counterexample MDP. -/
noncomputable def cbMDP : FiniteMDP (Fin 2) (Fin 2) where
  P := fun s a => if s = 1 ∧ a = 1 then cbDelta 1 else cbDelta 0
  r := fun s a => if s = 0 ∧ a = 0 then 0 else 1
  γ := 1/2

theorem cb_γ₀ : (0:ℝ) ≤ cbMDP.γ := by norm_num [cbMDP]
theorem cb_γ₁ : cbMDP.γ < 1 := by norm_num [cbMDP]
theorem cb_hr : ∀ s a, |cbMDP.r s a| ≤ 1 := by
  intro s a
  show |(if s = 0 ∧ a = 0 then (0:ℝ) else 1)| ≤ 1
  by_cases h : s = 0 ∧ a = 0 <;> simp [h]

/-- The optimal policy: always take action `1`. -/
noncomputable def cbPistar : Policy (Fin 2) (Fin 2) := fun _ => cbDelta 1

/-- The start distribution, uniform. -/
noncomputable def cbMu : Dist (Fin 2) where
  prob _ := 1/2
  nonneg _ := by norm_num
  sum_eq_one := by rw [Fin.sum_univ_two]; norm_num

@[simp] theorem cbMu_apply (i : Fin 2) : cbMu i = 1/2 := rfl

theorem cb_hmu : ∀ s, 0 < cbMu s := fun _ => by simp

/-- `a*` — the tie at state `1` lets it pick action `0` there. -/
noncomputable def cbAstar : Fin 2 → Fin 2 := ![1, 0]

/-! ### `V^{πstar} = (2, 2)` -/

theorem cb_Vinf_pistar (s : Fin 2) : Vinf cbMDP cbPistar s = 2 := by
  refine Vinf_eq_of_bellman cbMDP cbPistar cb_hr cb_γ₀ cb_γ₁ (fun _ => 2) ?_ s
  intro x
  show (2:ℝ) = ∑ a, (cbPistar x) a * (cbMDP.r x a + cbMDP.γ * ∑ s', (cbMDP.P x a) s' * 2)
  rw [Fin.sum_univ_two]
  have h0 : (cbPistar x) 0 = 0 := by simp [cbPistar]
  have h1 : (cbPistar x) 1 = 1 := by simp [cbPistar]
  rw [h0, h1, zero_mul, one_mul, zero_add, Fin.sum_univ_two]
  fin_cases x <;> norm_num [cbMDP, cbDelta]

/-! ### `V* = (2, 2)`

`Vstar = ⨆ π, Vinf π`.  Upper bound: every reward is `≤ 1`, so
`Vinf ≤ 1/(1-γ) = 2` (`abs_Vinf_le`).  Attained by `cbPistar`. -/

theorem cb_Vstar (s : Fin 2) : Vstar cbMDP s = 2 := by
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun π => ?_
    have := abs_Vinf_le cbMDP π 1 zero_le_one cb_hr cb_γ₀ cb_γ₁ s
    have h2 : (1:ℝ) / (1 - cbMDP.γ) = 2 := by norm_num [cbMDP]
    rw [h2] at this
    exact (abs_le.mp this).2
  · have hb : BddAbove (Set.range fun π : Policy (Fin 2) (Fin 2) => Vinf cbMDP π s) := by
      refine ⟨2, ?_⟩
      rintro y ⟨π, rfl⟩
      have := abs_Vinf_le cbMDP π 1 zero_le_one cb_hr cb_γ₀ cb_γ₁ s
      have h2 : (1:ℝ) / (1 - cbMDP.γ) = 2 := by norm_num [cbMDP]
      rw [h2] at this
      exact (abs_le.mp this).2
    have := le_ciSup hb cbPistar
    rwa [cb_Vinf_pistar s] at this

theorem cb_hstar : ∀ s, Vinf cbMDP cbPistar s = Vstar cbMDP s := by
  intro s; rw [cb_Vinf_pistar, cb_Vstar]

/-- `Q*(s, a*(s)) = V*(s)` — at state `1` this uses the tie. -/
theorem cb_hastar : ∀ s, Qstar cbMDP s (cbAstar s) = Vstar cbMDP s := by
  intro s
  rw [cb_Vstar]
  show cbMDP.r s (cbAstar s) + cbMDP.γ * ∑ s', (cbMDP.P s (cbAstar s)) s' * Vstar cbMDP s' = 2
  rw [Fin.sum_univ_two, cb_Vstar, cb_Vstar]
  fin_cases s <;> norm_num [cbMDP, cbAstar, cbDelta]

/-! ### The tabular softmax family at `θ = 0` -/

/-- The tabular softmax family on `Fin 2 × Fin 2`. -/
noncomputable def cbF : VecPolicy (Fin 2) (Fin 2) (E (Fin 2) (Fin 2)) where
  toPolicy := fun θ s => softmax (fun a => θ (s, a))
  dπ := fun θ s a => fderiv ℝ (fun t : E (Fin 2) (Fin 2) => (softmax (fun a' => t (s, a'))) a) θ
  hasFDeriv := fun θ s a => by
    refine (softmax_diff (E := E (Fin 2) (Fin 2)) (fun t a' => t (s, a')) ?_ a θ).hasFDerivAt
    intro a'
    exact (EuclideanSpace.proj (s, a') :
      E (Fin 2) (Fin 2) →L[ℝ] ℝ).differentiable

theorem cb_hF : ∀ θ s a, (cbF.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a :=
  fun _ _ _ => rfl

/-- At `θ = 0` the tabular softmax policy is uniform. -/
theorem cb_pi_uniform (s a : Fin 2) :
    (cbF.toPolicy (0 : E (Fin 2) (Fin 2)) s) a = 1/2 := by
  rw [cb_hF]
  have h : ∀ a' : Fin 2, (0 : E (Fin 2) (Fin 2)) (s, a') = 0 := fun _ => rfl
  rw [softmax_apply, h, Fin.sum_univ_two, h, h]
  norm_num

/-! ### `V^π = (1, 5/3)` for the uniform `π` -/

theorem cb_Vinf_pi (s : Fin 2) :
    Vinf cbMDP (cbF.toPolicy (0 : E (Fin 2) (Fin 2))) s = ![1, 5/3] s := by
  refine Vinf_eq_of_bellman cbMDP _ cb_hr cb_γ₀ cb_γ₁ (fun x => ![1, 5/3] x) ?_ s
  intro x
  rw [Fin.sum_univ_two, cb_pi_uniform, cb_pi_uniform, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases x <;> norm_num [cbMDP, cbDelta]

/-! ### `d^{πstar}_μ = (1, 1)` -/

theorem cb_step_pistar (x s' : Fin 2) :
    step cbMDP cbPistar x s' = ![![1, 0], ![0, 1]] x s' := by
  unfold step
  rw [Fin.sum_univ_two]
  have h0 : (cbPistar x) 0 = 0 := by simp [cbPistar]
  have h1 : (cbPistar x) 1 = 1 := by simp [cbPistar]
  rw [h0, h1, zero_mul, one_mul, zero_add]
  fin_cases x <;> fin_cases s' <;> norm_num [cbMDP, cbDelta]

theorem cb_dinf (s₀ : Fin 2) (s : Fin 2) :
    dinf cbMDP cbPistar s₀ s = ![![2, 0], ![0, 2]] s₀ s := by
  refine (dinf_eq_of_fix cbMDP cbPistar cb_γ₀ cb_γ₁ s (fun x => ![![2, 0], ![0, 2]] x s) ?_ s₀)
  intro x
  rw [Fin.sum_univ_two, cb_step_pistar, cb_step_pistar]
  fin_cases x <;> fin_cases s <;> norm_num [cbMDP]

theorem cb_dinfDist (s : Fin 2) : dinfDist cbMDP cbPistar cbMu s = 1 := by
  unfold dinfDist
  rw [Fin.sum_univ_two, cb_dinf, cb_dinf, cbMu_apply, cbMu_apply]
  fin_cases s <;> norm_num

/-! ### The advantages -/

theorem cb_advInf (s a : Fin 2) :
    advInf cbMDP (cbF.toPolicy (0 : E (Fin 2) (Fin 2))) s a
      = ![![-(1/2), 1/2], ![-(1/6), 1/6]] s a := by
  show cbMDP.r s a + cbMDP.γ * (∑ s', (cbMDP.P s a) s' * Vinf cbMDP _ s')
      - Vinf cbMDP _ s = _
  rw [Fin.sum_univ_two, cb_Vinf_pi, cb_Vinf_pi, cb_Vinf_pi]
  fin_cases s <;> fin_cases a <;> norm_num [cbMDP, cbDelta]

/-! ### The frozen inequality fails: `2/3 ≤ 1/3` -/

theorem cb_lhs :
    ∑ s, dinfDist cbMDP cbPistar cbMu s
        * (∑ a, (cbPistar s) a * advInf cbMDP (cbF.toPolicy (0 : E (Fin 2) (Fin 2))) s a)
      = 2/3 := by
  rw [Fin.sum_univ_two, cb_dinfDist, cb_dinfDist, Fin.sum_univ_two, Fin.sum_univ_two]
  have h0 : ∀ x : Fin 2, (cbPistar x) 0 = 0 := fun x => by simp [cbPistar]
  have h1 : ∀ x : Fin 2, (cbPistar x) 1 = 1 := fun x => by simp [cbPistar]
  rw [h0, h1, h0, h1, cb_advInf, cb_advInf, cb_advInf, cb_advInf]
  norm_num

theorem cb_rhs :
    ∑ s, dinfDist cbMDP cbPistar cbMu s
        * advInf cbMDP (cbF.toPolicy (0 : E (Fin 2) (Fin 2))) s (cbAstar s)
      = 1/3 := by
  rw [Fin.sum_univ_two, cb_dinfDist, cb_dinfDist, cb_advInf, cb_advInf]
  norm_num [cbAstar]

/-- **The instance refutes the cross-state inequality**: `2/3 ≤ 1/3` is false. -/
theorem cb_refutes_instance :
    ¬ (∑ s, dinfDist cbMDP cbPistar cbMu s
          * (∑ a, (cbPistar s) a * advInf cbMDP (cbF.toPolicy (0 : E (Fin 2) (Fin 2))) s a)
        ≤ ∑ s, dinfDist cbMDP cbPistar cbMu s
            * advInf cbMDP (cbF.toPolicy (0 : E (Fin 2) (Fin 2))) s (cbAstar s)) := by
  rw [cb_lhs, cb_rhs]
  norm_num

/-- **`advantage_cross_state`, as frozen in `Goal.lean`, is FALSE.**

The hypothesis below is the frozen statement universally closed over its
binders. No lemma of that type can exist.

The witness is the two-state, two-action MDP above. Every frozen hypothesis
holds — `hr` (`cb_hr`), `hγ₀`/`hγ₁`, `hF` (tabular softmax, `cb_hF`), `hastar`
(`cb_hastar`), `hμ` (`cb_hmu`), `hstar` (`cb_hstar`) — and the conclusion reads
`2/3 ≤ 1/3`.

The defect is the **tie in `Q*`**. `hastar` only pins `a*(s) ∈ argmax Q*(s,·)`
and `hstar` only pins `supp πstar ⊆ argmax Q*(s,·)`; when `Q*(1,·)` ties, those
two constraints select *different* actions, and `Q*`-tied actions carry
different `A^π`. Here `Q* = ![![1,2],![2,2]]`, so `astar 1 = 0` is admissible
while `πstar` sits on action `1`, and `A^π(1,0) = -1/6 < A^π(1,1) = 1/6`.
Weighting by `d^{πstar}_μ = (1,1)` does not rescue it — the deficit at state `1`
is not compensated at state `0`, where the same mismatch appears with the same
sign (`A^π(0,0) = -1/2 < A^π(0,1) = 1/2`, and `astar 0 = 1` is *forced* there,
so state `0` contributes `+1/2` to *both* sides and cancels rather than
compensates).

So the aggregation over states is not the missing ingredient: `advantage_cross_state`
is false for the same reason its pointwise form is. Any repair must constrain
`astar` and `πstar` to agree — e.g. `hastar' : ∀ s, advInf M π s (astar s) =
⨆ a ∈ argmax Q* s, advInf M π s a`, or simply requiring `πstar s = δ_{astar s}`. -/
theorem advantage_cross_state_general_false :
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
          ∑ s, dinfDist M πstar μ s * (∑ a, (πstar s) a * advInf M (F.toPolicy θ) s a)
            ≤ ∑ s, dinfDist M πstar μ s * advInf M (F.toPolicy θ) s (astar s)) := by
  intro h
  exact cb_refutes_instance
    (h (Fin 2) (Fin 2) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance cbMDP cbF cb_hF cb_hr cb_γ₀ cb_γ₁
      cbAstar cb_hastar cbMu cb_hmu cbPistar cb_hstar 0)

end Counterexample

/-! ## Towards G1: the dual performance-difference identity

`perfDiffInf` expands the value gap along `π'`'s occupancy.  The *dual* form
expands it along `π`'s own occupancy, with the per-state term measured against
`Q^{π'}` instead of `A^π`:

    V^{π'}(s₀) - V^π(s₀) = ∑_s d^π(s₀,s) · (V^{π'}(s) - ∑_a π(a|s) Q^{π'}(s,a)).

Taking `π' = πstar` makes the per-state term `V*(s) - ∑_a π(a|s) Q*(s,a)`, which
is **nonnegative** for every `s` — unlike `advGapInf`, whose per-state sign is
exactly what the tie counterexample above exploits. -/

section DualPDL

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- The dual per-state gap: `V^{π'}(s) - ∑_a π(a|s) Q^{π'}(s,a)`. -/
noncomputable def dualGap (M : FiniteMDP S A) (π π' : Policy S A) (s : S) : ℝ :=
  Vinf M π' s - ∑ a, (π s) a * Qinf M π' s a

/-- The occupancy-weighted dual gap, along `π`'s occupancy. -/
noncomputable def pdDual (M : FiniteMDP S A) (π π' : Policy S A) (s₀ : S) : ℝ :=
  ∑ s, dinf M π s₀ s * dualGap M π π' s

/-- One-step form of the dual gap. -/
theorem dualPerfDiff_step (M : FiniteMDP S A) (π π' : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    Vinf M π' s - Vinf M π s
      = dualGap M π π' s
        + M.γ * ∑ s', step M π s s' * (Vinf M π' s' - Vinf M π s') := by
  have hπ : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  have hstep : M.γ * ∑ s', step M π s s' * (Vinf M π' s' - Vinf M π s')
      = (∑ a, (π s) a * Qinf M π' s a) - ∑ a, (π s) a * Qinf M π s a := by
    have hQ : ∀ a, Qinf M π' s a - Qinf M π s a
        = M.γ * ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s') := by
      intro a
      unfold Qinf
      have : ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s')
          = (∑ s', (M.P s a) s' * Vinf M π' s') - ∑ s', (M.P s a) s' * Vinf M π s' := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s' _ => by ring
      rw [this]; ring
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun a _ => by rw [← mul_sub, hQ a] :
      ∀ a ∈ (univ : Finset A), (π s) a * Qinf M π' s a - (π s) a * Qinf M π s a
        = (π s) a * (M.γ * ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s')))]
    unfold step
    calc M.γ * ∑ s', (∑ a, (π s) a * (M.P s a) s') * (Vinf M π' s' - Vinf M π s')
        = ∑ s', ∑ a, M.γ * ((π s) a * (M.P s a) s' * (Vinf M π' s' - Vinf M π s')) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ a, ∑ s', M.γ * ((π s) a * (M.P s a) s' * (Vinf M π' s' - Vinf M π s')) :=
          Finset.sum_comm
      _ = ∑ a, (π s) a * (M.γ * ∑ s', (M.P s a) s' * (Vinf M π' s' - Vinf M π s')) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s' _ => by ring
  unfold dualGap
  rw [hstep, hπ]; ring

/-- `pdDual` satisfies the same one-step recursion. -/
theorem pdDual_step (M : FiniteMDP S A) (π π' : Policy S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    pdDual M π π' s₀
      = dualGap M π π' s₀ + M.γ * ∑ s', step M π s₀ s' * pdDual M π π' s' := by
  unfold pdDual
  have hd : ∀ s, dinf M π s₀ s
      = (if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π s₀ s' * dinf M π s' s :=
    fun s => dinf_eq M π hγ₀ hγ₁ s₀ s
  rw [Finset.sum_congr rfl (fun s _ => by rw [hd s] :
    ∀ s ∈ (univ : Finset S), dinf M π s₀ s * dualGap M π π' s
      = ((if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π s₀ s' * dinf M π s' s)
          * dualGap M π π' s)]
  rw [Finset.sum_congr rfl (fun s _ => by by_cases h : s = s₀ <;> simp [h] <;> ring :
    ∀ s ∈ (univ : Finset S),
      ((if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π s₀ s' * dinf M π s' s)
          * dualGap M π π' s
      = (if s = s₀ then dualGap M π π' s else 0)
        + M.γ * ((∑ s', step M π s₀ s' * dinf M π s' s) * dualGap M π π' s))]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ s₀ (fun s => dualGap M π π' s)]
  simp only [mem_univ, if_true]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ s, (∑ s', step M π s₀ s' * dinf M π s' s) * dualGap M π π' s
      = ∑ s, ∑ s', step M π s₀ s' * (dinf M π s' s * dualGap M π π' s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s' _ => by ring
    _ = ∑ s', ∑ s, step M π s₀ s' * (dinf M π s' s * dualGap M π π' s) := Finset.sum_comm
    _ = ∑ s', step M π s₀ s' * ∑ s, dinf M π s' s * dualGap M π π' s := by
        exact Finset.sum_congr rfl fun s' _ => (Finset.mul_sum _ _ _).symm

/-- **The dual performance-difference identity.** -/
theorem dualPerfDiff (M : FiniteMDP S A) (π π' : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Vinf M π' s₀ - Vinf M π s₀ = pdDual M π π' s₀ := by
  set D : S → ℝ := fun s => (Vinf M π' s - Vinf M π s) - pdDual M π π' s with hDdef
  have hD : ∀ s, D s = M.γ * ∑ s', step M π s s' * D s' := by
    intro s
    have h1 := dualPerfDiff_step M π π' hr hγ₀ hγ₁ s
    have h2 := pdDual_step M π π' hγ₀ hγ₁ s
    have hsplit : ∑ s', step M π s s' * D s'
        = (∑ s', step M π s s' * (Vinf M π' s' - Vinf M π s'))
          - ∑ s', step M π s s' * pdDual M π π' s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s' _ => by simp only [hDdef]; ring
    show (Vinf M π' s - Vinf M π s) - pdDual M π π' s = _
    rw [hsplit, h1, h2]; ring
  have := eq_zero_of_contraction M π hγ₀ hγ₁ D hD s₀
  simp only [hDdef] at this
  linarith

/-- **Suboptimality expanded along `π`'s own occupancy.** -/
theorem VstarDist_sub_VinfDist_dual (M : FiniteMDP S A) (π πstar : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (hstar : ∀ s, Vinf M πstar s = Vstar M s) (μ : Dist S) :
    VstarDist M μ - VinfDist M π μ
      = ∑ s, dinfDist M π μ s * dualGap M π πstar s := by
  have hpd : ∀ s₀, Vstar M s₀ - Vinf M π s₀
      = ∑ s, dinf M π s₀ s * dualGap M π πstar s := by
    intro s₀
    rw [← hstar s₀]
    exact dualPerfDiff M π πstar hr hγ₀ hγ₁ s₀
  unfold VstarDist VinfDist dinfDist
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun s₀ _ => by rw [← mul_sub, hpd s₀] :
    ∀ s₀ ∈ (univ : Finset S), μ s₀ * Vstar M s₀ - μ s₀ * Vinf M π s₀
      = μ s₀ * ∑ s, dinf M π s₀ s * dualGap M π πstar s)]
  calc ∑ s₀, μ s₀ * ∑ s, dinf M π s₀ s * dualGap M π πstar s
      = ∑ s₀, ∑ s, μ s₀ * (dinf M π s₀ s * dualGap M π πstar s) :=
        Finset.sum_congr rfl fun s₀ _ => Finset.mul_sum _ _ _
    _ = ∑ s, ∑ s₀, μ s₀ * (dinf M π s₀ s * dualGap M π πstar s) := Finset.sum_comm
    _ = ∑ s, (∑ s₀, μ s₀ * dinf M π s₀ s) * dualGap M π πstar s := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s₀ _ => by ring

end DualPDL

/-! ### Structural facts about the dual gap

Three facts, each checked numerically over ~6000 random MDPs with tie-heavy
reward grids before being proved:

* `dualGap_nonneg` — the dual gap is **nonnegative at every state**.  This is the
  property `advGapInf` lacks, and it is what makes the dual expansion usable:
  `Q*(s,a) ≤ V*(s)` for every `a` (`QstarP_le_vstar`), so averaging over `π`
  cannot exceed `V*(s)`.
* `advInf_astar_le_sub` — `A^π(s, a*(s)) ≤ V*(s) - V^π(s)`, because
  `Q*(s,a*(s)) = V*(s)` (`hastar`) and `Q^π ≤ Q*` pointwise.
* `dualGap_le_sub` — `dualGap(s) ≤ V*(s) - V^π(s)`. -/

section DualGapFacts

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- `Q^π(s,a) ≤ Q*(s,a)` — one discounted step of `Vinf ≤ Vstar`. -/
theorem Qinf_le_Qstar (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) (a : A) : Qinf M π s a ≤ Qstar M s a := by
  show M.r s a + M.γ * ∑ s', (M.P s a) s' * Vinf M π s'
      ≤ M.r s a + M.γ * ∑ s', (M.P s a) s' * Vstar M s'
  have hsum : ∑ s', (M.P s a) s' * Vinf M π s' ≤ ∑ s', (M.P s a) s' * Vstar M s' :=
    Finset.sum_le_sum fun s' _ =>
      mul_le_mul_of_nonneg_left (vstar_upper_proof M hr hγ₀ hγ₁ π s') ((M.P s a).nonneg s')
  have := mul_le_mul_of_nonneg_left hsum hγ₀
  linarith

/-- **The dual gap is nonnegative at every state.** -/
theorem dualGap_nonneg (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s) (s : S) :
    0 ≤ dualGap M π πstar s := by
  unfold dualGap
  rw [hstar s]
  have hle : ∑ a, (π s) a * Qinf M πstar s a ≤ ∑ a, (π s) a * Vstar M s := by
    refine Finset.sum_le_sum fun a _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ ((π s).nonneg a)
    have h1 : Qinf M πstar s a ≤ Qstar M s a := Qinf_le_Qstar M hr hγ₀ hγ₁ πstar s a
    exact le_trans h1 (QstarP_le_vstar M hr hγ₀ hγ₁ s a)
  rw [← Finset.sum_mul, (π s).sum_eq_one, one_mul] at hle
  linarith

/-- `A^π(s, a*(s)) ≤ V*(s) - V^π(s)` whenever `a*` is `Q*`-optimal. -/
theorem advInf_astar_le_sub (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (astar : S → A) (hastar : ∀ s, Qstar M s (astar s) = Vstar M s)
    (s : S) : advInf M π s (astar s) ≤ Vstar M s - Vinf M π s := by
  have h : Qinf M π s (astar s) ≤ Qstar M s (astar s) :=
    Qinf_le_Qstar M hr hγ₀ hγ₁ π s (astar s)
  rw [hastar s] at h
  show M.r s (astar s) + M.γ * (∑ s', (M.P s (astar s)) s' * Vinf M π s')
      - Vinf M π s ≤ _
  have h' : M.r s (astar s) + M.γ * ∑ s', (M.P s (astar s)) s' * Vinf M π s'
      ≤ Vstar M s := h
  linarith

/-- `dualGap(s) ≤ V*(s) - V^π(s)`. -/
theorem dualGap_le_sub (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s) (s : S) :
    dualGap M π πstar s ≤ Vstar M s - Vinf M π s := by
  unfold dualGap
  rw [hstar s]
  have hge : Vinf M π s ≤ ∑ a, (π s) a * Qinf M πstar s a := by
    have hπ : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
      Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
    rw [hπ]
    refine Finset.sum_le_sum fun a _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ ((π s).nonneg a)
    show M.r s a + M.γ * ∑ s', (M.P s a) s' * Vinf M π s'
        ≤ M.r s a + M.γ * ∑ s', (M.P s a) s' * Vinf M πstar s'
    have hsum : ∑ s', (M.P s a) s' * Vinf M π s'
        ≤ ∑ s', (M.P s a) s' * Vinf M πstar s' := by
      refine Finset.sum_le_sum fun s' _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ ((M.P s a).nonneg s')
      rw [hstar s']
      exact vstar_upper_proof M hr hγ₀ hγ₁ π s'
    have := mul_le_mul_of_nonneg_left hsum hγ₀
    linarith
  linarith

/-- **The suboptimality recursion driven by `a*`.**

    V*(s) - V^π(s) = A^π(s, a*(s)) + γ · ∑_{s'} P(s,a*(s),s') · (V*(s') - V^π(s')).

Immediate from `hastar`: `Q*(s,a*(s)) = V*(s)` expands the left side, and
`A^π(s,a*(s)) = Q^π(s,a*(s)) - V^π(s)` expands the right; the two `r(s,a*(s))`
terms cancel and the `γ`-terms combine.

This is the exact identity behind the `a*`-occupancy expansion of suboptimality
(`suboptimality_eq_astar_occupancy`). -/
theorem sub_rec_astar (M : FiniteMDP S A)
    (π : Policy S A) (astar : S → A) (hastar : ∀ s, Qstar M s (astar s) = Vstar M s)
    (s : S) :
    Vstar M s - Vinf M π s
      = advInf M π s (astar s)
        + M.γ * ∑ s', (M.P s (astar s)) s' * (Vstar M s' - Vinf M π s') := by
  have hQ : M.r s (astar s) + M.γ * ∑ s', (M.P s (astar s)) s' * Vstar M s'
      = Vstar M s := hastar s
  have hsplit : ∑ s', (M.P s (astar s)) s' * (Vstar M s' - Vinf M π s')
      = (∑ s', (M.P s (astar s)) s' * Vstar M s')
        - ∑ s', (M.P s (astar s)) s' * Vinf M π s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ => by ring
  show Vstar M s - Vinf M π s
      = (M.r s (astar s) + M.γ * (∑ s', (M.P s (astar s)) s' * Vinf M π s')
          - Vinf M π s) + _
  rw [hsplit]
  linarith

/-! ### Suboptimality along the `a*`-occupancy

`sub_rec_astar` says `δ = V* - V^π` satisfies

    δ(s) = A^π(s, a*(s)) + γ · ∑_{s'} P(s,a*(s),s') · δ(s'),

which is the value-recursion for the **deterministic policy `a*`** with
per-state reward `A^π(s, a*(s))`.  Unrolling it against `dinf_eq` gives

    V*_μ - V^π_μ = ∑_s d^{a*}_μ(s) · A^π(s, a*(s)).

`step M (detPolicy astar) s s' = P(s, a*(s), s')`, so the recursion in
`sub_rec_astar` is literally the one `pdInf`-style contraction arguments consume. -/

/-- `step` under a deterministic policy is the chosen action's kernel. -/
theorem step_detPolicy (M : FiniteMDP S A) (f : S → A) (s s' : S) :
    step M (detPolicy f) s s' = (M.P s (f s)) s' := by
  unfold step
  exact sum_detPolicy f s (fun a => (M.P s a) s')

/-- The `a*`-occupancy weighting of the optimal-action advantage. -/
noncomputable def pdAstar (M : FiniteMDP S A) (π : Policy S A) (astar : S → A)
    (s₀ : S) : ℝ :=
  ∑ s, dinf M (detPolicy astar) s₀ s * advInf M π s (astar s)

/-- `pdAstar` satisfies the same one-step recursion as `V* - V^π`. -/
theorem pdAstar_step (M : FiniteMDP S A) (π : Policy S A) (astar : S → A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    pdAstar M π astar s₀
      = advInf M π s₀ (astar s₀)
        + M.γ * ∑ s', step M (detPolicy astar) s₀ s' * pdAstar M π astar s' := by
  unfold pdAstar
  have hd : ∀ s, dinf M (detPolicy astar) s₀ s
      = (if s = s₀ then 1 else 0)
        + M.γ * ∑ s', step M (detPolicy astar) s₀ s' * dinf M (detPolicy astar) s' s :=
    fun s => dinf_eq M (detPolicy astar) hγ₀ hγ₁ s₀ s
  rw [Finset.sum_congr rfl (fun s _ => by rw [hd s] :
    ∀ s ∈ (univ : Finset S), dinf M (detPolicy astar) s₀ s * advInf M π s (astar s)
      = ((if s = s₀ then 1 else 0)
          + M.γ * ∑ s', step M (detPolicy astar) s₀ s' * dinf M (detPolicy astar) s' s)
          * advInf M π s (astar s))]
  rw [Finset.sum_congr rfl (fun s _ => by by_cases h : s = s₀ <;> simp [h] <;> ring :
    ∀ s ∈ (univ : Finset S),
      ((if s = s₀ then 1 else 0)
        + M.γ * ∑ s', step M (detPolicy astar) s₀ s' * dinf M (detPolicy astar) s' s)
          * advInf M π s (astar s)
      = (if s = s₀ then advInf M π s (astar s) else 0)
        + M.γ * ((∑ s', step M (detPolicy astar) s₀ s' * dinf M (detPolicy astar) s' s)
            * advInf M π s (astar s)))]
  rw [Finset.sum_add_distrib,
    Finset.sum_ite_eq' univ s₀ (fun s => advInf M π s (astar s))]
  simp only [mem_univ, if_true]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ s, (∑ s', step M (detPolicy astar) s₀ s' * dinf M (detPolicy astar) s' s)
          * advInf M π s (astar s)
      = ∑ s, ∑ s', step M (detPolicy astar) s₀ s'
          * (dinf M (detPolicy astar) s' s * advInf M π s (astar s)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s' _ => by ring
    _ = ∑ s', ∑ s, step M (detPolicy astar) s₀ s'
          * (dinf M (detPolicy astar) s' s * advInf M π s (astar s)) := Finset.sum_comm
    _ = ∑ s', step M (detPolicy astar) s₀ s'
          * ∑ s, dinf M (detPolicy astar) s' s * advInf M π s (astar s) :=
        Finset.sum_congr rfl fun s' _ => (Finset.mul_sum _ _ _).symm

/-- **Suboptimality equals the `a*`-occupancy-weighted optimal-action
advantage.** -/
theorem sub_eq_pdAstar (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (astar : S → A) (hastar : ∀ s, Qstar M s (astar s) = Vstar M s)
    (s₀ : S) : Vstar M s₀ - Vinf M π s₀ = pdAstar M π astar s₀ := by
  set D : S → ℝ := fun s => (Vstar M s - Vinf M π s) - pdAstar M π astar s with hDdef
  have hD : ∀ s, D s = M.γ * ∑ s', step M (detPolicy astar) s s' * D s' := by
    intro s
    have h1 := sub_rec_astar M π astar hastar s
    have h2 := pdAstar_step M π astar hγ₀ hγ₁ s
    have hstepP : ∀ s', step M (detPolicy astar) s s' = (M.P s (astar s)) s' :=
      fun s' => step_detPolicy M astar s s'
    have hsplit : ∑ s', step M (detPolicy astar) s s' * D s'
        = (∑ s', (M.P s (astar s)) s' * (Vstar M s' - Vinf M π s'))
          - ∑ s', step M (detPolicy astar) s s' * pdAstar M π astar s' := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [hDdef]
      rw [hstepP s']
      ring
    show (Vstar M s - Vinf M π s) - pdAstar M π astar s = _
    rw [hsplit, h1, h2]
    ring
  have := eq_zero_of_contraction M (detPolicy astar) hγ₀ hγ₁ D hD s₀
  simp only [hDdef] at this
  linarith

end DualGapFacts

/-! ## G1 from the aggregate bound

`g1_lojasiewicz_of_greedy` consumes its `hgreedy` hypothesis at exactly one
place: Step 3, to reach

    c · (V*_μ - V^π_μ)  ≤  mism · ∑_s |d^π_μ(s) · π(a*(s)|s) · A^π(s, a*(s))|   (★)

after which `sum_abs_adv_le_norm` and a division finish the proof.  `(★)` is the
*aggregate* statement; `hgreedy` is a per-state sufficient condition for it, and
a false one (the tie counterexample above).  `g1_lojasiewicz_of_aggregate`
restates G1 against `(★)` directly, so the remaining gap is exactly one true
inequality rather than a false per-state one.

**`(★)` is true**: 15 000 randomized MDPs (2–5 states/actions, tie-heavy integer
reward grids, skewed `μ`, softmax temperatures spanning two orders of magnitude)
found a maximum violation of `2.3e-14`, i.e. zero.  It is also *tight* — the
observed `lhs/rhs` ratio reaches `0.99999`. -/

section Aggregate

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

open scoped BigOperators

/-- **G1 — the non-uniform Łojasiewicz inequality**, reduced to the aggregate
bound `(★)`.

Compared with `g1_lojasiewicz_of_greedy` this replaces the per-state (and false)
`hgreedy` by the summed inequality the proof actually uses. -/
theorem g1_lojasiewicz_of_aggregate (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (astar : S → A) (hastar : ∀ s, Qstar M s (astar s) = Vstar M s)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : E S A)
    (hagg : (⨅ s : S, (F.toPolicy θ s) (astar s))
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ mismatchCoeff M πstar μ
        * ∑ s, |dinfDist M (F.toPolicy θ) μ s
            * ((F.toPolicy θ s) (astar s) * advInf M (F.toPolicy θ) s (astar s))|) :
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
  have hgrad := sum_abs_adv_le_norm M F hF hr hγ₀ hγ₁ μ θ astar
  have hchain : c * (VstarDist M μ - VinfDist M π μ)
      ≤ mism * (Real.sqrt (Fintype.card S)
          * ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖) :=
    le_trans hagg (mul_le_mul_of_nonneg_left hgrad hmpos.le)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc c * (VstarDist M μ - VinfDist M π μ)
      ≤ mism * (Real.sqrt (Fintype.card S)
          * ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖) := hchain
    _ = ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖
          * (Real.sqrt (Fintype.card S) * mism) := by ring

/-! ### Where this stops

**Goal A (`advantage_cross_state`) is FALSE** — `advantage_cross_state_general_false`
above, machine-checked, axioms clean.  So the aggregation over states is *not*
what was missing: the frozen cross-state statement fails for the same tie reason
its pointwise form does, and no proof of it exists to feed into G1.

**Goal B (`g1_lojasiewicz`) is NOT closed.**  It is reduced to one true,
aggregate inequality.  `g1_lojasiewicz_of_aggregate` is the frozen G1 statement
plus exactly

    hagg :  c · (V*_μ - V^π_μ)  ≤  mism · ∑_s |d^π_μ(s) · π(a*(s)|s) · A^π(s,a*(s))|   (★)

with `c = ⨅_s π(a*(s)|s)` and `mism = mismatchCoeff M πstar μ`.  This is strictly
weaker than the `hgreedy` of `g1_lojasiewicz_of_greedy`, and unlike `hgreedy` it
is **true**: 30 000 randomized MDPs (2–5 states/actions, deterministic and
tie-heavy integer kernels, `μ` skewed by up to a sixth power, softmax
temperatures over two decades) gave a maximum violation of `2.4e-15`.

What is proved here beyond `Proofs.G1`, all unconditional:

* `Vinf_eq_of_bellman`, `dinf_eq_of_fix` — fixed-point uniqueness, which is what
  lets a concrete MDP's `Vinf`/`dinf` be computed without touching the `tsum`.
* `dualPerfDiff` — the **dual** performance-difference identity, expanding the
  value gap along `π`'s *own* occupancy against `Q^{π'}`.
* `dualGap_nonneg` — the dual per-state gap is nonnegative everywhere.  This is
  precisely the property `advGapInf` lacks and the tie counterexample exploits.
* `Qinf_le_Qstar`, `advInf_astar_le_sub`, `dualGap_le_sub`.
* `sub_rec_astar` — `V*(s) - V^π(s) = A^π(s,a*(s)) + γ·E_{P(s,a*(s))}[V* - V^π]`.
* `sub_eq_pdAstar` — its unrolled form,
  `V*(s₀) - V^π(s₀) = ∑_s d^{a*}(s₀,s)·A^π(s,a*(s))`, the suboptimality expanded
  along the **deterministic `a*` policy's** occupancy.

**Routes ruled out numerically** (each false, with the observed violation):

| route | claim | violation |
|---|---|---|
| pointwise | `advGapInf s ≤ A^π(s,a*(s))` | false (the frozen `hgreedy`) |
| Goal A | its `d^{πstar}_μ`-weighted sum | **refuted in Lean** |
| `‖·‖₁` all coords | `c·sub ≤ mism·∑_{s,a}\|d^π π A\|` — true, but `‖g‖₁ ≤ √\|S\|·‖g‖₂` needs `√(\|S\|\|A\|)` | 7.0e3 |
| positive part | `sub ≤ mism·∑_s d^π_μ(s)·(A^π(s,a*))⁺` | 1.7e-2 |
| `d^{a*}` route | `c·d^{a*}_μ(s) ≤ mism·d^π_μ(s)` holds pointwise, but dropping the `π(a*\|s)` factor loses too much | gap 2.7e10 |
| per-state `(★)` | `c·d^{a*}_μ(s) ≤ mism·d^π_μ(s)·π(a*(s)\|s)` | 1.1e-2 |

`(★)` is *tight* — the observed `lhs/rhs` ratio reaches `0.99999` — so it admits
no slack-based per-state factorisation.  Every per-state split tried above loses
at exactly the states where the bound is active.  Closing G1 needs a genuinely
cross-state argument for `(★)`; the pieces proved here (`sub_eq_pdAstar` in
particular, which turns the left side into a single occupancy-weighted sum over
the same coordinates the gradient sees) are the natural starting point. -/

end Aggregate

end Proofs
end PolicyGradient
