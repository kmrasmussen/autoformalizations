/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Greedy

/-!
# G9 — `Goal.g9_c_positive` is FALSE, and the defect is a `Q*` tie

`Goal.g9_c_positive` asks for a single `c > 0` with

  `∀ t, c ≤ ⨅ s, π_{θ t}(a*(s) | s)`

along softmax gradient ascent, where `a*` is **any** function satisfying
`hastar : ∀ s, Q*(s, a*(s)) = V*(s)`.

`hastar` was added after `Proofs.g9_is_false`, where `astar` selected a strictly
*suboptimal* action. It fixes that defect and no other. It does **not** exclude a
`Q*` **tie**: when two actions are both optimal at `s`, `hastar` permits `astar`
to select whichever one gradient ascent abandons — and softmax ascent does
abandon one of two tied optimal actions, because the tie is broken by the
initialization, not by the rewards.

`g9_c_positive_frozen_is_false` below takes the frozen statement **with
`Goal.lean`'s own implicit and instance binders** as a hypothesis and derives
`False`. It applies directly to `PolicyGradient.g9_c_positive` itself:

  `example : False := g9_c_positive_frozen_is_false @PolicyGradient.g9_c_positive`

typechecks (it cannot be recorded in this file, which `Goal.lean` transitively
imports).

## The witness

One state, three actions, `γ = 0`, rewards `r = (1, 1, 0)`.

* `γ = 0` makes `Q*(s,a) = r(s,a)` and `V*(s) = 1`.
* So `Q*(s,0) = Q*(s,1) = 1 = V*(s)` — a **tie** — and `Q*(s,2) = 0 < 1`.
* `astar := fun _ => 0` therefore satisfies `hastar` (`tie_hastar`), and so does
  `fun _ => 1` (`tie_hastar'`). Nothing suboptimal is selected: the old defect is
  genuinely absent, and the statement is still false.

`γ = 0` is chosen deliberately so no part of the failure can be blamed on the
discount factor, and the state space is a single state so the frozen `⨅ s : S`
cannot be blamed either — the infimum is over one term.

Gradient ascent from `θ₀ = (0, 1, 0)` breaks the tie in favour of action `1`:
both tied actions have positive advantage, but action `1` starts with more mass,
so its logit grows faster, and `π_t(0) → 0` while `π_t(1) → 1`.

## The argument

With `γ = 0` the occupancy is `1` and the policy gradient (`gradient_Vinf_coord`,
proved here in general) collapses to

  `θ_{t+1}(a) = θ_t(a) + (1/8) · p_t(a) · (r a - (p_t 0 + p_t 1))`.

Write `x_t = θ_t 1 - θ_t 0` (the gap between the two **tied** actions) and
`y_t = θ_t 1 - θ_t 2`. Then

  `x_{t+1} = x_t + (1/8) · p 2 · (p 1 - p 0)`,
  `y_{t+1} = y_t + (1/8) · p 2 · (2·p 1 + p 0)`.

1. `tie_gaps_ge_one`: both gaps stay `≥ 1`. `y` increases unconditionally; `x`
   increases exactly while `p 1 ≥ p 0`, which is exactly `x ≥ 0` — a single
   simultaneous induction.
2. `tieP_one_ge`: hence the softmax denominator relative to action `1` is
   `1 + e^{-x} + e^{-y} ≤ 3`, so `p 1 ≥ 1/3` and `p 2 ≥ e^{-y}/3`.
3. `tieSm_unbounded`: **`∑_t p_t 2 = ∞`.** Both growth rates are proportional to
   `p 2`, which itself tends to `0`, so no rate estimate is available. The
   argument is instead self-defeating: `y_{t+1} - y_t ≤ p 2 / 4`, so bounded
   partial sums would keep `y` bounded, hence `p 2 ≥ e^{-B}/3` bounded *below* —
   and a series of terms bounded below by a positive constant diverges. **No
   estimate on the decay rate of `p 2` is needed**, which is what makes the whole
   thing elementary.
4. `tiex_unbounded`: `x_{t+1} - x_t ≥ ((1-e⁻¹)/24) · p_t 2`, so `x_t → ∞`, and
   `p_t 0 ≤ e^{-x_t}` gets arbitrarily small (`tieP_zero_inf`).

## The intended reduction is false too

The task this file answers asked first for the reduction

  `V(θ_t) → V*(μ)  ⟹  ∃ c > 0, ∀ t, c ≤ ⨅ s, π_t(a*(s)|s)`,

to be composed later with `softmax_ascent_converges`. **That reduction is also
false**, by the same witness (`g9_of_convergence_is_false`): here
`V^{π_t}(0) = 1 - p_t 2 → 1 = V*(0)` (`tie_hconv`, from the mirror of step 3
applied to `y`), so the convergence hypothesis holds while the conclusion fails.

That is not an accident of the witness. Value convergence *cannot* imply the
conclusion, because both tied actions are optimal: abandoning one of them costs
the value nothing, which is exactly why `V → V*` fails to see it. Any proof of a
`c > 0` must control the policy, not the value.

## The witness is not degenerate

`tie_moves`: gradient ascent genuinely moves (the tied-action logit gap strictly
increases at the first step) — this is not the `unreachMDP` situation where the
gradient vanishes identically and the trajectory is constant.
`tie_lt_Vstar`: the value is strictly below `V*` at every finite `t`, since
softmax never puts probability `0` on the suboptimal action. The optimum is
approached and never attained, exactly as in the real algorithm.

## What survives, and what a repair needs

* `iInf_pi_pos` — for each **fixed** `t` the infimum is positive (softmax is
  strictly positive, `S` is finite). The frozen goal is the uniform-in-`t`
  strengthening, and the tie breaks exactly that.
* `g9_of_policy_limit` — the reduction that **is** true: if the policies converge
  coordinatewise to a `πbar` with `πbar(a*(s)|s) > 0` at every `s`, then a single
  `c > 0` exists. This is strictly stronger than value convergence, and it is
  what a proof of G9 has to establish.

So a repaired G9 must pin `astar` to the actions the trajectory keeps — e.g.
carry `0 < liminf_t π_t(a*(s)|s)` as part of the selection, or state the bound
for the *best* optimal action, `⨅ s, ⨆ {a | Q*(s,a) = V*(s)}, π_t(a|s)`, rather
than for an arbitrary `Q*`-argmax selector.

## Reusable machinery proved on the way

`gradient_Vinf_coord` (general `S`, `A`): the tabular softmax policy gradient in
coordinates, `(∇_θ V^{π_θ}(μ))(s,a) = d^{π_θ}(μ,s) · π_θ(a|s) · A^{π_θ}(s,a)`.
The repo had `dVinfDist_single` (a start *distribution*, and `fderiv` applied to
a coordinate vector); this is the single-start-state version, and it goes all the
way to `gradient`, which is what the frozen `hstep` recursion actually moves
along. Nothing before this could compute a step of that recursion.
-/

open Finset Filter

namespace PolicyGradient
namespace Proofs

section G9Tie

/-! ## The witness MDP: one state, three actions, `γ = 0` -/

/-- Every action loops back to the single state. -/
noncomputable def tieTransition (_s : Fin 1) (_a : Fin 3) : Dist (Fin 1) where
  prob _ := 1
  nonneg _ := zero_le_one
  sum_eq_one := by simp

/-- `r = (1, 1, 0)`: actions `0` and `1` are **tied optimal**, action `2` is not. -/
noncomputable def tieReward : Fin 1 → Fin 3 → ℝ
  | _, 0 => 1
  | _, 1 => 1
  | _, 2 => 0

/-- **The witness.** One state, three actions, `γ = 0`. -/
noncomputable def tieMDP : FiniteMDP (Fin 1) (Fin 3) where
  P := tieTransition
  r := tieReward
  γ := 0

@[simp] theorem tieMDP_gamma : tieMDP.γ = 0 := rfl
@[simp] theorem tieMDP_r (s : Fin 1) (a : Fin 3) : tieMDP.r s a = tieReward s a := rfl
@[simp] theorem tieMDP_P (s : Fin 1) (a : Fin 3) : tieMDP.P s a = tieTransition s a := rfl

theorem tie_hr : ∀ s a, |tieMDP.r s a| ≤ 1 := by
  intro s a; fin_cases s <;> (fin_cases a <;> norm_num [tieReward])

theorem tie_γ₀ : (0:ℝ) ≤ tieMDP.γ := le_rfl
theorem tie_γ₁ : tieMDP.γ < 1 := by norm_num [tieMDP]

/-! ### Values with `γ = 0`

`γ = 0` collapses everything: `V^π(s) = ∑_a π(a|s) r(s,a)`, `Q^π = Q* = r`,
`A^π(s,a) = r(s,a) - V^π(s)`, and `d^π(s,s) = 1`. -/

/-- The expected one-step reward of `π`. -/
noncomputable def tieRbar (π : Policy (Fin 1) (Fin 3)) : ℝ :=
  (π 0) 0 + (π 0) 1

theorem tie_Vinf (π : Policy (Fin 1) (Fin 3)) (s : Fin 1) :
    Vinf tieMDP π s = tieRbar π := by
  refine Vinf_eq_of_bellman tieMDP π tie_hr tie_γ₀ tie_γ₁
    (fun _ => tieRbar π) ?_ s
  intro x
  have : ∀ a : Fin 3, (π x) a * (tieMDP.r x a
      + tieMDP.γ * ∑ s', (tieMDP.P x a) s' * tieRbar π) = (π x) a * tieReward x a := by
    intro a; show (π x) a * (tieReward x a + 0 * _) = _; ring
  rw [Finset.sum_congr rfl (fun a _ => this a)]
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  show tieRbar π = _
  rw [Fin.sum_univ_three]
  simp [tieRbar, tieReward]

theorem tie_Qinf (π : Policy (Fin 1) (Fin 3)) (s : Fin 1) (a : Fin 3) :
    Qinf tieMDP π s a = tieReward s a := by
  show tieMDP.r s a + tieMDP.γ * _ = _
  simp [tieMDP]

theorem tie_advInf (π : Policy (Fin 1) (Fin 3)) (s : Fin 1) (a : Fin 3) :
    advInf tieMDP π s a = tieReward s a - tieRbar π := by
  show tieMDP.r s a + tieMDP.γ * (∑ s', (tieMDP.P s a) s' * Vinf tieMDP π s')
    - Vinf tieMDP π s = _
  rw [tie_Vinf π s]
  simp [tieMDP]

/-! ### `V* = 1` and the tie -/

theorem tie_Vstar (s : Fin 1) : Vstar tieMDP s = 1 := by
  have hb : ∀ π : Policy (Fin 1) (Fin 3), Vinf tieMDP π s ≤ 1 := by
    intro π
    rw [tie_Vinf π s, tieRbar]
    have h := (π 0).sum_eq_one
    rw [Fin.sum_univ_three] at h
    have := (π 0).nonneg 2
    linarith
  refine le_antisymm (ciSup_le hb) ?_
  have hbdd : BddAbove (Set.range fun π : Policy (Fin 1) (Fin 3) => Vinf tieMDP π s) :=
    ⟨1, by rintro y ⟨π, rfl⟩; exact hb π⟩
  have := le_ciSup hbdd (detPolicy (fun _ : Fin 1 => (0 : Fin 3)))
  rw [tie_Vinf _ s] at this
  refine le_trans ?_ this
  simp [tieRbar, detPolicy, pointMass]

theorem tie_Qstar (s : Fin 1) (a : Fin 3) : Qstar tieMDP s a = tieReward s a := by
  show tieMDP.r s a + tieMDP.γ * _ = _
  simp [tieMDP]

/-- **`astar = fun _ => 0` is a legitimate optimal selector.**

This is the whole defect: `Q*(s,0) = Q*(s,1) = V*(s) = 1`, so `hastar` cannot
distinguish action `0` from action `1`. -/
theorem tie_hastar : ∀ s, Qstar tieMDP s ((fun _ : Fin 1 => (0 : Fin 3)) s) = Vstar tieMDP s := by
  intro s; rw [tie_Qstar, tie_Vstar]; simp [tieReward]

/-- Action `1` is equally optimal — the tie, stated. -/
theorem tie_hastar' : ∀ s, Qstar tieMDP s ((fun _ : Fin 1 => (1 : Fin 3)) s) = Vstar tieMDP s := by
  intro s; rw [tie_Qstar, tie_Vstar]; simp [tieReward]

/-- Action `2` is strictly suboptimal, so the witness is not degenerate: the
tie is between `0` and `1` only. -/
theorem tie_Qstar_two (s : Fin 1) : Qstar tieMDP s 2 < Vstar tieMDP s := by
  rw [tie_Qstar, tie_Vstar]; norm_num [tieReward]

end G9Tie

/-! ## The gradient of `Vinf` in coordinates

`gradient` is the Riesz representative of `fderiv`, so its `(s,a)` coordinate is
`fderiv` applied to the coordinate vector `single (s,a) 1`.  Composed with
`dVinf_single` that is the policy-gradient formula
`∂V/∂θ(s,a) = d^π(s) · π(a|s) · A^π(s,a)`. -/

section GradCoord

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

omit [Nonempty S] [Nonempty A] in
/-- A gradient's coordinate is the derivative applied to the coordinate vector. -/
theorem gradient_coord (f : E S A → ℝ) (θ : E S A) (p : S × A) :
    (gradient f θ) p = fderiv ℝ f θ (EuclideanSpace.single p (1:ℝ)) := by
  have h := inner_gradient_left (𝕜 := ℝ) (f := f) (x := θ)
      (y := (EuclideanSpace.single p (1:ℝ) : E S A))
  rw [← h, EuclideanSpace.inner_single_right]
  simp

/-- **`dVinf` applied to one coordinate vector.**

The single-start-state companion of `dVinfDist_single`. -/
theorem dVinf_single (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : E S A) (s : S) (a : A) :
    dVinf M (F.toPolicy θ) θ μ (EuclideanSpace.single (s, a) (1:ℝ))
      = dinf M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) := by
  classical
  unfold dVinf
  rw [ContinuousLinearMap.sum_apply]
  have hterm : ∀ x : S,
      (dinf M (F.toPolicy θ) μ x
        • dg (S:=S) (A:=A) x (fun a' => Qinf M (F.toPolicy θ) x a') θ)
          (EuclideanSpace.single (s, a) (1:ℝ))
      = if x = s then
          dinf M (F.toPolicy θ) μ s
            * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a)
        else 0 := by
    intro x
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, ← dg_advInf_eq,
      dg_single s x a (fun a' => advInf M (F.toPolicy θ) x a') θ]
    by_cases hx : x = s
    · subst hx
      have hzero : ∑ a', (softmax (fun a'' => θ (x,a''))) a' * advInf M (F.toPolicy θ) x a'
          = 0 := by
        have h := advGapInf_self M (F.toPolicy θ) hr hγ₀ hγ₁ x
        unfold advGapInf at h
        rw [Finset.sum_congr rfl (fun a' _ => by rw [hF θ x a'] :
          ∀ a' ∈ (univ : Finset A),
            (F.toPolicy θ x) a' * advInf M (F.toPolicy θ) x a'
              = (softmax (fun a'' => θ (x,a''))) a' * advInf M (F.toPolicy θ) x a')] at h
        exact h
      rw [if_pos rfl, hzero, hF θ x a]
      simp
    · simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [Finset.sum_ite_eq' univ s (fun _ => dinf M (F.toPolicy θ) μ s
    * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a))]
  simp

/-- **The tabular softmax policy gradient, in coordinates.**

`(∇_θ V^{π_θ}(μ))(s,a) = d^{π_θ}(μ,s) · π_θ(a|s) · A^{π_θ}(s,a)`.

This is the formula the frozen `hstep` recursion moves along, made explicit. -/
theorem gradient_Vinf_coord (M : FiniteMDP S A)
    (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : E S A) (s : S) (a : A) :
    (gradient (fun w : E S A => Vinf M (F.toPolicy w) μ) θ) (s, a)
      = dinf M (F.toPolicy θ) μ s
        * ((F.toPolicy θ s) a * advInf M (F.toPolicy θ) s a) := by
  rw [gradient_coord, (hasFDerivAt_Vinf M F hF hr hγ₀ hγ₁ θ μ).fderiv,
    dVinf_single M F hF hr hγ₀ hγ₁ μ θ s a]

end GradCoord

/-! ## The trajectory

`tieF` is the tabular softmax family on `Fin 1 × Fin 3`; `tieTh` is the frozen
ascent recursion, defined *by* that recursion so that `hstep` is `rfl`. -/

section Traj

/-- The tabular softmax family on `Fin 1 × Fin 3`. -/
noncomputable def tieF : VecPolicy (Fin 1) (Fin 3) (E (Fin 1) (Fin 3)) where
  toPolicy := fun θ s => softmax (fun a => θ (s, a))
  dπ := fun θ s a => fderiv ℝ (fun t : E (Fin 1) (Fin 3) => (softmax (fun a' => t (s, a'))) a) θ
  hasFDeriv := fun θ s a => by
    refine (softmax_diff (E := E (Fin 1) (Fin 3)) (fun t a' => t (s, a')) ?_ a θ).hasFDerivAt
    intro a'
    exact (EuclideanSpace.proj (s, a') :
      E (Fin 1) (Fin 3) →L[ℝ] ℝ).differentiable

theorem tie_hF : ∀ θ s a, (tieF.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a :=
  fun _ _ _ => rfl

/-- The occupancy is `1`: with `γ = 0` only the start state at time `0` counts. -/
theorem tie_dinf (π : Policy (Fin 1) (Fin 3)) (s₀ s : Fin 1) :
    dinf tieMDP π s₀ s = 1 := by
  refine dinf_eq_of_fix tieMDP π tie_γ₀ tie_γ₁ s (fun _ => 1) ?_ s₀
  intro x
  have : s = x := Subsingleton.elim _ _
  subst this
  simp [tieMDP]

/-- **The gradient of the witness objective, coordinatewise.**

`∂V/∂θ(s,a) = π(a|s) · (r(s,a) - V^π)`. -/
theorem tie_grad (θ : E (Fin 1) (Fin 3)) (s : Fin 1) (a : Fin 3) :
    (gradient (fun w : E (Fin 1) (Fin 3) => Vinf tieMDP (tieF.toPolicy w) 0) θ) (s, a)
      = (softmax (fun a' => θ (s, a'))) a
        * (tieReward s a - tieRbar (tieF.toPolicy θ)) := by
  rw [gradient_Vinf_coord tieMDP tieF tie_hF tie_hr tie_γ₀ tie_γ₁ 0 θ s a,
    tie_dinf, tie_advInf, tie_hF]
  ring

/-- The step size of the frozen recursion at `γ = 0`. -/
theorem tie_eta : ((1 - tieMDP.γ) ^ 3 / 8 : ℝ) = 1 / 8 := by norm_num [tieMDP]

/-- The initial parameter `θ₀ = (0, 1, 0)`: the tie between actions `0` and `1`
is broken in favour of action `1`. -/
noncomputable def tieTh0 : E (Fin 1) (Fin 3) := EuclideanSpace.single (0, 1) (1:ℝ)

/-- **The ascent trajectory**, defined by the frozen recursion itself. -/
noncomputable def tieTh : ℕ → E (Fin 1) (Fin 3)
  | 0 => tieTh0
  | t + 1 => tieTh t
      + ((1 - tieMDP.γ) ^ 3 / 8)
        • gradient (fun w : E (Fin 1) (Fin 3) => Vinf tieMDP (tieF.toPolicy w) 0) (tieTh t)

/-- `hstep` holds by construction. -/
theorem tie_hstep : ∀ t, tieTh (t + 1)
    = tieTh t + ((1 - tieMDP.γ) ^ 3 / 8)
      • gradient (fun w : E (Fin 1) (Fin 3) => Vinf tieMDP (tieF.toPolicy w) 0) (tieTh t) :=
  fun _ => rfl

/-- The three logits of the trajectory at time `t`. -/
noncomputable def tieL (t : ℕ) (a : Fin 3) : ℝ := tieTh t (0, a)

/-- The three probabilities of the trajectory at time `t`. -/
noncomputable def tieP (t : ℕ) (a : Fin 3) : ℝ := (softmax (tieL t)) a

theorem tieP_pos (t : ℕ) (a : Fin 3) : 0 < tieP t a := softmax_pos _ a

theorem tieP_sum (t : ℕ) : tieP t 0 + tieP t 1 + tieP t 2 = 1 := by
  have := (softmax (tieL t)).sum_eq_one
  rw [Fin.sum_univ_three] at this
  exact this

theorem tieP_lt_one (t : ℕ) (a : Fin 3) : tieP t a < 1 := by
  have h := tieP_sum t
  have h0 := tieP_pos t 0
  have h1 := tieP_pos t 1
  have h2 := tieP_pos t 2
  fin_cases a
  · show tieP t 0 < 1; linarith
  · show tieP t 1 < 1; linarith
  · show tieP t 2 < 1; linarith

/-- The value along the trajectory is `π(0) + π(1)`. -/
theorem tie_V (t : ℕ) : tieRbar (tieF.toPolicy (tieTh t)) = tieP t 0 + tieP t 1 := rfl

/-- **The recursion, in logit coordinates.** -/
theorem tieL_succ (t : ℕ) (a : Fin 3) :
    tieL (t + 1) a = tieL t a + (1/8) * (tieP t a * (tieReward 0 a - (tieP t 0 + tieP t 1))) := by
  show tieTh (t + 1) (0, a) = _
  rw [tie_hstep t]
  have hadd : (tieTh t + ((1 - tieMDP.γ) ^ 3 / 8)
      • gradient (fun w : E (Fin 1) (Fin 3) => Vinf tieMDP (tieF.toPolicy w) 0) (tieTh t))
      ((0 : Fin 1), a)
      = tieTh t (0, a) + ((1 - tieMDP.γ) ^ 3 / 8)
        * (gradient (fun w : E (Fin 1) (Fin 3) => Vinf tieMDP (tieF.toPolicy w) 0)
            (tieTh t)) (0, a) := by
    simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hadd, tie_eta, tie_grad]
  rfl

end Traj

/-! ## The analysis

Write `x t = tieL t 1 - tieL t 0` (the logit gap between the two **tied optimal**
actions) and `y t = tieL t 1 - tieL t 2` (the gap to the suboptimal action).  The
recursion `tieL_succ` reads, with `p a = tieP t a`,

  `x (t+1) = x t + (1/8) · p 2 · (p 1 - p 0)`
  `y (t+1) = y t + (1/8) · p 2 · (p 1 + p 0 + p 1)`

(using `1 - p 2 = p 0 + p 1`).  Both increments are nonnegative once `x t ≥ 0`.
-/

section Analysis

/-- The logit gap between the two tied optimal actions. -/
noncomputable def tiex (t : ℕ) : ℝ := tieL t 1 - tieL t 0

/-- The logit gap to the strictly suboptimal action. -/
noncomputable def tiey (t : ℕ) : ℝ := tieL t 1 - tieL t 2

theorem tiex_zero : tiex 0 = 1 := by
  show tieTh 0 (0, 1) - tieTh 0 (0, 0) = 1
  show tieTh0 (0, 1) - tieTh0 (0, 0) = 1
  rw [tieTh0]
  rw [show ((EuclideanSpace.single ((0 : Fin 1), (1 : Fin 3)) (1:ℝ)) : E (Fin 1) (Fin 3))
      ((0 : Fin 1), (1 : Fin 3)) = 1 by simp,
    show ((EuclideanSpace.single ((0 : Fin 1), (1 : Fin 3)) (1:ℝ)) : E (Fin 1) (Fin 3))
      ((0 : Fin 1), (0 : Fin 3)) = 0 by simp]
  ring

theorem tiey_zero : tiey 0 = 1 := by
  show tieTh 0 (0, 1) - tieTh 0 (0, 2) = 1
  show tieTh0 (0, 1) - tieTh0 (0, 2) = 1
  rw [tieTh0]
  rw [show ((EuclideanSpace.single ((0 : Fin 1), (1 : Fin 3)) (1:ℝ)) : E (Fin 1) (Fin 3))
      ((0 : Fin 1), (1 : Fin 3)) = 1 by simp,
    show ((EuclideanSpace.single ((0 : Fin 1), (1 : Fin 3)) (1:ℝ)) : E (Fin 1) (Fin 3))
      ((0 : Fin 1), (2 : Fin 3)) = 0 by simp]
  ring

/-- The recursion for `tiex`. -/
theorem tiex_succ (t : ℕ) :
    tiex (t + 1) = tiex t + (1/8) * (tieP t 2 * (tieP t 1 - tieP t 0)) := by
  have h0 := tieL_succ t 0
  have h1 := tieL_succ t 1
  have hs := tieP_sum t
  simp only [tiex]
  rw [h0, h1]
  have e0 : tieReward 0 0 = 1 := rfl
  have e1 : tieReward 0 1 = 1 := rfl
  rw [e0, e1]
  have hp2 : tieP t 2 = 1 - (tieP t 0 + tieP t 1) := by linarith
  rw [hp2]; ring

/-- The recursion for `tiey`. -/
theorem tiey_succ (t : ℕ) :
    tiey (t + 1) = tiey t + (1/8) * (tieP t 2 * (2 * tieP t 1 + tieP t 0)) := by
  have h1 := tieL_succ t 1
  have h2 := tieL_succ t 2
  have hs := tieP_sum t
  simp only [tiey]
  rw [h1, h2]
  have e1 : tieReward 0 1 = 1 := rfl
  have e2 : tieReward 0 2 = 0 := rfl
  rw [e1, e2]
  have hp2 : tieP t 2 = 1 - (tieP t 0 + tieP t 1) := by linarith
  rw [hp2]; ring

/-! ### Softmax in terms of the two gaps -/

/-- `p 0 = p 1 · e^{-x}`. -/
theorem tieP_zero_eq (t : ℕ) : tieP t 0 = tieP t 1 * Real.exp (- tiex t) := by
  show (softmax (tieL t)) 0 = (softmax (tieL t)) 1 * Real.exp (- tiex t)
  rw [softmax_apply, softmax_apply]
  have hd : (0:ℝ) < ∑ a', Real.exp (tieL t a') := softmax_denom_pos _
  field_simp
  rw [← Real.exp_add]
  congr 1
  simp [tiex]

/-- `p 2 = p 1 · e^{-y}`. -/
theorem tieP_two_eq (t : ℕ) : tieP t 2 = tieP t 1 * Real.exp (- tiey t) := by
  show (softmax (tieL t)) 2 = (softmax (tieL t)) 1 * Real.exp (- tiey t)
  rw [softmax_apply, softmax_apply]
  have hd : (0:ℝ) < ∑ a', Real.exp (tieL t a') := softmax_denom_pos _
  field_simp
  rw [← Real.exp_add]
  congr 1
  simp [tiey]

/-! ### Both gaps stay at least `1` -/

/-- **The two gaps never fall below their initial value `1`.**

`tiey` increases unconditionally; `tiex` increases exactly while `p 1 ≥ p 0`, which
is exactly `tiex ≥ 0`.  The two are proved together by a single induction. -/
theorem tie_gaps_ge_one : ∀ t, 1 ≤ tiex t ∧ 1 ≤ tiey t := by
  intro t
  induction t with
  | zero => exact ⟨le_of_eq tiex_zero.symm, le_of_eq tiey_zero.symm⟩
  | succ t ih =>
      obtain ⟨hx, hy⟩ := ih
      have h2 := tieP_pos t 2
      have h1 := tieP_pos t 1
      have h0 := tieP_pos t 0
      have hgap : tieP t 0 ≤ tieP t 1 := by
        rw [tieP_zero_eq t]
        have : Real.exp (- tiex t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        nlinarith
      constructor
      · rw [tiex_succ t]; nlinarith
      · rw [tiey_succ t]; nlinarith

theorem tiex_ge_one (t : ℕ) : 1 ≤ tiex t := (tie_gaps_ge_one t).1
theorem tiey_ge_one (t : ℕ) : 1 ≤ tiey t := (tie_gaps_ge_one t).2

/-- **`p 1 ≥ 1/3`.**  The softmax denominator, written relative to action `1`,
is `1 + e^{-x} + e^{-y} ≤ 3` because both gaps are nonnegative. -/
theorem tieP_one_ge (t : ℕ) : (1:ℝ)/3 ≤ tieP t 1 := by
  have hs := tieP_sum t
  have h0 := tieP_zero_eq t
  have h2 := tieP_two_eq t
  have hx : Real.exp (- tiex t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [tiex_ge_one t])
  have hy : Real.exp (- tiey t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [tiey_ge_one t])
  have h1 := tieP_pos t 1
  nlinarith

/-- **`p 0 ≤ e^{-x}`.** -/
theorem tieP_zero_le (t : ℕ) : tieP t 0 ≤ Real.exp (- tiex t) := by
  rw [tieP_zero_eq t]
  have h1 : tieP t 1 ≤ 1 := (tieP_lt_one t 1).le
  have he : (0:ℝ) < Real.exp (- tiex t) := Real.exp_pos _
  nlinarith

/-- **`p 2 ≥ e^{-y}/3`.** -/
theorem tieP_two_ge (t : ℕ) : Real.exp (- tiey t) / 3 ≤ tieP t 2 := by
  rw [tieP_two_eq t]
  have h1 := tieP_one_ge t
  have he : (0:ℝ) < Real.exp (- tiey t) := Real.exp_pos _
  nlinarith

end Analysis

/-! ## The gap `tiex` is unbounded

The one step with real content.  Both `tiex` and `tiey` grow at a rate proportional
to `p 2`, which itself tends to `0` — so neither growth rate is bounded below,
and the question is whether the increments still sum to `∞`.

They do, and the proof is a self-defeating assumption: if `∑ p 2` were bounded
then `tiey` — whose increments are at most `p 2 / 4` — would stay bounded, hence
`p 2 = p 1 · e^{-y} ≥ e^{-B}/3` would be bounded **below** by a positive
constant, and a series of such terms diverges.

No estimate on the decay *rate* of `p 2` is needed, which is what makes this
elementary. -/

section Divergence

/-- The partial sums of `p 2`. -/
noncomputable def tieSm (t : ℕ) : ℝ := ∑ k ∈ Finset.range t, tieP k 2

theorem tieSm_mono : Monotone tieSm := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [tieSm, tieSm, Finset.sum_range_succ]
  linarith [(tieP_pos t 2).le]

theorem tieSm_nonneg (t : ℕ) : 0 ≤ tieSm t :=
  Finset.sum_nonneg fun k _ => (tieP_pos k 2).le

/-- `tiey` is controlled by the partial sums: `y t ≤ 1 + S t / 4`. -/
theorem tiey_le (t : ℕ) : tiey t ≤ 1 + tieSm t / 4 := by
  induction t with
  | zero => rw [tiey_zero, tieSm]; simp
  | succ t ih =>
      rw [tiey_succ t, tieSm, Finset.sum_range_succ, ← tieSm]
      have hs := tieP_sum t
      have h0 := (tieP_pos t 0).le
      have h1 := (tieP_pos t 1).le
      have h2 := (tieP_pos t 2).le
      have hb : 2 * tieP t 1 + tieP t 0 ≤ 2 := by linarith
      nlinarith

/-- **The partial sums of `p 2` are unbounded.**

If `S t ≤ B` for all `t` then `tiey t ≤ 1 + B/4`, hence
`p 2 ≥ e^{-(1+B/4)}/3 > 0` at every step, hence `S t ≥ t · e^{-(1+B/4)}/3`,
which exceeds `B` for large `t`. -/
theorem tieSm_unbounded : ∀ B : ℝ, ∃ t, B < tieSm t := by
  intro B
  by_contra hcon
  push_neg at hcon
  -- every partial sum is ≤ B, so `tiey` is bounded
  set ε : ℝ := Real.exp (-(1 + B / 4)) / 3 with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hyb : ∀ t, tiey t ≤ 1 + B / 4 := fun t =>
    le_trans (tiey_le t) (by linarith [hcon t])
  have hlow : ∀ t, ε ≤ tieP t 2 := by
    intro t
    refine le_trans ?_ (tieP_two_ge t)
    rw [hε]
    have := Real.exp_le_exp.mpr (by linarith [hyb t] : -(1 + B / 4) ≤ - tiey t)
    linarith
  have hSt : ∀ t : ℕ, (t : ℝ) * ε ≤ tieSm t := by
    intro t
    rw [tieSm]
    calc (t : ℝ) * ε = ∑ _k ∈ Finset.range t, ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range t, tieP k 2 := Finset.sum_le_sum fun k _ => hlow k
  obtain ⟨n, hn⟩ := exists_nat_gt ((B + 1) / ε)
  have h1 : B + 1 ≤ (n : ℝ) * ε := by
    rw [div_lt_iff₀ hεpos] at hn
    linarith
  have := le_trans h1 (hSt n)
  linarith [hcon n]

/-- `tiex` grows at least `(1 - e⁻¹)/24` per unit of `∑ p 2`. -/
theorem tiex_ge_Sm (t : ℕ) : 1 + (1 - Real.exp (-1)) / 24 * tieSm t ≤ tiex t := by
  induction t with
  | zero => rw [tiex_zero, tieSm]; simp
  | succ t ih =>
      rw [tiex_succ t, tieSm, Finset.sum_range_succ, ← tieSm]
      have h2 := (tieP_pos t 2).le
      have hd : (1 - Real.exp (-1)) / 3 ≤ tieP t 1 - tieP t 0 := by
        rw [tieP_zero_eq t]
        have h1 := tieP_one_ge t
        have hx : Real.exp (- tiex t) ≤ Real.exp (-1) :=
          Real.exp_le_exp.mpr (by linarith [tiex_ge_one t])
        have hle1 : tieP t 1 ≤ 1 := (tieP_lt_one t 1).le
        have hep : (0:ℝ) < Real.exp (- tiex t) := Real.exp_pos _
        have he1 : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
        have key : (1 - Real.exp (-1)) / 3 ≤ tieP t 1 * (1 - Real.exp (- tiex t)) := by
          have hfac : 0 ≤ 1 - Real.exp (- tiex t) := by linarith
          have h13 : (1:ℝ)/3 * (1 - Real.exp (-1)) ≤ tieP t 1 * (1 - Real.exp (- tiex t)) := by
            refine mul_le_mul h1 (by linarith) (by linarith) (by linarith)
          linarith
        nlinarith
      have hepos : Real.exp (-1) < 1 := by
        rw [Real.exp_lt_one_iff]; norm_num
      nlinarith

/-- **The logit gap between the two tied optimal actions diverges.** -/
theorem tiex_unbounded : ∀ C : ℝ, ∃ t, C < tiex t := by
  intro C
  set c : ℝ := (1 - Real.exp (-1)) / 24 with hc
  have hcpos : 0 < c := by
    rw [hc]
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  obtain ⟨t, ht⟩ := tieSm_unbounded ((C - 1) / c)
  refine ⟨t, lt_of_lt_of_le ?_ (tiex_ge_Sm t)⟩
  rw [div_lt_iff₀ hcpos] at ht
  rw [← hc]
  linarith

/-- **`π_t(a₀ | s)` gets arbitrarily small.**

`p 0 ≤ e^{-x}` and `x` is unbounded. -/
theorem tieP_zero_inf : ∀ c : ℝ, 0 < c → ∃ t, tieP t 0 < c := by
  intro c hc
  obtain ⟨t, ht⟩ := tiex_unbounded (Real.log (1 / c))
  refine ⟨t, lt_of_le_of_lt (tieP_zero_le t) ?_⟩
  have h1 : Real.exp (- tiex t) < Real.exp (- Real.log (1 / c)) :=
    Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (- Real.log (1 / c)) = c := by
    rw [← Real.log_inv, Real.exp_log (by positivity)]
    field_simp
  rwa [h2] at h1

end Divergence

/-! ## The refutation

`S = Fin 1`, so the frozen `⨅ s : S, π_t(a*(s)|s)` is just `π_t(0|0) = tieP t 0`,
which `tieP_zero_inf` makes arbitrarily small. -/

section Refutation

/-- Over a one-element index type the infimum is the single value. -/
theorem tie_iInf_fin_one (f : Fin 1 → ℝ) : (⨅ s : Fin 1, f s) = f 0 := by
  exact ciInf_subsingleton (0 : Fin 1) f

/-- The frozen infimum along the witness trajectory is exactly `tieP t 0`. -/
theorem tie_iInf (t : ℕ) :
    (⨅ s : Fin 1, (tieF.toPolicy (tieTh t) s) ((fun _ : Fin 1 => (0 : Fin 3)) s))
      = tieP t 0 := by
  rw [tie_iInf_fin_one]
  rfl

/-- **`Goal.g9_c_positive` is FALSE as frozen**, stated against the goal's own
binder shape.

The hypothesis is `Goal.g9_c_positive` verbatim — implicit `{S A}` and instance
binders included, copied from `Goal.lean` — so the application below would not
typecheck if the statement assumed here were not the frozen one.

Witness: `tieMDP` (one state, three actions, `γ = 0`, `r = (1,1,0)`), the
tabular softmax family `tieF`, start state `0`, the ascent trajectory `tieTh`
from `θ₀ = (0,1,0)`, and `astar = fun _ => 0`.

* `hF` — `tie_hF`;
* `hr`, `hγ₀`, `hγ₁` — `tie_hr`, `tie_γ₀`, `tie_γ₁`;
* `hstep` — `tie_hstep`, true by construction of `tieTh`;
* `hastar` — `tie_hastar`: `Q*(s,0) = 1 = V*(s)`, because action `0` really is
  **optimal**.  This is not the old `g9_is_false` defect: nothing suboptimal is
  being selected.  Action `1` is *equally* optimal (`tie_hastar'`), and that
  tie is what the statement fails to exclude.

The conclusion fails because `tieP_zero_inf` produces, for any candidate `c > 0`,
a time `t` with `π_t(0|0) < c`. -/
theorem g9_c_positive_frozen_is_false
    (frozen : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
      [Nonempty S] [Nonempty A]
      (M : FiniteMDP S A) (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
      (∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a) →
      (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
      ∀ (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A)),
      (∀ t, θ (t + 1)
        = θ t + ((1 - M.γ) ^ 3 / 8)
          • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) →
      ∀ (astar : S → A), (∀ s, Qstar M s (astar s) = Vstar M s) →
      ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s)) : False := by
  obtain ⟨c, hcpos, hc⟩ := frozen (S := Fin 1) (A := Fin 3) tieMDP tieF tie_hF
    tie_hr tie_γ₀ tie_γ₁ 0 tieTh tie_hstep (fun _ => 0) tie_hastar
  obtain ⟨t, ht⟩ := tieP_zero_inf c hcpos
  have := hc t
  rw [tie_iInf t] at this
  linarith

end Refutation

/-! ## The intended reduction is false too

The task this file answers proposed proving the reduction

  `V(θ_t) → V*(μ)  ⟹  ∃ c > 0, ∀ t, c ≤ ⨅ s, π_t(a*(s)|s)`

and then discharging the hypothesis from the concurrent
`softmax_ascent_converges`.  The same witness kills the reduction: here the
value **does** converge to the optimum, and the conclusion still fails.

`p 2 → 0` by the mirror of the `tiex` argument (`tiey` also grows like `∑ p 2`), and
`V^{π_t}(0) = p 0 + p 1 = 1 - p 2 → 1 = V*(0)`.  Both tied actions are optimal,
so losing all mass on action `0` costs the value nothing — which is precisely
why the convergence hypothesis cannot rule the situation out. -/

section ReductionFalse

/-- `tiey` grows at least `1/12` per unit of `∑ p 2`. -/
theorem tiey_ge_Sm (t : ℕ) : 1 + tieSm t / 12 ≤ tiey t := by
  induction t with
  | zero => rw [tiey_zero, tieSm]; simp
  | succ t ih =>
      rw [tiey_succ t, tieSm, Finset.sum_range_succ, ← tieSm]
      have h2 := (tieP_pos t 2).le
      have h0 := (tieP_pos t 0).le
      have h1 := tieP_one_ge t
      nlinarith

/-- **`p 2 → 0`.** -/
theorem tieP_two_tendsto : Filter.Tendsto (fun t => tieP t 2) Filter.atTop (nhds 0) := by
  have hub : ∀ t, tieP t 2 ≤ Real.exp (- (1 + tieSm t / 12)) := by
    intro t
    rw [tieP_two_eq t]
    have h1 : tieP t 1 ≤ 1 := (tieP_lt_one t 1).le
    have hle : Real.exp (- tiey t) ≤ Real.exp (- (1 + tieSm t / 12)) :=
      Real.exp_le_exp.mpr (by linarith [tiey_ge_Sm t])
    have hpos : (0:ℝ) < Real.exp (- tiey t) := Real.exp_pos _
    nlinarith
  have hg : Filter.Tendsto (fun t => Real.exp (- (1 + tieSm t / 12)))
      Filter.atTop (nhds 0) := by
    -- `tieSm` is monotone and unbounded, so `exp(-(1 + tieSm/12)) → 0`
    have hS : Filter.Tendsto tieSm Filter.atTop Filter.atTop :=
      tendsto_atTop_atTop_of_monotone tieSm_mono (fun B => (tieSm_unbounded B).imp
        (fun _ h => h.le))
    have h2 : Filter.Tendsto (fun t => - (1 + tieSm t / 12)) Filter.atTop Filter.atBot := by
      refine Filter.tendsto_neg_atTop_atBot.comp ?_
      exact Filter.tendsto_atTop_add_const_left _ 1 (hS.atTop_div_const (by norm_num))
    have h3 := Real.tendsto_exp_atBot.comp h2
    exact h3
  exact squeeze_zero (fun t => (tieP_pos t 2).le) hub hg

/-- **The value converges to the optimum along the witness trajectory.** -/
theorem tie_hconv :
    Filter.Tendsto (fun t => Vinf tieMDP (tieF.toPolicy (tieTh t)) 0) Filter.atTop
      (nhds (Vstar tieMDP 0)) := by
  have hV : ∀ t, Vinf tieMDP (tieF.toPolicy (tieTh t)) 0 = 1 - tieP t 2 := by
    intro t
    rw [tie_Vinf _ 0, tie_V t]
    linarith [tieP_sum t]
  rw [tie_Vstar]
  simp only [hV]
  have := (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop (α := ℕ))).sub
    tieP_two_tendsto
  simpa using this

/-- **The reduction `V(θ_t) → V*  ⟹  c > 0` is FALSE.**

Same witness, same binder shape as `g9_c_positive_frozen_is_false`, with the
convergence hypothesis added and discharged by `tie_hconv`. -/
theorem g9_of_convergence_is_false
    (frozen : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
      [Nonempty S] [Nonempty A]
      (M : FiniteMDP S A) (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
      (∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a) →
      (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
      ∀ (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A)),
      (∀ t, θ (t + 1)
        = θ t + ((1 - M.γ) ^ 3 / 8)
          • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) →
      ∀ (astar : S → A), (∀ s, Qstar M s (astar s) = Vstar M s) →
      Filter.Tendsto (fun t => Vinf M (F.toPolicy (θ t)) μ) Filter.atTop
        (nhds (Vstar M μ)) →
      ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s)) : False := by
  obtain ⟨c, hcpos, hc⟩ := frozen (S := Fin 1) (A := Fin 3) tieMDP tieF tie_hF
    tie_hr tie_γ₀ tie_γ₁ 0 tieTh tie_hstep (fun _ => 0) tie_hastar tie_hconv
  obtain ⟨t, ht⟩ := tieP_zero_inf c hcpos
  have := hc t
  rw [tie_iInf t] at this
  linarith


/-! ### Non-degeneracy of the witness

Three checks that the refutation is not an artifact of a trivial MDP: the
trajectory actually moves, the optimum is really `1`, and the value really is
strictly suboptimal at every finite time (so nothing is being smuggled in by the
policy reaching a vertex of the simplex). -/

/-- **Gradient ascent genuinely moves.**  The logit gap between the two tied
optimal actions strictly increases at the very first step, so this is not the
`unreachMDP`-style situation where the gradient vanishes identically. -/
theorem tie_moves : tiex 0 < tiex 1 := by
  rw [tiex_succ 0]
  have h2 := tieP_pos 0 2
  have hgap : tieP 0 0 < tieP 0 1 := by
    rw [tieP_zero_eq 0]
    have h1 := tieP_pos 0 1
    have : Real.exp (- tiex 0) < 1 := by
      rw [Real.exp_lt_one_iff, tiex_zero]; norm_num
    nlinarith
  nlinarith

/-- **The value is strictly suboptimal at every finite time.**

Softmax never puts probability `0` on the suboptimal action `2`, so
`V^{π_t}(0) < V*(0)` always — while `tie_hconv` gives convergence.  The optimum
is approached, never attained, exactly as in the real algorithm. -/
theorem tie_lt_Vstar (t : ℕ) :
    Vinf tieMDP (tieF.toPolicy (tieTh t)) 0 < Vstar tieMDP 0 := by
  rw [tie_Vinf _ 0, tie_Vstar]
  have h := tieP_sum t
  have h2 := tieP_pos t 2
  show tieRbar (tieF.toPolicy (tieTh t)) < 1
  rw [tie_V t]
  linarith

end ReductionFalse

/-! ## What survives

Two things are true and are recorded here so the next attempt starts from them
rather than from the frozen statement.

1. **For each fixed `t` the infimum is positive** (`iInf_pi_pos`).  Softmax is
   strictly positive and `S` is finite, so `⨅ s, π_t(a|s) > 0` at every single
   time.  The frozen goal is the *uniform in `t`* strengthening, and that is the
   part the tie breaks.

2. **The correct hypothesis is a limit condition on the policy, not on the
   value** (`g9_of_policy_limit`).  If the policies converge coordinatewise to
   some `πbar` that still puts positive mass on `a*(s)` at every `s`, then a
   uniform `c > 0` does exist.  This is what a proof of G9 has to supply, and it
   is strictly stronger than `V(θ_t) → V*(μ)`: the witness above satisfies the
   value hypothesis and violates the policy hypothesis (`πbar(0|0) = 0`).
-/

section Survives

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

omit [DecidableEq S] in
/-- **The easy half: at each fixed time the infimum is strictly positive.** -/
theorem iInf_pi_pos (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : E S A) (astar : S → A) :
    0 < ⨅ s : S, (F.toPolicy θ s) (astar s) := by
  classical
  obtain ⟨s₀, -, hmin⟩ := Finset.exists_min_image (univ : Finset S)
    (fun s => (F.toPolicy θ s) (astar s)) ⟨Classical.arbitrary S, mem_univ _⟩
  have hle : (⨅ s : S, (F.toPolicy θ s) (astar s))
      = (F.toPolicy θ s₀) (astar s₀) := by
    refine le_antisymm (ciInf_le ⟨0, ?_⟩ s₀) (le_ciInf fun s => hmin s (mem_univ s))
    rintro y ⟨s, rfl⟩
    exact (F.toPolicy θ s).nonneg _
  rw [hle, hF]
  exact softmax_pos _ _

/-- **The reduction that is actually true.**

If the policy sequence converges coordinatewise to `πbar` and `πbar` keeps
positive mass on every `a*(s)`, then a single `c > 0` bounds
`⨅ s, π_t(a*(s)|s)` from below for **all** `t`.

Compare `g9_of_convergence_is_false`: replacing this hypothesis by
`V(θ_t) → V*(μ)` makes the statement false, because value convergence does not
prevent the trajectory from abandoning one of two **tied** optimal actions.

Proof: the finitely many coordinate limits are positive, so `⨅ s, πbar(a*(s)|s)`
is positive; convergence puts all but finitely many terms above half of it; and
the finitely many exceptional terms are positive by `iInf_pi_pos`.  Take the
minimum. -/
theorem g9_of_policy_limit (F : VecPolicy S A (E S A))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (θ : ℕ → E S A) (astar : S → A) (πbar : Policy S A)
    (hlim : Filter.Tendsto (fun t s a => (F.toPolicy (θ t) s) a) Filter.atTop
      (nhds (fun s a => (πbar s) a)))
    (hpos : ∀ s, 0 < (πbar s) (astar s)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, c ≤ ⨅ s : S, (F.toPolicy (θ t) s) (astar s) := by
  classical
  -- the limiting infimum is positive
  set m : ℝ := ⨅ s : S, (πbar s) (astar s) with hm
  have hmpos : 0 < m := by
    obtain ⟨s₀, -, hmin⟩ := Finset.exists_min_image (univ : Finset S)
      (fun s => (πbar s) (astar s)) ⟨Classical.arbitrary S, mem_univ _⟩
    have : m = (πbar s₀) (astar s₀) := by
      refine le_antisymm (ciInf_le ⟨0, ?_⟩ s₀) (le_ciInf fun s => hmin s (mem_univ s))
      rintro y ⟨s, rfl⟩
      exact (πbar s).nonneg _
    rw [this]; exact hpos s₀
  -- coordinatewise convergence at the selected actions
  have hcoord : ∀ s, Filter.Tendsto (fun t => (F.toPolicy (θ t) s) (astar s))
      Filter.atTop (nhds ((πbar s) (astar s))) := by
    intro s
    have h1 := (continuous_apply s).continuousAt.tendsto.comp hlim
    exact ((continuous_apply (astar s)).continuousAt.tendsto.comp h1)
  -- eventually every coordinate exceeds `m/2`
  have hev : ∀ s, ∀ᶠ t in Filter.atTop, m / 2 < (F.toPolicy (θ t) s) (astar s) := by
    intro s
    refine (hcoord s).eventually (eventually_gt_nhds ?_)
    have : m ≤ (πbar s) (astar s) := by
      refine ciInf_le ⟨0, ?_⟩ s
      rintro y ⟨x, rfl⟩
      exact (πbar x).nonneg _
    linarith
  have hall : ∀ᶠ t in Filter.atTop, ∀ s, m / 2 < (F.toPolicy (θ t) s) (astar s) :=
    (Filter.eventually_all (p := fun s t => m / 2 < (F.toPolicy (θ t) s) (astar s))).2 hev
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  -- the finitely many early terms are positive
  set early : Finset ℕ := Finset.range N with hearly
  set c : ℝ := min (m / 2)
    (if h : early.Nonempty then
      early.inf' h (fun t => ⨅ s : S, (F.toPolicy (θ t) s) (astar s)) else m / 2) with hc
  refine ⟨c, ?_, ?_⟩
  · rw [hc]
    refine lt_min (by linarith) ?_
    by_cases h : early.Nonempty
    · rw [dif_pos h]
      exact (Finset.lt_inf'_iff h).2 fun t _ => iInf_pi_pos F hF (θ t) astar
    · rw [dif_neg h]; linarith
  · intro t
    by_cases ht : N ≤ t
    · refine le_trans (min_le_left _ _) ?_
      refine le_ciInf fun s => ?_
      exact (hN t ht s).le
    · push_neg at ht
      have hmem : t ∈ early := Finset.mem_range.mpr ht
      have hne : early.Nonempty := ⟨t, hmem⟩
      refine le_trans (min_le_right _ _) ?_
      rw [dif_pos hne]
      exact Finset.inf'_le _ hmem

end Survives

end Proofs
end PolicyGradient
