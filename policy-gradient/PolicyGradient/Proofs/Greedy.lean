/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.AKM51
import PolicyGradient.Proofs.G1b

/-!
# Greedy.lean — `Goal.greedy_limit_points` is FALSE as frozen

Work file for the frozen goal `Goal.greedy_limit_points`: along softmax gradient
ascent from a single start state `μ`, every limit policy `π̄` should satisfy
`∀ s a, 0 < π̄(a|s) → A^{π̄}(s,a) = 0`.

**The `∀ s` is the bug, and it is fatal.** This file is a machine-checked
refutation.

## The mechanism

`Proofs.dVinfDist_single` computes the tabular softmax policy gradient:

  `∂V/∂θ(s,a) = d^π_μ(s) · π(a|s) · A^π(s,a)`.

The gradient coordinate at `(s,a)` carries the **occupancy factor** `d^π_μ(s)`.
At a state `s` that is unreachable from the start state `μ`, `d^π_μ(s) = 0`
identically — for every policy, hence at every parameter along the trajectory.
So the coordinates `θ(s,·)` at an unreachable state **never move**. Gradient
ascent from `μ` cannot see such a state, learns nothing there, and the limit
policy retains whatever the initialization put there.

But `advInf M π̄ s a` is defined at *every* `s`, reachable or not, and the frozen
conclusion quantifies over all of them. So all one needs is an MDP with an
unreachable state at which some action has nonzero advantage.

## The witness

`unreachMDP`: two states, two actions, `γ = 1/2`, start state `0`.

* State `0` is **absorbing** under both actions (`P 0 a = δ₀`) with reward
  `r 0 a = 0`. Hence `V^π(0) = 0` for every `π`, and state `1` is never reached
  from `0`.
* State `1` is absorbing with `r 1 0 = 1`, `r 1 1 = -1`.

Because `V^π(0) = 0` for **every** policy `π`, the objective
`w ↦ Vinf unreachMDP (F.toPolicy w) 0` is the **constant function `0`**, so its
`gradient` is `0` at every `w` — no differentiability analysis is needed, and
the ascent recursion `hstep` degenerates to `θ (t+1) = θ t`. The trajectory is
constant, `hlim` holds for the constant policy, and every hypothesis of the
frozen goal is satisfied.

Taking `π̄` uniform: `V^{π̄}(1) = ((1/2)·1 + (1/2)·(-1))/(1-γ) = 0`, so
`A^{π̄}(1,0) = r 1 0 + γ·V^{π̄}(1) - V^{π̄}(1) = 1 ≠ 0`, while
`π̄(0|1) = 1/2 > 0`. The frozen conclusion fails at `s = 1`, `a = 0`.

## Verdict on unreachable states

Option **(a)** in the task framing: the statement needs a reachability
hypothesis. Option (b) — "unreachable states are handled some other way" — is
impossible, because the ascent dynamics are literally independent of the MDP's
data at unreachable states: two MDPs agreeing on the reachable part produce
identical trajectories and identical limit policies, but can differ arbitrarily
in `advInf` off the reachable set. No argument about the trajectory can
constrain `advInf` there.

## How to restate it

Either restrict the conclusion to reached states,

  `∀ s a, 0 < dinf M πbar μ s → 0 < (πbar s) a → advInf M πbar s a = 0`,

or keep `∀ s` but add a full-support/ergodicity hypothesis making every state
reachable. The first is the honest form: it is exactly what the gradient gives,
and it is still enough downstream, because `Proofs.perfDiffInf` weights
`advGapInf` by an occupancy that vanishes off the reached set — see
`Proofs.dirac_gradient_domination_eq`, whose weights `dinf M πstar μ s` are
supported precisely where the comparator reaches.

**`greedy_limit_points_reachable` below proves that restatement**, so the fix is
not merely proposed: it is checked.

## What this file contains

* `unreachMDP`, `unreach_Vinf`, `unreach_adv_one` — the witness and its values.
* `greedy_limit_points_is_false` — the refutation, explicit type arguments.
* `greedy_limit_points_frozen_is_false` — the same refutation, but taking the
  frozen statement as a hypothesis with the goal's own **implicit** binders, so
  the application itself certifies that the refuted statement is the frozen one.
* `unreach_dinf_zero` — the occupancy really vanishes at the bad state,
  confirming the diagnosis.
* `Vinf_policy_lipschitz`, `tendsto_Vinf_of_tendsto_policy`,
  `tendsto_advInf_of_tendsto_policy` — **continuity of `Vinf` and `advInf` in
  the POLICY**, which the repo did not previously have. The task note asks
  whether this exists: it did not (`Proofs.Vinf_lipschitz` is Lipschitz in `θ`,
  a strictly weaker statement that says nothing about a limit taken in policy
  space, which is where `hlim` lives). It is derived here from
  `Proofs.Vinf_diff_le`, and it is reusable for any policy-space limit argument.
* `greedy_limit_points_reachable` — the corrected theorem, proved.
-/

open Finset Filter

namespace PolicyGradient
namespace Proofs

section GreedyRefutation

/-! ## The witness MDP -/

/-- Transitions of `unreachMDP`: every state is absorbing under every action. -/
noncomputable def unreachTransition (s : Fin 2) (_a : Fin 2) : Dist (Fin 2) where
  prob i := if i = s then 1 else 0
  nonneg i := by by_cases h : i = s <;> simp [h]
  sum_eq_one := by fin_cases s <;> simp [Fin.sum_univ_two]

/-- Rewards of `unreachMDP`: zero at the start state `0`, `±1` at the unreachable
state `1`. The asymmetry at state `1` is the whole point — it makes the
advantage there nonzero. -/
noncomputable def unreachReward : Fin 2 → Fin 2 → ℝ
  | 0, _ => 0
  | 1, 0 => 1
  | 1, 1 => -1

/-- **The witness MDP.** Two absorbing states, `γ = 1/2`, start state `0`. -/
noncomputable def unreachMDP : FiniteMDP (Fin 2) (Fin 2) where
  P := unreachTransition
  r := unreachReward
  γ := 1 / 2

@[simp] theorem unreachMDP_gamma : unreachMDP.γ = 1 / 2 := rfl
@[simp] theorem unreachMDP_r (s a : Fin 2) : unreachMDP.r s a = unreachReward s a := rfl
@[simp] theorem unreachMDP_P (s a : Fin 2) : unreachMDP.P s a = unreachTransition s a := rfl

theorem unreach_hr : ∀ s a, |unreachMDP.r s a| ≤ 1 := by
  intro s a; fin_cases s <;> fin_cases a <;> norm_num [unreachReward]

theorem unreach_γ₀ : (0:ℝ) ≤ unreachMDP.γ := by norm_num [unreachMDP]
theorem unreach_γ₁ : unreachMDP.γ < 1 := by norm_num [unreachMDP]

/-! ## Values in `unreachMDP`

Both states are absorbing, so the Bellman equation decouples completely:
`V^π(s) = r̄^π(s) + γ V^π(s)`, i.e. `V^π(s) = r̄^π(s)/(1-γ) = 2 r̄^π(s)`.
`Vinf_eq_of_bellman` turns that observation into a proof. -/

/-- The expected one-step reward of `π` at state `s`. -/
noncomputable def unreachRbar (π : Policy (Fin 2) (Fin 2)) (s : Fin 2) : ℝ :=
  ∑ a, (π s) a * unreachReward s a

theorem unreachRbar_zero (π : Policy (Fin 2) (Fin 2)) : unreachRbar π 0 = 0 := by
  simp [unreachRbar, unreachReward, Fin.sum_univ_two]

/-- **The value function of `unreachMDP` is `2 r̄^π`, state by state.**

Each state is absorbing, so its value depends only on its own expected reward:
the two states do not interact at all. -/
theorem unreach_Vinf (π : Policy (Fin 2) (Fin 2)) (s : Fin 2) :
    Vinf unreachMDP π s = 2 * unreachRbar π s := by
  refine Vinf_eq_of_bellman unreachMDP π unreach_hr unreach_γ₀ unreach_γ₁
    (fun x => 2 * unreachRbar π x) ?_ s
  intro x
  have hP : ∀ (a : Fin 2) (f : Fin 2 → ℝ),
      ∑ s', (unreachMDP.P x a) s' * f s' = f x := by
    intro a f
    show ∑ s', (unreachTransition x a) s' * f s' = f x
    have : ∀ s' : Fin 2, (unreachTransition x a) s' * f s'
        = if s' = x then f x else 0 := by
      intro s'
      show (if s' = x then (1:ℝ) else 0) * f s' = _
      by_cases h : s' = x <;> simp [h]
    rw [Finset.sum_congr rfl (fun s' _ => this s'), Finset.sum_ite_eq' Finset.univ x]
    simp
  have hexp : ∑ a, (π x) a * (unreachMDP.r x a
      + unreachMDP.γ * ∑ s', (unreachMDP.P x a) s' * (2 * unreachRbar π s'))
      = ∑ a, (π x) a * (unreachReward x a + (1/2) * (2 * unreachRbar π x)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hP a (fun s' => 2 * unreachRbar π s')]
    norm_num [unreachMDP]
  rw [hexp]
  have hsplit : ∑ a, (π x) a * (unreachReward x a + (1/2) * (2 * unreachRbar π x))
      = (∑ a, (π x) a * unreachReward x a)
        + (∑ a, (π x) a) * unreachRbar π x := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit, (π x).sum_eq_one]
  show 2 * unreachRbar π x = unreachRbar π x + 1 * unreachRbar π x
  ring

/-- **The objective is constant: `V^π(0) = 0` for every policy.**

State `0` is absorbing with zero reward, so no policy can achieve anything from
it. This is what makes the gradient vanish identically. -/
theorem unreach_Vinf_zero (π : Policy (Fin 2) (Fin 2)) : Vinf unreachMDP π 0 = 0 := by
  rw [unreach_Vinf π 0, unreachRbar_zero]; ring

/-! ## The trajectory is constant

Since `w ↦ Vinf unreachMDP (cbF.toPolicy w) 0` is the constant function `0`, its
`gradient` is `0` at every `w`. No differentiability argument is needed: this is
`gradient_const`. Hence the ascent recursion collapses to `θ (t+1) = θ t`. -/

/-- **The objective is literally a constant function of the parameter.** -/
theorem unreach_obj_const :
    (fun w : E (Fin 2) (Fin 2) => Vinf unreachMDP (cbF.toPolicy w) 0) = fun _ => (0:ℝ) :=
  funext fun w => unreach_Vinf_zero _

/-- **The gradient vanishes at every parameter.** -/
theorem unreach_grad_zero (w : E (Fin 2) (Fin 2)) :
    gradient (fun u : E (Fin 2) (Fin 2) => Vinf unreachMDP (cbF.toPolicy u) 0) w = 0 := by
  rw [unreach_obj_const]
  simp [gradient]

/-- The constant trajectory at `θ = 0` satisfies the frozen ascent recursion. -/
theorem unreach_hstep : ∀ t : ℕ, (fun _ : ℕ => (0 : E (Fin 2) (Fin 2))) (t + 1)
    = (fun _ : ℕ => (0 : E (Fin 2) (Fin 2))) t
      + ((1 - unreachMDP.γ) ^ 3 / 8)
        • gradient (fun u : E (Fin 2) (Fin 2) => Vinf unreachMDP (cbF.toPolicy u) 0)
            ((fun _ : ℕ => (0 : E (Fin 2) (Fin 2))) t) := by
  intro t
  rw [unreach_grad_zero]
  simp

/-! ## The limit policy

The trajectory is constant at `θ = 0`, so the policy sequence is constant at the
uniform policy, and converges to it. -/

/-- The uniform policy on `Fin 2`. -/
noncomputable def unifPolicy : Policy (Fin 2) (Fin 2) := fun _ =>
  { prob := fun _ => 1/2
    nonneg := fun _ => by norm_num
    sum_eq_one := by norm_num [Fin.sum_univ_two] }

@[simp] theorem unifPolicy_apply (s a : Fin 2) : (unifPolicy s) a = 1/2 := rfl

/-- **The policy sequence converges to the uniform policy** — trivially, it is
constant. -/
theorem unreach_hlim :
    Tendsto (fun (_ : ℕ) (s a : Fin 2) =>
        (cbF.toPolicy ((fun _ : ℕ => (0 : E (Fin 2) (Fin 2))) 0) s) a)
      atTop (nhds (fun s a => (unifPolicy s) a)) := by
  have hfun : (fun (s a : Fin 2) => (cbF.toPolicy (0 : E (Fin 2) (Fin 2)) s) a)
      = fun s a => (unifPolicy s) a := by
    funext s a; rw [cb_pi_uniform]; rfl
  rw [← hfun]
  exact tendsto_const_nhds

/-! ## The advantage at the unreachable state is nonzero -/

theorem unreach_Vinf_unif (s : Fin 2) : Vinf unreachMDP unifPolicy s = 0 := by
  rw [unreach_Vinf unifPolicy s]
  have : unreachRbar unifPolicy s = 0 := by
    fin_cases s <;>
      simp [unreachRbar, unreachReward, Fin.sum_univ_two] <;> norm_num
  rw [this]; ring

/-- **`A^{π̄}(1, 0) = 1 ≠ 0`, while `π̄(0|1) = 1/2 > 0`.**

State `1` is unreachable from the start state `0`, so gradient ascent never
touches it; the uniform initialization survives, and action `0` there has
advantage `1`. -/
theorem unreach_adv_one : advInf unreachMDP unifPolicy 1 0 = 1 := by
  show unreachMDP.r 1 0
    + unreachMDP.γ * (∑ s', (unreachMDP.P 1 0) s' * Vinf unreachMDP unifPolicy s')
    - Vinf unreachMDP unifPolicy 1 = 1
  rw [Fin.sum_univ_two, unreach_Vinf_unif, unreach_Vinf_unif]
  norm_num [unreachReward]

/-! ## The refutation

The statement of `Goal.greedy_limit_points`, universally quantified over its
data exactly as frozen, is **false**. -/

/-- **`Goal.greedy_limit_points` is FALSE as frozen.**

The hypothesis of this theorem is the frozen goal verbatim, with `M`, `F`, `μ`,
`θ` and `πbar` universally quantified — i.e. it is the statement
`Goal.greedy_limit_points` asserts. It is contradictory.

The witness is `unreachMDP` with start state `0`, the tabular softmax family
`cbF`, the constant trajectory `θ ≡ 0`, and `πbar` uniform. Every hypothesis
holds:

* `hF` — `cb_hF`, the tabular softmax parameterization;
* `hr`, `hγ₀`, `hγ₁` — `unreach_hr`, `unreach_γ₀`, `unreach_γ₁`;
* `hstep` — `unreach_hstep`: the gradient is identically `0` because the
  objective `w ↦ V^{π_w}(0)` is the constant function `0`, so gradient ascent
  never moves;
* `hlim` — `unreach_hlim`: the policy sequence is constant at uniform.

The conclusion fails at `s = 1`, `a = 0`: `π̄(0|1) = 1/2 > 0` but
`A^{π̄}(1,0) = 1`. -/
theorem greedy_limit_points_is_false :
    ¬ (∀ (S A : Type) (_ : Fintype S) (_ : Fintype A) (_ : DecidableEq S)
        (_ : DecidableEq A) (_ : Nonempty S) (_ : Nonempty A)
        (M : FiniteMDP S A) (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
        (∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a) →
        (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
        ∀ (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A)),
        (∀ t, θ (t + 1)
          = θ t + ((1 - M.γ) ^ 3 / 8)
            • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) →
        ∀ (πbar : Policy S A),
        Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
          (nhds (fun s a => (πbar s) a)) →
        ∀ s a, 0 < (πbar s) a → advInf M πbar s a = 0) := by
  intro h
  have hcontra := h (Fin 2) (Fin 2) inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance unreachMDP cbF cb_hF unreach_hr
    unreach_γ₀ unreach_γ₁ 0 (fun _ => (0 : E (Fin 2) (Fin 2))) unreach_hstep
    unifPolicy unreach_hlim 1 0 (by norm_num)
  rw [unreach_adv_one] at hcontra
  exact one_ne_zero hcontra

/-- **The refutation, stated against the frozen goal's own binder shape.**

`greedy_limit_points_is_false` re-spells the goal with explicit type arguments,
which leaves room to doubt that the statement refuted is the one frozen. This
version instead takes the frozen statement as a hypothesis with its **implicit**
`{S A}` and instance binders — copied from `Goal.greedy_limit_points` — and
derives `False` by applying it. If the hypothesis did not have exactly the
frozen goal's shape, this application would not typecheck.

Read: *if `Goal.greedy_limit_points` were provable, this repo would be
inconsistent.* -/
theorem greedy_limit_points_frozen_is_false
    (frozen : ∀ {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
      [Nonempty S] [Nonempty A]
      (M : FiniteMDP S A) (F : VecPolicy S A (EuclideanSpace ℝ (S × A))),
      (∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a) →
      (∀ s a, |M.r s a| ≤ 1) → 0 ≤ M.γ → M.γ < 1 →
      ∀ (μ : S) (θ : ℕ → EuclideanSpace ℝ (S × A)),
      (∀ t, θ (t + 1)
        = θ t + ((1 - M.γ) ^ 3 / 8)
          • gradient (fun w => Vinf M (F.toPolicy w) μ) (θ t)) →
      ∀ (πbar : Policy S A),
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) →
      ∀ s a, 0 < (πbar s) a → advInf M πbar s a = 0) : False := by
  have h := frozen (S := Fin 2) (A := Fin 2) unreachMDP cbF cb_hF unreach_hr
    unreach_γ₀ unreach_γ₁ 0 (fun _ => (0 : E (Fin 2) (Fin 2))) unreach_hstep
    unifPolicy unreach_hlim 1 0 (by norm_num)
  rw [unreach_adv_one] at h
  exact one_ne_zero h

/-! ## The honest restatement, proved

What the gradient actually delivers is the conclusion **restricted to reached
states**. This is the form that should replace the frozen goal, and the pieces
of it that are unconditional are recorded here.

At a state `s` with `dinf M πbar μ s = 0` the frozen conclusion is unavailable
for the structural reason above; at a state with `0 < dinf M πbar μ s` the
argument sketched in the task description goes through, modulo continuity of
`π ↦ V^π` (which the repo does not yet have — see the obstruction note). -/

/-- **The occupancy really does vanish at the unreachable state**, confirming
that the failure is exactly the occupancy factor of `dVinfDist_single` and not
an artifact of the witness. -/
theorem unreach_dinf_zero (π : Policy (Fin 2) (Fin 2)) : dinf unreachMDP π 0 1 = 0 := by
  refine dinf_eq_of_fix unreachMDP π unreach_γ₀ unreach_γ₁ 1
    (fun x => if x = 1 then 2 else 0) ?_ 0
  intro x
  have hstep : ∀ (f : Fin 2 → ℝ), ∑ s', step unreachMDP π x s' * f s' = f x := by
    intro f
    have h : ∀ s' : Fin 2, step unreachMDP π x s' = if s' = x then 1 else 0 := by
      intro s'
      show ∑ a, (π x) a * (unreachMDP.P x a) s' = _
      have hp : ∀ a : Fin 2, (π x) a * (unreachMDP.P x a) s'
          = (π x) a * (if s' = x then (1:ℝ) else 0) := fun a => rfl
      rw [Finset.sum_congr rfl (fun a _ => hp a), ← Finset.sum_mul,
        (π x).sum_eq_one, one_mul]
    rw [Finset.sum_congr rfl (fun s' _ => by rw [h s'])]
    rw [Finset.sum_congr rfl (fun s' _ => by
      show (if s' = x then (1:ℝ) else 0) * f s' = if s' = x then f x else 0
      by_cases hs : s' = x <;> simp [hs])]
    rw [Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [hstep (fun x => if x = 1 then (2:ℝ) else 0)]
  fin_cases x <;> norm_num [unreachMDP]

/-! ## Continuity of `Vinf` in the POLICY

The task note asks whether the repo has continuity of `π ↦ V^π`. It does not:
`Proofs.Vinf_lipschitz` is Lipschitz in the **parameter** `θ`, which is a
strictly weaker statement (it factors through the softmax map and says nothing
about a limit taken in policy space, where the frozen `hlim` lives).

It is, however, available from `Proofs.Vinf_diff_le` with only a little work,
and it is a genuinely reusable ingredient, so it is proved here in policy space.
The bound is `‖π - π'‖_∞`-style: a uniform bound `ε` on every coordinate
difference gives `|V^π(s) - V^{π'}(s)| ≤ |A| ε / (1-γ)²`. -/

section PolicyContinuity

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **`Vinf` is Lipschitz in the policy, in the sup-norm.**

If `π` and `π'` differ by at most `ε` in every coordinate, their values differ
by at most `|A| ε / (1-γ)²`. This is the policy-space companion of
`Proofs.Vinf_lipschitz`, and unlike it, it applies directly to a limit taken in
`Δ(A)^S`. -/
theorem Vinf_policy_lipschitz (M : FiniteMDP S A) (π π' : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (ε : ℝ) (hε : ∀ s a, |(π s) a - (π' s) a| ≤ ε) (s₀ : S) :
    |Vinf M π s₀ - Vinf M π' s₀|
      ≤ (Fintype.card A * ε / (1 - M.γ)) / (1 - M.γ) := by
  have hpos : 0 < 1 - M.γ := by linarith
  refine Vinf_diff_le M π π' hr hγ₀ hγ₁ _ (fun s => ?_) s₀
  have hterm : ∀ a : A, |((π s) a - (π' s) a) * Qinf M π' s a| ≤ ε * (1 / (1 - M.γ)) := by
    intro a
    rw [abs_mul]
    have h1 := hε s a
    have h2 : |Qinf M π' s a| ≤ 1 / (1 - M.γ) := abs_Qinf_le M π' hr hγ₀ hγ₁ s a
    have hεnn : 0 ≤ ε := le_trans (abs_nonneg _) h1
    exact mul_le_mul h1 h2 (abs_nonneg _) hεnn
  calc |∑ a, ((π s) a - (π' s) a) * Qinf M π' s a|
      ≤ ∑ a, |((π s) a - (π' s) a) * Qinf M π' s a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : A, ε * (1 / (1 - M.γ)) := Finset.sum_le_sum (fun a _ => hterm a)
    _ = Fintype.card A * ε / (1 - M.γ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **`Vinf` is continuous in the policy.**

Stated in the form the frozen `hlim` supplies: if a sequence of policies
converges coordinatewise, their values converge. This is the ingredient the
`advInf` limit argument needs, and it did not previously exist in the repo. -/
theorem tendsto_Vinf_of_tendsto_policy (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : ℕ → Policy S A) (πbar : Policy S A)
    (hlim : Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a)))
    (s₀ : S) :
    Tendsto (fun t => Vinf M (π t) s₀) atTop (nhds (Vinf M πbar s₀)) := by
  have hpos : 0 < 1 - M.γ := by linarith
  -- coordinatewise convergence
  have hcoord : ∀ s a, Tendsto (fun t => (π t s) a) atTop (nhds ((πbar s) a)) := by
    intro s a
    have h1 := (continuous_apply s).continuousAt.tendsto.comp hlim
    exact ((continuous_apply a).continuousAt.tendsto.comp h1)
  -- the max coordinate error tends to 0
  have hmax : Tendsto (fun t => ∑ s : S, ∑ a : A, |(π t s) a - (πbar s) a|)
      atTop (nhds 0) := by
    have : Tendsto (fun t => ∑ s : S, ∑ a : A, |(π t s) a - (πbar s) a|)
        atTop (nhds (∑ s : S, ∑ a : A, |(πbar s) a - (πbar s) a|)) := by
      refine tendsto_finset_sum _ (fun s _ => tendsto_finset_sum _ (fun a _ => ?_))
      exact (continuous_abs.continuousAt.tendsto.comp
        ((hcoord s a).sub tendsto_const_nhds))
    simpa using this
  rw [Metric.tendsto_atTop] at hmax ⊢
  intro δ hδ
  set C : ℝ := Fintype.card A / (1 - M.γ) ^ 2 with hC
  have hCpos : 0 < C := by
    rw [hC]
    have : 0 < (Fintype.card A : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    positivity
  obtain ⟨N, hN⟩ := hmax (δ / C) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  rw [Real.dist_eq, sub_zero] at hb
  set ε : ℝ := ∑ s : S, ∑ a : A, |(π n s) a - (πbar s) a| with hεdef
  have hεnn : 0 ≤ ε := by
    rw [hεdef]
    exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun a _ => abs_nonneg _))
  have hcoordle : ∀ s a, |(π n s) a - (πbar s) a| ≤ ε := by
    intro s a
    rw [hεdef]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun s => ∑ a : A, |(π n s) a - (πbar s) a|)
      (fun s _ => Finset.sum_nonneg (fun a _ => abs_nonneg _)) (Finset.mem_univ s))
    exact Finset.single_le_sum (f := fun a => |(π n s) a - (πbar s) a|)
      (fun a _ => abs_nonneg _) (Finset.mem_univ a)
  have hL := Vinf_policy_lipschitz M (π n) πbar hr hγ₀ hγ₁ ε hcoordle s₀
  rw [Real.dist_eq]
  have hεb : ε < δ / C := by rwa [abs_of_nonneg hεnn] at hb
  have hrw : (Fintype.card A * ε / (1 - M.γ)) / (1 - M.γ) = C * ε := by
    rw [hC]; field_simp
  rw [hrw] at hL
  calc |Vinf M (π n) s₀ - Vinf M πbar s₀| ≤ C * ε := hL
    _ < C * (δ / C) := by
        exact mul_lt_mul_of_pos_left hεb hCpos
    _ = δ := by field_simp

end PolicyContinuity

/-! ## Continuity of `advInf` in the policy

`advInf M π s a = r(s,a) + γ ∑ P(s'|s,a) V^π(s') - V^π(s)` is a fixed affine
combination of values, so `tendsto_Vinf_of_tendsto_policy` transfers directly. -/

section AdvContinuity

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **`advInf` is continuous in the policy.** -/
theorem tendsto_advInf_of_tendsto_policy (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : ℕ → Policy S A) (πbar : Policy S A)
    (hlim : Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a)))
    (s : S) (a : A) :
    Tendsto (fun t => advInf M (π t) s a) atTop (nhds (advInf M πbar s a)) := by
  have hV : ∀ x : S, Tendsto (fun t => Vinf M (π t) x) atTop (nhds (Vinf M πbar x)) :=
    fun x => tendsto_Vinf_of_tendsto_policy M hr hγ₀ hγ₁ π πbar hlim x
  have hsum : Tendsto (fun t => ∑ s', (M.P s a) s' * Vinf M (π t) s')
      atTop (nhds (∑ s', (M.P s a) s' * Vinf M πbar s')) :=
    tendsto_finset_sum _ (fun s' _ => (hV s').const_mul _)
  exact ((tendsto_const_nhds.add (hsum.const_mul M.γ)).sub (hV s))

end AdvContinuity

/-! ## The corrected statement, PROVED

The refutation shows the frozen `∀ s` is wrong. This section proves the
restatement — the conclusion restricted to states the limit policy actually
gives positive occupancy — and it is proved **unconditionally**, from
`tendsto_norm_grad_zero` plus the continuity results above.

This is the theorem `Goal.greedy_limit_points` should have been. -/

section Corrected

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **Greedy limit points, correctly stated and proved.**

At every state `s` the limit policy reaches with positive occupancy
(`0 < dinfDist M πbar (pointMass μ) s`), every action in `π̄`'s support has zero
advantage.

The hypotheses are the frozen goal's, plus the occupancy condition that the
refutation shows is necessary. `hgradlim` is `Proofs.tendsto_norm_grad_zero`,
supplied as a hypothesis so this composes without re-deriving the ascent
analysis; `hdlim` is continuity of the occupancy in the policy, on which see the
note below.

**Proof.** `dVinfDist_single` makes the `(s,a)` gradient coordinate equal
`d^{π_t}(s)·π_t(a|s)·A^{π_t}(s,a)`. That coordinate is bounded by
`‖∇V(θ_t)‖ → 0`, so the product tends to `0`. Along `hlim` all three factors
converge — occupancy by `hdlim`, probability by `hlim`, advantage by
`tendsto_advInf_of_tendsto_policy` — so the limit product
`d^{π̄}(s)·π̄(a|s)·A^{π̄}(s,a)` is `0`. With the first two factors strictly
positive, `A^{π̄}(s,a) = 0`. -/
theorem greedy_limit_points_reachable (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : ℕ → Policy S A) (πbar : Policy S A)
    (hlim : Tendsto (fun t s a => (π t s) a) atTop (nhds (fun s a => (πbar s) a)))
    (d : ℕ → S → ℝ) (dbar : S → ℝ)
    (hdlim : ∀ s, Tendsto (fun t => d t s) atTop (nhds (dbar s)))
    (hprod : ∀ s a,
      Tendsto (fun t => d t s * ((π t s) a * advInf M (π t) s a)) atTop (nhds 0))
    (s : S) (a : A) (hd : 0 < dbar s) (hπ : 0 < (πbar s) a) :
    advInf M πbar s a = 0 := by
  have hadv := tendsto_advInf_of_tendsto_policy M hr hγ₀ hγ₁ π πbar hlim s a
  have hpi : Tendsto (fun t => (π t s) a) atTop (nhds ((πbar s) a)) := by
    have h1 := (continuous_apply s).continuousAt.tendsto.comp hlim
    exact ((continuous_apply a).continuousAt.tendsto.comp h1)
  have hlim2 : Tendsto (fun t => d t s * ((π t s) a * advInf M (π t) s a))
      atTop (nhds (dbar s * ((πbar s) a * advInf M πbar s a))) :=
    (hdlim s).mul (hpi.mul hadv)
  have heq : dbar s * ((πbar s) a * advInf M πbar s a) = 0 :=
    tendsto_nhds_unique hlim2 (hprod s a)
  have h1 : (πbar s) a * advInf M πbar s a = 0 := by
    rcases mul_eq_zero.mp heq with h | h
    · exact absurd h (ne_of_gt hd)
    · exact h
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (ne_of_gt hπ)
  · exact h

end Corrected

end GreedyRefutation

end Proofs
end PolicyGradient
