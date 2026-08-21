/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Value

/-!
# The Markov chain induced by a policy

`step` is the one-step state-transition matrix and `visit k s₀ s = Pr(s_k = s | s₀)`.
Nothing here involves differentiation: these are facts about the chain a policy
induces, needed by every theorem in the development.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- One-step state-transition matrix induced by `π`. -/
noncomputable def step (M : FiniteMDP S A) (π : Policy S A) (s s' : S) : ℝ :=
  ∑ a, (π s) a * (M.P s a) s'

/-- `visit M π k s₀ s = Pr(s_k = s | s₀)` under `π`. -/
noncomputable def visit (M : FiniteMDP S A) (π : Policy S A) : ℕ → S → S → ℝ
  | 0, s₀, s => if s = s₀ then 1 else 0
  | k + 1, s₀, s => ∑ s', visit M π k s₀ s' * step M π s' s

@[simp] theorem visit_zero (M : FiniteMDP S A) (π : Policy S A) (s₀ s : S) :
    visit M π 0 s₀ s = if s = s₀ then 1 else 0 := rfl

theorem visit_succ (M : FiniteMDP S A) (π : Policy S A) (k : ℕ) (s₀ s : S) :
    visit M π (k + 1) s₀ s = ∑ s', visit M π k s₀ s' * step M π s' s := rfl

/-- Chapman-Kolmogorov: taking the step first or last gives the same visitation.

`∑ s', step s₀ s' * visit k s' s = visit (k+1) s₀ s = ∑ s', visit k s₀ s' * step s' s`

The right-hand equality is `visit_succ` by definition; the left-hand one is the
content of this lemma, proved by induction on `k`. Stated for an arbitrary policy: this is a fact about the induced Markov
chain and has nothing to do with differentiability. -/
theorem step_visit (M : FiniteMDP S A) (π : Policy S A) (k : ℕ) (s₀ s : S) :
    ∑ s', step M π s₀ s' * visit M π k s' s
      = visit M π (k + 1) s₀ s := by
  induction k generalizing s₀ s with
  | zero =>
    -- both sides collapse to `step s₀ s`
    simp [visit_zero, visit_succ]
  | succ k ih =>
    -- LHS: ∑ s', step s₀ s' * ∑ t, visit k s' t * step t s
    -- RHS: ∑ s', (∑ t, visit k s₀ t * step t s') * step s' s
    -- Flatten both to double sums, swap on the left, then apply ih.
    simp only [visit_succ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := ih s₀ t
    calc ∑ s', step M π s₀ s' * (visit M π k s' t
              * step M π t s)
        = (∑ s', step M π s₀ s' * visit M π k s' t)
              * step M π t s := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun s' _ => ?_; ring
      _ = visit M π (k + 1) s₀ t * step M π t s := by
          rw [this]
      _ = ∑ s', visit M π k s₀ s' * step M π s' t
              * step M π t s := by
          rw [visit_succ, Finset.sum_mul]



end PolicyGradient
