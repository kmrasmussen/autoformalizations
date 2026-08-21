/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Defs

/-!
# Finite-horizon value functions

`V m π s` is the expected discounted return from `s` with `m` steps remaining.
Defined by backward recursion:

  V 0       π s = 0
  V (m+1)   π s = ∑ a, π s a * (r s a + γ * ∑ s', P s a s' * V m π s')

`Q m π s a` is the value of taking `a` now and following `π` for the remaining
`m` steps. Note the indexing: `Q (m+1)` pairs with `V (m+1)`, and unfolds to `V m`.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Expected discounted return from `s` with `m` steps remaining. -/
noncomputable def V (M : FiniteMDP S A) (π : Policy S A) : ℕ → S → ℝ
  | 0, _ => 0
  | m + 1, s => ∑ a, (π s) a * (M.r s a + M.γ * ∑ s', (M.P s a) s' * V M π m s')

/-- Action-value: take `a` now, then follow `π` for `m` more steps. -/
noncomputable def Q (M : FiniteMDP S A) (π : Policy S A) (m : ℕ) (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * ∑ s', (M.P s a) s' * V M π m s'

@[simp] theorem V_zero (M : FiniteMDP S A) (π : Policy S A) (s : S) :
    V M π 0 s = 0 := rfl

theorem V_succ (M : FiniteMDP S A) (π : Policy S A) (m : ℕ) (s : S) :
    V M π (m + 1) s = ∑ a, (π s) a * Q M π m s a := rfl

end PolicyGradient
