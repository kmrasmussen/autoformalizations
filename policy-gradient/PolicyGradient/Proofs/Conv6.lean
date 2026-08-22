/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv5

/-!
# Conv6 — the value-gap vector obeys its own Bellman recursion

WORK IN PROGRESS.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv6

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- The limiting advantage of `Vbar`: `Abar(s,a) = r(s,a) + γ⟨P(·|s,a),Vbar⟩ - Vbar s`.
This is `advInf` with `Vinf M π` replaced by the limit `Vbar`; it is a function of
`Vbar` alone, with no policy in it. -/
noncomputable def advOf (M : FiniteMDP S A) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * (∑ s', (M.P s a) s' * V s') - V s

/-- The **gap source term** `c_t(s) := -∑_a π(a|s) · Abar(s,a)`. -/
noncomputable def gapSource (M : FiniteMDP S A) (Vbar : S → ℝ) (π : Policy S A)
    (s : S) : ℝ :=
  -∑ a, (π s) a * advOf M Vbar s a

/-- **(★) The value-gap Bellman recursion.**  Writing `δ s := Vbar s - V^π s`,

```
δ s = c(s) + γ · ∑_a π(a|s) ∑_{s'} P(s'|s,a) · δ s'
```

with `c = gapSource`.  Unconditional: no limit policy, no hypothesis on `Vbar`
beyond being a function.  It is the exact statement that `δ` is the value of the
*reward* `c` under `π`, i.e. `δ = (I - γ P^π)⁻¹ c`. -/
theorem gap_bellman (M : FiniteMDP S A) (hr : ∀ s a, |M.r s a| ≤ 1)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (Vbar : S → ℝ) (π : Policy S A) (s : S) :
    Vbar s - Vinf M π s
      = gapSource M Vbar π s
        + M.γ * (∑ a, (π s) a * (∑ s', (M.P s a) s' * (Vbar s' - Vinf M π s'))) := by
  classical
  have hV : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  have hone : ∑ a, (π s) a = 1 := (π s).sum_eq_one
  -- expand everything into a single sum over `a`
  have hsplit : ∀ a : A, (π s) a * (∑ s', (M.P s a) s' * (Vbar s' - Vinf M π s'))
      = (π s) a * (∑ s', (M.P s a) s' * Vbar s')
        - (π s) a * (∑ s', (M.P s a) s' * Vinf M π s') := by
    intro a
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    exact congrArg _ (Finset.sum_congr rfl (fun s' _ => by ring))
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hsplit a),
    Finset.sum_sub_distrib]
  unfold gapSource advOf
  rw [hV]
  have hQ : ∀ a : A, (π s) a * Qinf M π s a
      = (π s) a * M.r s a + (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vinf M π s') := by
    intro a; unfold Qinf; ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hQ a),
    Finset.sum_add_distrib]
  have hA : ∀ a : A, (π s) a * (M.r s a + M.γ * (∑ s', (M.P s a) s' * Vbar s') - Vbar s)
      = (π s) a * M.r s a + (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vbar s')
        - (π s) a * Vbar s := by
    intro a; ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hA a),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hone, one_mul]
  have hmulγ : ∀ a : A, (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vbar s')
      = M.γ * ((π s) a * ∑ s', (M.P s a) s' * Vbar s') := by intro a; ring
  have hmulγ' : ∀ a : A, (π s) a * (M.γ * ∑ s', (M.P s a) s' * Vinf M π s')
      = M.γ * ((π s) a * ∑ s', (M.P s a) s' * Vinf M π s') := by intro a; ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hmulγ a),
    Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hmulγ' a),
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end Conv6

end Proofs
end PolicyGradient
