/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1
import PolicyGradient.Proofs.G2

/-!
# Proofs/G2b.lean — AKM Lemma 4.1 in its **directional** form

Discharges the frozen goal `Goal.g2_gradient_domination`:

```
VstarDist M μ - VinfDist M (F.toPolicy θ) μ
  ≤ (mismatchCoeff M πstar μ / (1 - M.γ))
      * (⨆ s, ∑ a, ((πstar s) a - (F.toPolicy θ s) a) * advInf M (F.toPolicy θ) s a)
```

## Why this is not `Proofs/G2.lean` again

`g2_advantage_bound` (now `@[paper_tool]`) has `⨆ s, ⨆ a, |advInf|` on the right.
That is a max of absolute values; this one is a max over states of an *average*
against the signed probability difference `πstar − π`. The directional quantity
is genuinely smaller — every term of the average is `≤ max_a |advInf|` and the
weights sum to `1` — so the old proof does not transfer. In particular the route
of `Proofs/G2.lean` (a max-state contraction bounding the pointwise gap by
`B/(1−γ)` and then weakening through `mismatchCoeff ≥ 1`) is unavailable: the
contraction argument needs an upper bound on the advantage term *at the
maximizing state*, and here the only bound available is the supremum `C` itself,
which is exactly what we are trying to reach — so no slack is left to also pay
for the `1/(1−γ)`.

## ⚠ Naming

The requested name `Proofs.g2_gradient_domination_proof` was **already taken** by
`Proofs/G2.lean`, whose theorem of that name proves the *advantage-form*
statement and is referenced by the frozen `Goal.g2_advantage_bound` (which this
branch may not edit). Renaming it would break `Goal.lean`. This file therefore
declares `Proofs.g2_gradient_domination_directional_proof`, whose type is
*verbatim* the frozen `Goal.g2_gradient_domination`. Wiring it in is a one-line
edit to `Goal.lean` by whoever owns the spec:

```
theorem g2_gradient_domination … :=
  Proofs.g2_gradient_domination_directional_proof M F hF hr hγ₀ hγ₁ μ hμ πstar hstar θ
```

(If `Proofs/G2.lean`'s occupant is retired first, this one can simply take the
plain name.)

## The argument

The exact performance-difference identity is used instead of an inequality
surrogate. `Proofs.VstarDist_sub_VinfDist_eq` (from `Proofs/G1.lean`) gives

`V*_μ − V^π_μ = ∑_s d^{π*}_μ(s) · advGapInf(π, π*, s)`,  `advGapInf = ∑_a π*(a|s)·A^π(s,a)`,

which is AKM's Lemma 4.1 identity. Three steps then close it.

1. **The goal's inner sum is `advGapInf`.** `∑_a (π*(a|s) − π(a|s))·A^π(s,a)`
   equals `∑_a π*(a|s)·A^π(s,a)` because the advantage is centered under its own
   policy: `∑_a π(a|s)·A^π(s,a) = 0`. That is `Proofs.sum_adv_eq` applied twice
   (once with comparator `π*`, once with comparator `π`, whose `advGapInf` is
   then `∑_a π(a|s)·A^π(s,a)` — and `sum_adv_eq M π π` makes its left side the
   telescoping `∑_a (π − π)·Qinf = 0`). See `sum_pi_adv_eq_zero`.

2. **`C ≥ 0`**, where `C := ⨆ s, advGapInf(π, π*, s)`. Read `perfDiffInf_step` at
   the state `sm` maximizing `Δ s = V^{π*}(s) − V^π(s)`: the successor term is a
   convex combination of `Δ`, hence `≤ Δ sm`, so `advGapInf sm ≥ (1−γ)·Δ sm`, and
   `Δ sm ≥ 0` because `π*` is optimal (`vstar_upper_proof` + `hstar`). So the
   supremum is nonnegative even though individual states may have
   `advGapInf < 0`.

3. **Change of measure.** `dinfDist ≤ mismatchCoeff · μ` pointwise
   (`mismatch_bound_proof_of_support`), so with `advGapInf ≤ C` and `C ≥ 0`,

   `∑_s d^{π*}_μ(s)·advGapInf(s) ≤ ∑_s (mismatchCoeff · μ s) · C = mismatchCoeff · C`.

   Finally `1 ≤ 1/(1−γ)` and `mismatchCoeff · C ≥ 0` turn this into the frozen
   right side. (The `1/(1−γ)` is therefore slack here; the sharper
   `≤ mismatchCoeff · C` is recorded as `g2b_sharp` below.)

Like `Proofs/G2.lean` this does not use `hF`: the statement holds for any
differentiable policy family, softmax included. The softmax hypothesis is what
makes the *directional* right side the right object to put a gradient in — the
refuted `‖∇V‖` form loses the `π(a|s)` factor — but the inequality itself is
softmax-free.
-/

open Finset

namespace PolicyGradient
namespace Proofs

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ### Step 1 — the advantage is centered under its own policy -/

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- **`∑_a π(a|s)·A^π(s,a) = 0`.**

`sum_adv_eq M π π` reads `∑_a (π(a|s) − π(a|s))·Q^π(s,a) = ∑_a π(a|s)·A^π(s,a)`;
the left side is a sum of zeros. -/
theorem sum_pi_adv_eq_zero (M : FiniteMDP S A) (π : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    ∑ a, (π s) a * advInf M π s a = 0 := by
  have h := sum_adv_eq M π π hr hγ₀ hγ₁ s
  rw [← h]
  exact Finset.sum_eq_zero fun a _ => by ring

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- **The goal's inner sum is `advGapInf`.**

`∑_a (π*(a|s) − π(a|s))·A^π(s,a) = ∑_a π*(a|s)·A^π(s,a)`, by centering. -/
theorem sum_sub_adv_eq_advGapInf (M : FiniteMDP S A) (π πstar : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    ∑ a, ((πstar s) a - (π s) a) * advInf M π s a = advGapInf M π πstar s := by
  have hsplit : ∑ a, ((πstar s) a - (π s) a) * advInf M π s a
      = (∑ a, (πstar s) a * advInf M π s a)
        - ∑ a, (π s) a * advInf M π s a := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit, sum_pi_adv_eq_zero M π hr hγ₀ hγ₁ s, sub_zero]
  rfl

/-! ### Step 2 — the directional supremum is nonnegative -/

omit [DecidableEq A] in
/-- The family `s ↦ advGapInf M π πstar s` is bounded above (`S` is finite), so
`⨆ s, advGapInf …` is a genuine supremum and not the junk value `0`. -/
theorem bddAbove_advGapInf (M : FiniteMDP S A) (π πstar : Policy S A) :
    BddAbove (Set.range fun s : S => advGapInf M π πstar s) :=
  Finite.bddAbove_range _

omit [DecidableEq A] in
/-- Each state's directional term is at most the supremum. -/
theorem advGapInf_le_ciSup (M : FiniteMDP S A) (π πstar : Policy S A) (s : S) :
    advGapInf M π πstar s ≤ ⨆ s' : S, advGapInf M π πstar s' :=
  le_ciSup (bddAbove_advGapInf M π πstar) s

omit [DecidableEq A] in
/-- **`0 ≤ ⨆ s, ∑_a π*(a|s)·A^π(s,a)` when `π*` is optimal.**

At the state `sm` maximizing `Δ s = V^{π*}(s) − V^π(s)`, the one-step
performance difference `Δ sm = advGapInf sm + γ·∑_{s'} step(sm,s')·Δ s'` has its
successor term a convex combination of values `≤ Δ sm`, so
`advGapInf sm ≥ (1−γ)·Δ sm`. And `Δ sm ≥ 0` since `V^{π*} = V*` dominates every
policy's value. Hence the supremum, which is `≥ advGapInf sm`, is nonneg. -/
theorem ciSup_advGapInf_nonneg (M : FiniteMDP S A) (π πstar : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (hstar : ∀ s, Vinf M πstar s = Vstar M s) :
    0 ≤ ⨆ s : S, advGapInf M π πstar s := by
  classical
  obtain ⟨s₀⟩ := ‹Nonempty S›
  -- `Δ` is nonnegative everywhere, `π*` being optimal.
  have hΔnn : ∀ s, 0 ≤ Vinf M πstar s - Vinf M π s := by
    intro s
    have h := vstar_upper_proof M hr hγ₀ hγ₁ π s
    rw [← hstar s] at h
    linarith
  -- the maximizing state
  set D : ℝ := Finset.univ.sup' ⟨s₀, mem_univ s₀⟩
    (fun s => Vinf M πstar s - Vinf M π s) with hD
  have hle : ∀ s, Vinf M πstar s - Vinf M π s ≤ D := fun s => by
    rw [hD]; exact Finset.le_sup' (f := fun s => Vinf M πstar s - Vinf M π s) (mem_univ s)
  obtain ⟨sm, -, hsm⟩ := Finset.exists_mem_eq_sup' (⟨s₀, mem_univ s₀⟩ :
    (Finset.univ : Finset S).Nonempty) (fun s => Vinf M πstar s - Vinf M π s)
  have hDs : D = Vinf M πstar sm - Vinf M π sm := by rw [hD]; exact hsm
  have hDnn : 0 ≤ D := by rw [hDs]; exact hΔnn sm
  -- the successor term is a convex combination of `Δ`, hence `≤ D`
  have htail : ∑ s', step M πstar sm s' * (Vinf M πstar s' - Vinf M π s') ≤ D := by
    calc ∑ s', step M πstar sm s' * (Vinf M πstar s' - Vinf M π s')
        ≤ ∑ s', step M πstar sm s' * D :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_mul_of_nonneg_left (hle s') (step_nonneg M πstar sm s')
      _ = D := by rw [← Finset.sum_mul, step_sum_eq_one M πstar sm, one_mul]
  have hstep := perfDiffInf_step M π πstar hr hγ₀ hγ₁ sm
  rw [← hDs] at hstep
  -- `D = advGapInf sm + γ·(tail) ≤ advGapInf sm + γ·D`
  have hkey : 0 ≤ advGapInf M π πstar sm := by
    nlinarith [mul_le_mul_of_nonneg_left htail hγ₀]
  exact le_trans hkey (advGapInf_le_ciSup M π πstar sm)

/-! ### Step 3 — change of measure and assembly -/

/-- **The sharp form.** The `1/(1−γ)` in the frozen statement is slack: the
identity plus the pointwise change of measure already gives

`V*_μ − V^π_μ ≤ mismatchCoeff · (⨆ s, ∑_a (π*(a|s) − π(a|s))·A^π(s,a))`.

Recorded separately because the frozen goal is the weaker `/(1−γ)` version and
must be proved at its exact type. -/
theorem g2b_sharp (M : FiniteMDP S A) (π πstar : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (hstar : ∀ s, Vinf M πstar s = Vstar M s) :
    VstarDist M μ - VinfDist M π μ
      ≤ mismatchCoeff M πstar μ
          * (⨆ s : S, ∑ a : A, ((πstar s) a - (π s) a) * advInf M π s a) := by
  classical
  set C : ℝ := ⨆ s : S, advGapInf M π πstar s with hC
  have hCnn : 0 ≤ C := ciSup_advGapInf_nonneg M π πstar hr hγ₀ hγ₁ hstar
  -- the frozen right side's supremum is `C`, term by term
  have hrewrite : (⨆ s : S, ∑ a : A, ((πstar s) a - (π s) a) * advInf M π s a) = C := by
    rw [hC]
    exact iSup_congr fun s => sum_sub_adv_eq_advGapInf M π πstar hr hγ₀ hγ₁ s
  rw [hrewrite]
  -- the exact performance-difference identity
  rw [VstarDist_sub_VinfDist_eq M π πstar hr hγ₀ hγ₁ hstar μ]
  calc ∑ s, dinfDist M πstar μ s * advGapInf M π πstar s
      ≤ ∑ s, dinfDist M πstar μ s * C := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (advGapInf_le_ciSup M π πstar s)
          (dinfDist_nonneg M hγ₀ πstar μ s)
    _ ≤ ∑ s, (mismatchCoeff M πstar μ * μ s) * C := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_right
          (mismatch_bound_proof_of_support M hγ₀ hγ₁ πstar μ hμ s) hCnn
    _ = mismatchCoeff M πstar μ * C := by
        have hcg : ∀ s ∈ (univ : Finset S),
            (mismatchCoeff M πstar μ * μ s) * C
              = (mismatchCoeff M πstar μ * C) * μ s := fun s _ => by ring
        rw [Finset.sum_congr rfl hcg, ← Finset.mul_sum, μ.sum_eq_one, mul_one]

set_option linter.unusedVariables false in
/-- **G2b — AKM Lemma 4.1, directional gradient domination.**

Discharges `Goal.g2_gradient_domination` at exactly the frozen type.

`g2b_sharp` gives `≤ mismatchCoeff · C`; since `C ≥ 0`, `mismatchCoeff ≥ 1 > 0`
and `1 ≤ 1/(1−γ)`, that is at most `(mismatchCoeff/(1−γ)) · C`. -/
theorem g2_gradient_domination_directional_proof (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    VstarDist M μ - VinfDist M (F.toPolicy θ) μ
      ≤ (mismatchCoeff M πstar μ / (1 - M.γ))
          * (⨆ s : S, ∑ a : A,
              ((πstar s) a - (F.toPolicy θ s) a) * advInf M (F.toPolicy θ) s a) := by
  classical
  have hpos : 0 < 1 - M.γ := by linarith
  set π : Policy S A := F.toPolicy θ with hπ
  set C : ℝ := ⨆ s : S, ∑ a : A, ((πstar s) a - (π s) a) * advInf M π s a with hC
  have hCnn : 0 ≤ C := by
    rw [hC, iSup_congr fun s => sum_sub_adv_eq_advGapInf M π πstar hr hγ₀ hγ₁ s]
    exact ciSup_advGapInf_nonneg M π πstar hr hγ₀ hγ₁ hstar
  have hmm : 1 ≤ mismatchCoeff M πstar μ :=
    one_le_mismatchCoeff M hγ₀ hγ₁ πstar μ hμ
  have hsharp : VstarDist M μ - VinfDist M π μ ≤ mismatchCoeff M πstar μ * C :=
    g2b_sharp M π πstar hr hγ₀ hγ₁ μ hμ hstar
  refine le_trans hsharp ?_
  -- `mismatchCoeff · C ≤ (mismatchCoeff / (1−γ)) · C`, since `1 ≤ 1/(1−γ)`.
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [mul_nonneg (le_trans zero_le_one hmm) hCnn]

end Proofs
end PolicyGradient
