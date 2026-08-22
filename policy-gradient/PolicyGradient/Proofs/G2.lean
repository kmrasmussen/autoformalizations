/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target
import PolicyGradient.Proofs

/-!
# Proofs/G2.lean — AKM Lemma 4.1, gradient domination

Discharges the frozen goal `Goal.g2_gradient_domination`:

```
VstarDist M μ - VinfDist M (F.toPolicy θ) μ
  ≤ (mismatchCoeff M πstar μ / (1 - M.γ)) * (⨆ s, ⨆ a, |advInf M (F.toPolicy θ) s a|)
```

## The argument

AKM prove this via the performance-difference lemma plus a change of measure:
`V* − V^π = (1/(1−γ))·E_{s∼d^{π*}_μ}[ Σ_a π*(a|s)·A^π(s,a) ]`, then bound the
inner sum by `max_{s,a}|A^π|` and convert `d^{π*}_μ` to `μ` through
`mismatchCoeff`.

The route taken here reaches the same inequality without first proving the PDL
*identity* (which needs the occupancy `tsum` telescoped against a linear solve).
The observation that makes it cheap: the change of measure only ever *helps*,
because `mismatchCoeff ≥ 1` always (`mu_le_dinfDist`: the occupancy from `μ`
dominates `μ` itself, since the `t = 0` term already contributes `μ s`). So it
suffices to prove the **pointwise** bound

`Vinf M πstar s − Vinf M π s ≤ B / (1 − γ)`,  `B := ⨆ s, ⨆ a, |advInf M π s a|`,

average it against `μ`, and then weaken by `1 ≤ mismatchCoeff`.

The pointwise bound is a max-state contraction in the style of `Vinf_diff_le`:
writing `Δ s = Vinf πstar s − Vinf π s`, the one-step decomposition
(`Vinf_diff_eq`) reads

`Δ s = Σ_a π*(a|s)·A^π(s,a) + γ·Σ_a π*(a|s) Σ_{s'} P(s'|s,a)·Δ s'`

— the first summand being exactly the advantage term, because
`Σ_a π(a|s)·Q^π(s,a) = V^π(s)` (`Vinf_eq_rbar_add`) turns
`Σ_a (π*(a|s) − π(a|s))·Q^π(s,a)` into `Σ_a π*(a|s)·A^π(s,a)`. Taking `D` to be
the max of `Δ` over states and evaluating at the argmax gives `D ≤ B + γ·D`,
hence `D ≤ B/(1−γ)`.

Nothing here is specific to softmax: `hF` is not needed, and the result holds
for any `πstar`. The hypotheses are kept because the frozen statement carries
them.
-/

open Finset

namespace PolicyGradient
namespace Proofs

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ### The advantage form of the one-step decomposition -/

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- `advInf` is `Qinf` minus `Vinf` — the definitional unfolding, stated so the
rest of the file can rewrite with it. -/
theorem advInf_eq_Qinf_sub (M : FiniteMDP S A) (π : Policy S A) (s : S) (a : A) :
    advInf M π s a = Qinf M π s a - Vinf M π s := by
  unfold advInf Qinf; ring

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- **The advantage rewriting of the policy-difference term.**

`Σ_a (π*(a|s) − π(a|s))·Q^π(s,a) = Σ_a π*(a|s)·A^π(s,a)`.

Both `π*` and `π` are probability vectors, so the `V^π(s)` subtracted inside the
advantage is added back by `Σ_a π*(a|s) = 1`, while `Σ_a π(a|s)·Q^π(s,a)` is
`V^π(s)` by `Vinf_eq_rbar_add`. -/
theorem sum_adv_eq (M : FiniteMDP S A) (π πstar : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s : S) :
    ∑ a, ((πstar s) a - (π s) a) * Qinf M π s a
      = ∑ a, (πstar s) a * advInf M π s a := by
  have hV : ∑ a, (π s) a * Qinf M π s a = Vinf M π s :=
    (Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s).symm
  have hone : ∑ a, (πstar s) a = 1 := (πstar s).sum_eq_one
  calc ∑ a, ((πstar s) a - (π s) a) * Qinf M π s a
      = (∑ a, (πstar s) a * Qinf M π s a) - ∑ a, (π s) a * Qinf M π s a := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = (∑ a, (πstar s) a * Qinf M π s a) - Vinf M π s := by rw [hV]
    _ = (∑ a, (πstar s) a * Qinf M π s a)
          - (∑ a, (πstar s) a) * Vinf M π s := by rw [hone, one_mul]
    _ = ∑ a, (πstar s) a * (Qinf M π s a - Vinf M π s) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a, (πstar s) a * advInf M π s a := by
        exact Finset.sum_congr rfl fun a _ => by rw [advInf_eq_Qinf_sub]

/-! ### The uniform advantage bound -/

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- The doubly-indexed `⨆ s, ⨆ a, |advInf|` is bounded above, so the `ciSup`s
are genuine suprema rather than the junk value `0`. -/
theorem bddAbove_adv (M : FiniteMDP S A) (π : Policy S A) :
    BddAbove (Set.range fun s : S => ⨆ a : A, |advInf M π s a|) :=
  Finite.bddAbove_range _

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- Every `|A^π(s,a)|` is at most the double supremum. -/
theorem abs_adv_le_ciSup (M : FiniteMDP S A) (π : Policy S A) (s : S) (a : A) :
    |advInf M π s a| ≤ ⨆ s' : S, ⨆ a' : A, |advInf M π s' a'| := by
  refine le_trans (le_ciSup (f := fun a' : A => |advInf M π s a'|)
    (Finite.bddAbove_range _) a) ?_
  exact le_ciSup (bddAbove_adv M π) s

omit [DecidableEq A] in
/-- The double supremum of `|advInf|` is nonnegative. -/
theorem ciSup_adv_nonneg (M : FiniteMDP S A) (π : Policy S A) :
    0 ≤ ⨆ s : S, ⨆ a : A, |advInf M π s a| := by
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨a⟩ := ‹Nonempty A›
  exact le_trans (abs_nonneg _) (abs_adv_le_ciSup M π s a)

omit [DecidableEq A] [Nonempty S] [Nonempty A] in
/-- The `π*`-average of the advantage at a state is bounded by the double
supremum: a convex combination of numbers each `≤ B` in absolute value. -/
theorem sum_adv_le (M : FiniteMDP S A) (π πstar : Policy S A) (s : S) :
    ∑ a, (πstar s) a * advInf M π s a
      ≤ ⨆ s' : S, ⨆ a' : A, |advInf M π s' a'| := by
  set B : ℝ := ⨆ s' : S, ⨆ a' : A, |advInf M π s' a'| with hB
  calc ∑ a, (πstar s) a * advInf M π s a
      ≤ ∑ a, (πstar s) a * B := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ ((πstar s).nonneg a)
        exact le_trans (le_abs_self _) (abs_adv_le_ciSup M π s a)
    _ = B := by rw [← Finset.sum_mul, (πstar s).sum_eq_one, one_mul]

/-! ### The pointwise suboptimality bound

The max-state contraction. This is the infinite-horizon analogue of the
performance-difference lemma in inequality form: it is exactly what PDL gives
after bounding the inner sum, without needing the occupancy measure. -/

/-- **Pointwise gradient domination.**

`V^{π*}(s₀) − V^π(s₀) ≤ (max_{s,a}|A^π(s,a)|) / (1 − γ)` for *any* two policies.

Proof: let `D` be the largest value of `Δ s = V^{π*}(s) − V^π(s)` over states,
attained at `sm`. The one-step decomposition at `sm` (`Vinf_diff_eq`, rewritten
into advantage form by `sum_adv_eq`) bounds `D` by `B + γ·D`, since the
advantage term is `≤ B` (`sum_adv_le`) and the successor term is a convex
combination of values `≤ D`. Then `D(1 − γ) ≤ B` with `1 − γ > 0`. -/
theorem Vinf_sub_le_adv_div (M : FiniteMDP S A) (π πstar : Policy S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Vinf M πstar s₀ - Vinf M π s₀
      ≤ (⨆ s : S, ⨆ a : A, |advInf M π s a|) / (1 - M.γ) := by
  classical
  have hpos : 0 < 1 - M.γ := by linarith
  set B : ℝ := ⨆ s : S, ⨆ a : A, |advInf M π s a| with hBdef
  have hBnn : 0 ≤ B := ciSup_adv_nonneg M π
  -- `D` is the largest suboptimality over states.
  set D : ℝ := Finset.univ.sup' ⟨s₀, mem_univ s₀⟩
    (fun s => Vinf M πstar s - Vinf M π s) with hD
  have hle : ∀ s, Vinf M πstar s - Vinf M π s ≤ D := by
    intro s
    rw [hD]
    exact Finset.le_sup' (f := fun s => Vinf M πstar s - Vinf M π s) (mem_univ s)
  -- The contraction step: `D ≤ B + γ·D`, read off at the maximizing state.
  have hstep : D ≤ B + M.γ * D := by
    obtain ⟨sm, -, hsm⟩ := Finset.exists_mem_eq_sup' (⟨s₀, mem_univ s₀⟩ :
      (Finset.univ : Finset S).Nonempty) (fun s => Vinf M πstar s - Vinf M π s)
    have hDs : D = Vinf M πstar sm - Vinf M π sm := by rw [hD]; exact hsm
    -- rewrite only the LHS `D`: `rw [hDs]` would also unfold the `D` in `B + γ·D`
    nth_rewrite 1 [hDs]
    rw [Vinf_diff_eq M πstar π hr hγ₀ hγ₁ sm, sum_adv_eq M π πstar hr hγ₀ hγ₁ sm]
    -- the successor term is `γ` times a convex combination of `Δ`, hence `≤ γ·D`
    have htail : M.γ * ∑ a, (πstar sm) a
          * ∑ s', (M.P sm a) s' * (Vinf M πstar s' - Vinf M π s')
        ≤ M.γ * D := by
      refine mul_le_mul_of_nonneg_left ?_ hγ₀
      calc ∑ a, (πstar sm) a
              * ∑ s', (M.P sm a) s' * (Vinf M πstar s' - Vinf M π s')
          ≤ ∑ a, (πstar sm) a * D := by
            refine Finset.sum_le_sum fun a _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ ((πstar sm).nonneg a)
            calc ∑ s', (M.P sm a) s' * (Vinf M πstar s' - Vinf M π s')
                ≤ ∑ s', (M.P sm a) s' * D :=
                  Finset.sum_le_sum fun s' _ =>
                    mul_le_mul_of_nonneg_left (hle s') ((M.P sm a).nonneg s')
              _ = D := by rw [← Finset.sum_mul, (M.P sm a).sum_eq_one, one_mul]
        _ = D := by rw [← Finset.sum_mul, (πstar sm).sum_eq_one, one_mul]
    have hadv : ∑ a, (πstar sm) a * advInf M π sm a ≤ B := sum_adv_le M π πstar sm
    exact add_le_add hadv htail
  have hDle : D ≤ B / (1 - M.γ) := by
    rw [le_div_iff₀ hpos]; nlinarith
  exact le_trans (hle s₀) hDle

/-! ### Averaging against `μ` and the change of measure -/

/-- `1 ≤ mismatchCoeff M π μ` whenever `μ` has full support.

This is what makes the change of measure a *weakening*: the occupancy `d^π_μ`
dominates `μ` pointwise (`mu_le_dinfDist`), so every ratio in the supremum is at
least `1`. -/
theorem one_le_mismatchCoeff (M : FiniteMDP S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (π : Policy S A) (μ : Dist S)
    (hμ : ∀ s, 0 < μ s) :
    1 ≤ mismatchCoeff M π μ := by
  obtain ⟨s⟩ := ‹Nonempty S›
  have h1 : (1:ℝ) ≤ dinfDist M π μ s / μ s := by
    rw [le_div_iff₀ (hμ s), one_mul]
    exact mu_le_dinfDist M hγ₀ hγ₁ π μ s
  exact le_trans h1 (le_ciSup (bddAbove_mismatch M π μ) s)

set_option linter.unusedVariables false in
/-- **G2 — AKM Lemma 4.1, gradient domination.**

Discharges `Goal.g2_gradient_domination` with exactly the frozen type.

`VstarDist − VinfDist` is the `μ`-average of the pointwise suboptimality, which
`Vinf_sub_le_adv_div` bounds by `B/(1−γ)` at every state (using `hstar` to turn
`Vstar` into `Vinf πstar`). Averaging a constant against a probability vector
returns the constant, giving `B/(1−γ)`. The change of measure to
`mismatchCoeff/(1−γ)` is then a weakening, since `mismatchCoeff ≥ 1` and `B ≥ 0`. -/
theorem g2_gradient_domination_proof (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    VstarDist M μ - VinfDist M (F.toPolicy θ) μ
      ≤ (mismatchCoeff M πstar μ / (1 - M.γ))
          * (⨆ s : S, ⨆ a : A, |advInf M (F.toPolicy θ) s a|) := by
  classical
  have hpos : 0 < 1 - M.γ := by linarith
  set π : Policy S A := F.toPolicy θ with hπ
  set B : ℝ := ⨆ s : S, ⨆ a : A, |advInf M π s a| with hBdef
  have hBnn : 0 ≤ B := ciSup_adv_nonneg M π
  -- Step 1: the `μ`-average of the pointwise bound.
  have hpt : VstarDist M μ - VinfDist M π μ ≤ B / (1 - M.γ) := by
    have hdiff : VstarDist M μ - VinfDist M π μ
        = ∑ s, μ s * (Vinf M πstar s - Vinf M π s) := by
      unfold VstarDist VinfDist
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by rw [hstar s]; ring
    rw [hdiff]
    calc ∑ s, μ s * (Vinf M πstar s - Vinf M π s)
        ≤ ∑ s, μ s * (B / (1 - M.γ)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          exact mul_le_mul_of_nonneg_left
            (Vinf_sub_le_adv_div M π πstar hr hγ₀ hγ₁ s) (μ.nonneg s)
      _ = B / (1 - M.γ) := by rw [← Finset.sum_mul, μ.sum_eq_one, one_mul]
  -- Step 2: the change of measure is a weakening, since `mismatchCoeff ≥ 1`.
  have hmm : 1 ≤ mismatchCoeff M πstar μ :=
    one_le_mismatchCoeff M hγ₀ hγ₁ πstar μ hμ
  have hweak : B / (1 - M.γ) ≤ (mismatchCoeff M πstar μ / (1 - M.γ)) * B := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
    nlinarith
  exact le_trans hpt hweak

end Proofs
end PolicyGradient
