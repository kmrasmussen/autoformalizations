/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1c

/-!
# G1Sel — the aggregate Łojasiewicz bound at the maximizing selector

Work file for the frozen goal `g1_aggregate_bound` (`@[infra "G1-aggregate"]`)
in its restated form, which carries a selector `b : S → A` with

```
hb : ∀ s a, π(a|s)·A^π(s,a) ≤ π(b s|s)·A^π(s,b s)
```

i.e. `b s = argmax_a π(a|s)·A^π(s,a)`.

Note the two candidate `hb` selectors coincide: `hb` says `b s` maximizes
`a ↦ π(a|s)·A^π(s,a)`, and `sum_pi_advInf_eq_zero` then forces `m(s) ≥ 0`.

## Status: the change-of-measure half is proved; (★) is open

What is established here, unconditionally:

* `sel_nonneg` — `m(s) = π(b s|s)·A^π(s,b s) ≥ 0`. This is the first real
  dividend of the restatement: at the old `astar` the corresponding quantity
  could be negative, which is exactly why `sum_abs_adv_le_norm` had to carry an
  absolute value. At `b` the absolute value is vacuous (`sel_rhs_eq`).
* `sum_dinfDistStar_sel_le` — the change of measure at `b`:
  `∑_s d^{πstar}_μ(s)·m(s) ≤ mism·∑_s d^π_μ(s)·m(s)`.
* `g1_aggregate_bound_reduce` — the frozen goal is *equivalent* to (★).

## Why no termwise proof of (★) can exist

(★) is genuinely global, and this is now pinned down sharply rather than
observed loosely. Write `X⁺(s) = max(X(s), 0)`. Numerically, over 10⁵–10⁶
tie-seeded MDPs (integer/half-integer reward grids, `πstar` a random
distribution over the `Q*`-argmax set, `astar` chosen adversarially to
*maximize* `c`, which is the worst case since the LHS increases in `c`):

| candidate | status | max violation |
|---|---|---|
| (★) itself | holds | `6.2e-15` |
| `X → X⁺` in (★) | holds | `7.5e-16` |
| `c·X⁺(s) ≤ m(s)·mism·d^π_μ(s)/d^{πstar}_μ(s)` (★ termwise) | **FALSE** | `0.155` |
| `c·X⁺(s) ≤ m(s)·d^π_μ(s)/μ(s)` | **FALSE** | `0.203` |
| `c·∑_s d^{πstar}_μ(s)·X⁺(s) ≤ ∑_s d^{πstar}_μ(s)·m(s)` | **FALSE** | `4.34` |
| `c·(V*_μ − V^π_μ) ≤ ∑_s d^{πstar}_μ(s)·m(s)` | **FALSE** | `0.514` |
| `c·mism·∑_s μ(s)·X⁺(s) ≤ mism·∑_s d^π_μ(s)·m(s)` | **FALSE** | `1.09` |
| `c·∑_s d^{πstar}_μ(s)·X⁺(s) ≤ ∑_s d^π_μ(s)·m(s)/(1−γ)` | **FALSE** | `0.154` |

The third row is the decisive one: it is (★) itself read state by state — the
*sharpest possible* termwise sufficient condition — and it is false. So **no
argument that bounds the `s`-th summand of the LHS by the `s`-th summand of the
RHS can work**, no matter how the constants are arranged.

The fifth and sixth rows kill the only route the repo's lemma stock actually
offers for introducing `mism`. The single lemma relating `mism` to anything is
`mismatch_bound_proof_of_support`, `d^{πstar}_μ(s) ≤ mism·μ(s)`, applied
pointwise. Using it at all replaces `d^{πstar}_μ` by `mism·μ` inside the sum,
and the resulting inequality is false (row five, violation `1.09`). Even the
much weaker `1/(1−γ)` relaxation fails (row seven), and `mism ≥ 1` always, so
there is no slack to spend there either.

So `mism` must be used as a **supremum coupled to the whole sum** — the state
`s₀` attaining `mism = d^{πstar}_μ(s₀)/μ(s₀)` has to be played off against the
states carrying the mass of `∑_s d^{πstar}_μ(s)·X⁺(s)` — and the repo has no
lemma of that shape. That is the precise remaining research gap.

The tight cases (ratio `0.9947`, approached but never crossed) all have the same
anatomy: a single state `s₁` carries essentially all of `d^{πstar}_μ`, `πstar`
is effectively deterministic there, `c = π(astar s₁|s₁)`, and
`c·X⁺(s₁) = m(s₁)` exactly. Tightness is therefore realised in the regime where
`πstar` is deterministic — and in that regime the termwise bound *does* hold
(zero violations in 1.5·10⁵ samples with `πstar` deterministic at `s`; all
`3588` observed termwise violations had `πstar` stochastic at `s`, i.e. a
genuine `Q*` tie). The gap between those two facts is where a proof would have
to live.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Sel

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

open scoped BigOperators

/-- `∑_a π(a|s)·A^π(s,a) = 0`: the advantage has zero mean under `π`. -/
theorem sum_pi_advInf_eq_zero (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s : S) :
    ∑ a, (π s) a * advInf M π s a = 0 := by
  have hV : Vinf M π s = ∑ a, (π s) a * Qinf M π s a :=
    Vinf_eq_rbar_add M π 1 zero_le_one hr hγ₀ hγ₁ s
  have h : ∀ a, (π s) a * advInf M π s a
      = (π s) a * Qinf M π s a - (π s) a * Vinf M π s := by
    intro a; rw [advInf_eq]; ring
  rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_sub_distrib,
    ← Finset.sum_mul, (π s).sum_eq_one, one_mul, ← hV]
  ring

/-- The maximizing selector value `m(s) = π(b s|s)·A^π(s,b s)` is nonnegative,
because the `π`-weighted advantages sum to zero and `m(s)` dominates each of
them. -/
theorem sel_nonneg (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s))
    (s : S) : 0 ≤ (π s) (b s) * advInf M π s (b s) := by
  by_contra hneg
  rw [not_le] at hneg
  have hsum : ∑ a, (π s) a * advInf M π s a < 0 := by
    have hlt : ∀ a ∈ (univ : Finset A), (π s) a * advInf M π s a
        ≤ (π s) (b s) * advInf M π s (b s) := fun a _ => hb s a
    calc ∑ a, (π s) a * advInf M π s a
        ≤ ∑ _a : A, (π s) (b s) * advInf M π s (b s) := Finset.sum_le_sum hlt
      _ = (Fintype.card A : ℝ) * ((π s) (b s) * advInf M π s (b s)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < 0 := by
          have hc : (0:ℝ) < (Fintype.card A : ℝ) := by
            have := Fintype.card_pos_iff.mpr ‹Nonempty A›
            exact_mod_cast this
          exact mul_neg_of_pos_of_neg hc hneg
  rw [sum_pi_advInf_eq_zero M hr hγ₀ hγ₁ π s] at hsum
  exact lt_irrefl 0 hsum

/-- The RHS of the frozen goal, with the absolute value removed:
`m(s) ≥ 0` and `d^π_μ(s) ≥ 0`, so each summand is already nonnegative. -/
theorem sel_rhs_eq (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (μ : Dist S) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s)) :
    ∑ s, |dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))|
      = ∑ s, dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s)) := by
  refine Finset.sum_congr rfl fun s _ => ?_
  have hd : 0 ≤ dinfDist M π μ s := by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ => mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ π s₀ s)
  exact abs_of_nonneg (mul_nonneg hd (sel_nonneg M hr hγ₀ hγ₁ π b hb s))

/-- **Change of measure at the selector `b`.**

`d^{πstar}_μ(s) ≤ mism·μ(s) ≤ mism·d^π_μ(s)` and `m(s) ≥ 0`, so the
`πstar`-occupancy-weighted selector sum is dominated by `mism` times the
`π`-occupancy-weighted one. -/
theorem sum_dinfDistStar_sel_le (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (μ : Dist S) (hμ : ∀ s, 0 < μ s) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s)) :
    ∑ s, dinfDist M πstar μ s * ((π s) (b s) * advInf M π s (b s))
      ≤ mismatchCoeff M πstar μ
          * ∑ s, dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  have hm : 0 ≤ (π s) (b s) * advInf M π s (b s) := sel_nonneg M hr hγ₀ hγ₁ π b hb s
  have h1 : dinfDist M πstar μ s ≤ mismatchCoeff M πstar μ * μ s :=
    mismatch_bound_proof_of_support M hγ₀ hγ₁ πstar μ hμ s
  have h2 : μ s ≤ dinfDist M π μ s := mu_le_dinfDist M hγ₀ hγ₁ π μ s
  have hm0 : 0 < mismatchCoeff M πstar μ := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have h3 : dinfDist M πstar μ s ≤ mismatchCoeff M πstar μ * dinfDist M π μ s :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 hm0.le)
  calc dinfDist M πstar μ s * ((π s) (b s) * advInf M π s (b s))
      ≤ (mismatchCoeff M πstar μ * dinfDist M π μ s)
          * ((π s) (b s) * advInf M π s (b s)) := mul_le_mul_of_nonneg_right h3 hm
    _ = mismatchCoeff M πstar μ * (dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))) := by
        ring

/-! ### The exact reduction of the frozen goal

`sel_rhs_eq` removes the absolute value, and `VstarDist_sub_VinfDist_eq`
expands the suboptimality, so the frozen goal is *equivalent* to

```
c · ∑_s d^{πstar}_μ(s) · X(s)  ≤  mism · ∑_s d^π_μ(s) · m(s)          (★)
```

with `c = ⨅_s π(astar s|s)`, `X(s) = ∑_a πstar(a|s)·A^π(s,a)` and
`m(s) = π(b s|s)·A^π(s,b s) ≥ 0` (`sel_nonneg`).

`g1_aggregate_bound_reduce` below is that equivalence, proved unconditionally. -/

/-- **The frozen goal is equivalent to (★).**

Both rewrites are exact: the RHS absolute value is vacuous because every summand
is already nonnegative (`sel_rhs_eq`), and the LHS suboptimality is the
occupancy-weighted advantage (`VstarDist_sub_VinfDist_eq`). -/
theorem g1_aggregate_bound_reduce (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (μ : Dist S) (astar : S → A) (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s)) :
    ((⨅ s : S, (π s) (astar s)) * (VstarDist M μ - VinfDist M π μ)
        ≤ mismatchCoeff M πstar μ
            * ∑ s, |dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))|)
      ↔ ((⨅ s : S, (π s) (astar s))
              * ∑ s, dinfDist M πstar μ s * advGapInf M π πstar s
            ≤ mismatchCoeff M πstar μ
                * ∑ s, dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))) := by
  rw [sel_rhs_eq M hr hγ₀ hγ₁ π μ b hb,
    VstarDist_sub_VinfDist_eq M π πstar hr hγ₀ hγ₁ hstar μ]

#print axioms sel_nonneg
#print axioms sel_rhs_eq
#print axioms sum_dinfDistStar_sel_le
#print axioms g1_aggregate_bound_reduce

end Sel

end Proofs
end PolicyGradient
