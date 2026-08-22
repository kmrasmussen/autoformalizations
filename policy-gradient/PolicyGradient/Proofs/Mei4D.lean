/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Mei4C
import PolicyGradient.Proofs.G1Wire
import PolicyGradient.Proofs.G9c

/-!
# Mei4D — `Goal.mei_theorem4` (Mei et al., Theorem 4): interface + constants

Both analytic inputs are now proved:

* `PolicyGradient.g1_lojasiewicz` (Mei Lemma 8) — `Proofs.g1_lojasiewicz_proof`;
* `Proofs.mei4_rho_rate_of_g3` — the rate composition.

Two things stand between them and the frozen goal.  Both are settled here.

## 1. The interface gap, and how it is closed

`mei4_rho_rate_of_g3` takes `hloja` at a **fixed** `astar`, the same `astar`
that `hcbound` bounds below by `c`.  `g1_lojasiewicz` supplies `astar`
**existentially**:

```
∃ astar, (∀ s, 0 < (πstar s) (astar s)) ∧ <Łojasiewicz at that astar>
```

and its witness is `exists_argmax_selector`'s — an `A^{π_θ}`-argmax over
`supp πstar(·|s)`, which **depends on `θ`** and therefore may differ at every
iterate `θ t`, and need not be the `astar` `mei_theorem4` was handed.  So the
existential cannot be fed to the composition as it stands: `hcbound` says
nothing about the probability the trajectory assigns to Lemma 8's own witness,
and there is no lemma anywhere in the repo that lower-bounds `π_t(a|s)` for a
general `a ∈ supp πstar(·|s)`.

**Option 1 of the brief — re-invoking the chain at `mei_theorem4`'s own
`astar` — is the right route, and it works**, at the cost of one hypothesis
that the frozen statement does not carry.  Tracing `g1_lojasiewicz_of_selector`
back through `g1_aggregate_bound_at_argmax` and `iInf_mul_advGapInf_le_sel`,
the *only* use of `hmax` is via `advGapInf_le_advInf_argmax`, which converts it
into the single per-state fact

```
advGapInf M π πstar s ≤ advInf M π s (astar s)                       (†)
```

— "the given `astar s` is at least as good, under the *current* policy's
advantage, as the `πstar`-average".  `(†)` is strictly weaker than `hmax` and is
the honest minimal interface condition; it is named `hdom` below.

`(†)` is **not** derivable from `mei_theorem4`'s hypotheses.  `hastar` only puts
`astar s` in `supp πstar(·|s)`; `advInf` is the *current* policy's advantage, so
which action of that support maximises it moves with `θ t`.  A `Q*` tie shared
by `πstar` between two actions, with the trajectory currently preferring the one
`astar` did not pick, violates `(†)` — the same tie structure that refuted the
earlier `g9_c_positive` statement (`Proofs.g9_c_positive_frozen_is_false`).

`(†)` is discharged automatically in the case the paper actually intends:
`astar_compat_of_det` shows that if `πstar` is deterministic on `astar`
(`πstar s (astar s) = 1` — which Mei's own strict-gap `Δ*(s) > 0` forces, via
`Proofs.gap_pistar_det`), then `advGapInf = advInf (astar s)` with **equality**,
so `hdom` holds with no assumption on the trajectory at all.
`mei_theorem4_of_astar_gap` is that corollary, stated against Mei's
optimal-value-gap hypothesis directly.

## 2. The constant reconciliation

`mei4_rho_rate_of_g3` concludes

```
V*(ρ) − V^{π_T}(ρ)  ≤  ‖1/μ‖_∞ · ( 16|S| / (c²(1−γ)³ T) · m² )
```

and the frozen goal asks for

```
V*(ρ) − V^{π_T}(ρ)  ≤  16|S| / (c²(1−γ)⁶ T) · m² · ‖1/μ‖_∞ .
```

These are the *same product* of the *same four* factors — `16|S|`, `c⁻²T⁻¹`,
`m²`, `‖1/μ‖_∞` — differing only in the power of `(1−γ)` in the denominator.
`hγ₀ : 0 ≤ γ` and `hγ₁ : γ < 1` give `0 < 1−γ ≤ 1`, hence
`(1−γ)⁶ ≤ (1−γ)³` and so `1/(1−γ)⁶ ≥ 1/(1−γ)³`.  The frozen right-hand side is
therefore the **larger** of the two: the frozen bound is *implied by* the proved
one, and **no term blocks it**.  `rate_const_le` is that arithmetic, and the
factor-ordering difference (`‖1/μ‖_∞` on the left vs. on the right) is a pure
`ring` step since multiplication is commutative.

Note this is the exact opposite of `Mei4C`'s `hconst` situation.  `hconst` was
false because the frozen statement at that time carried `m` to the **first**
power and **no** `‖1/μ‖_∞`; the frozen statement has since been corrected to
`mismatchCoeff ^ 2 * Proofs.invMuSup μ`, and with those two factors restored the
only remaining discrepancy is the harmless `(1−γ)³ → (1−γ)⁶`.  `Mei4C`'s
`hconst_is_false` therefore no longer bears on the current frozen statement.

## 3. Status

`mei_theorem4_of_astar_compat` hits the frozen right-hand side **verbatim** and
is proved from `mei_theorem4`'s own hypotheses plus:

* `hdom` — the interface condition `(†)` above, and
* `s₀`/`hnondeg` — non-degeneracy, which `mei4_rho_rate_of_g3` already requires
  (some state admits some strictly suboptimal policy; without it every policy is
  optimal, `V* − V^π ≡ 0`, and `g3_strict_suboptimality` has nothing to say).

Neither is in the frozen signature, so the frozen `mei_theorem4` is **not**
closed here.  `mei_theorem4_of_astar_compat` is the precise reduction, and
`mei_theorem4_of_astar_gap` is the same thing under Mei's own strict-gap
assumption instead of `hdom`.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Mei4D

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

open scoped BigOperators

/-! ## The interface condition `(†)` -/

/-- **`(†)` holds outright when `πstar` is deterministic on `astar`.**

If `πstar` puts all its mass on `astar s`, the `πstar`-averaged advantage *is*
the advantage at `astar s`, so `(†)` holds with equality — no assumption on the
current policy `π` at all. -/
theorem astar_compat_of_det (M : FiniteMDP S A) (π πstar : Policy S A)
    (astar : S → A) (hdet : ∀ s, (πstar s) (astar s) = 1) (s : S) :
    advGapInf M π πstar s ≤ advInf M π s (astar s) := by
  classical
  have hsum := (πstar s).sum_eq_one
  rw [← Finset.add_sum_erase Finset.univ (fun b => (πstar s) b)
    (Finset.mem_univ (astar s)), hdet s] at hsum
  have hrest : ∑ b ∈ Finset.univ.erase (astar s), (πstar s) b = 0 := by linarith
  have hzero : ∀ a, a ≠ astar s → (πstar s) a = 0 := by
    intro a ha
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => (πstar s).nonneg b)).mp hrest a
      (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)
  have heq : advGapInf M π πstar s = advInf M π s (astar s) := by
    unfold advGapInf
    rw [Finset.sum_eq_single (astar s)]
    · rw [hdet s, one_mul]
    · intro b _ hb; rw [hzero b hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ (astar s)) h
  exact heq.le

/-- **`(†)` from Mei's optimal-value-gap assumption.**

Mei's proof of Lemma 9 opens by assuming a strictly positive optimal value gap
`Δ*(s) = Q*(s, a*(s)) − max_{a ≠ a*(s)} Q*(s,a) > 0`.  `gap_pistar_det` turns
that into determinism of `πstar` on `astar`, which `astar_compat_of_det` turns
into `(†)` — for every policy `π`, hence at every iterate. -/
theorem astar_compat_of_gap (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s))
    (π : Policy S A) (s : S) :
    advGapInf M π πstar s ≤ advInf M π s (astar s) := by
  classical
  refine astar_compat_of_det M π πstar astar (fun s' => ?_) s
  have hsum := (πstar s').sum_eq_one
  rw [← Finset.add_sum_erase Finset.univ (fun b => (πstar s') b)
    (Finset.mem_univ (astar s'))] at hsum
  have hrest : ∑ b ∈ Finset.univ.erase (astar s'), (πstar s') b = 0 :=
    Finset.sum_eq_zero fun b hb =>
      gap_pistar_det M hr hγ₀ hγ₁ πstar hstar astar hastar hgap s' b
        (Finset.mem_erase.mp hb).1
  linarith

/-! ## Re-deriving Mei Lemma 8 at a GIVEN `astar`

`iInf_mul_advGapInf_le_sel` uses `hmax` only through
`advGapInf_le_advInf_argmax`.  Replacing that one step by `hdom` gives the same
per-state collapse at an arbitrary `astar`. -/

/-- `iInf_mul_advGapInf_le_sel` with `hmax` weakened to `(†)`. -/
theorem iInf_mul_advGapInf_le_sel_of_dom (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π πstar : Policy S A) (astar : S → A)
    (hdom : ∀ s, advGapInf M π πstar s ≤ advInf M π s (astar s))
    (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s))
    (s : S) :
    (⨅ x : S, (π x) (astar x)) * advGapInf M π πstar s
      ≤ (π s) (b s) * advInf M π s (b s) := by
  classical
  set c : ℝ := ⨅ x : S, (π x) (astar x) with hc
  have hbdd : BddBelow (Set.range fun x : S => (π x) (astar x)) :=
    ⟨0, by rintro y ⟨x, rfl⟩; exact (π x).nonneg _⟩
  have hcle : c ≤ (π s) (astar s) := ciInf_le hbdd s
  have hc0 : 0 ≤ c := le_ciInf fun x => (π x).nonneg _
  have hS1 : advGapInf M π πstar s ≤ advInf M π s (astar s) := hdom s
  rcases le_or_gt (advInf M π s (astar s)) 0 with hA | hA
  · have h1 : c * advGapInf M π πstar s ≤ c * advInf M π s (astar s) :=
      mul_le_mul_of_nonneg_left hS1 hc0
    have h2 : c * advInf M π s (astar s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0 hA
    have hm0 : 0 ≤ (π s) (b s) * advInf M π s (b s) := sel_nonneg M hr hγ₀ hγ₁ π b hb s
    linarith
  · calc c * advGapInf M π πstar s
        ≤ c * advInf M π s (astar s) := mul_le_mul_of_nonneg_left hS1 hc0
      _ ≤ (π s) (astar s) * advInf M π s (astar s) :=
          mul_le_mul_of_nonneg_right hcle hA.le
      _ ≤ (π s) (b s) * advInf M π s (b s) := hb s (astar s)

/-- `g1_aggregate_bound_at_argmax` with `hmax` weakened to `(†)`. -/
theorem g1_aggregate_bound_of_dom (M : FiniteMDP S A)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (π πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A)
    (hdom : ∀ s, advGapInf M π πstar s ≤ advInf M π s (astar s))
    (b : S → A)
    (hb : ∀ s a, (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s)) :
    (⨅ s : S, (π s) (astar s)) * (VstarDist M μ - VinfDist M π μ)
      ≤ mismatchCoeff M πstar μ
          * ∑ s, |dinfDist M π μ s * ((π s) (b s) * advInf M π s (b s))| := by
  classical
  set c : ℝ := ⨅ x : S, (π x) (astar x) with hc
  set mism : ℝ := mismatchCoeff M πstar μ with hmism
  set m : S → ℝ := fun s => (π s) (b s) * advInf M π s (b s) with hm
  have hm0 : ∀ s, 0 ≤ m s := fun s => sel_nonneg M hr hγ₀ hγ₁ π b hb s
  have hmism0 : 0 < mism := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hdstar0 : ∀ s, 0 ≤ dinfDist M πstar μ s := fun s => by
    unfold dinfDist
    exact Finset.sum_nonneg fun s₀ _ =>
      mul_nonneg (μ.nonneg s₀) (dinf_nonneg M hγ₀ πstar s₀ s)
  rw [sel_rhs_eq M hr hγ₀ hγ₁ π μ b hb,
    VstarDist_sub_VinfDist_eq M π πstar hr hγ₀ hγ₁ hstar μ]
  have step1 : c * ∑ s, dinfDist M πstar μ s * advGapInf M π πstar s
      ≤ ∑ s, dinfDist M πstar μ s * m s := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h := iInf_mul_advGapInf_le_sel_of_dom M hr hγ₀ hγ₁ π πstar astar hdom b hb s
    calc c * (dinfDist M πstar μ s * advGapInf M π πstar s)
        = dinfDist M πstar μ s * (c * advGapInf M π πstar s) := by ring
      _ ≤ dinfDist M πstar μ s * m s := mul_le_mul_of_nonneg_left h (hdstar0 s)
  have step2 : ∑ s, dinfDist M πstar μ s * m s
      ≤ mism * ∑ s, dinfDist M π μ s * m s := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have h1 : dinfDist M πstar μ s ≤ mism * μ s :=
      mismatch_bound_proof_of_support M hγ₀ hγ₁ πstar μ hμ s
    have h2 : μ s ≤ dinfDist M π μ s := mu_le_dinfDist M hγ₀ hγ₁ π μ s
    have h3 : dinfDist M πstar μ s ≤ mism * dinfDist M π μ s :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 hmism0.le)
    calc dinfDist M πstar μ s * m s
        ≤ (mism * dinfDist M π μ s) * m s := mul_le_mul_of_nonneg_right h3 (hm0 s)
      _ = mism * (dinfDist M π μ s * m s) := by ring
  exact le_trans step1 step2

/-- **Mei Lemma 8 at a GIVEN `astar`**, under the interface condition `(†)`.

This is `g1_lojasiewicz`'s conclusion with `astar` *supplied* rather than
produced existentially — exactly the shape `mei4_rho_rate_of_g3` consumes. -/
theorem g1_lojasiewicz_at_astar (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (θ : EuclideanSpace ℝ (S × A))
    (hdom : ∀ s, advGapInf M (F.toPolicy θ) πstar s
      ≤ advInf M (F.toPolicy θ) s (astar s)) :
    (⨅ s : S, (F.toPolicy θ s) (astar s))
        / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
        * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
      ≤ ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖ := by
  classical
  obtain ⟨b, hb⟩ := exists_prod_argmax_selector M (F.toPolicy θ)
  exact g1_lojasiewicz_of_selector M F hF hr hγ₀ hγ₁ μ hμ πstar hstar astar hastar θ b
    (g1_aggregate_bound_of_dom M hr hγ₀ hγ₁ μ hμ (F.toPolicy θ) πstar hstar astar
      hdom b hb)

/-! ## The constant reconciliation -/

/-- **`(1−γ)³ → (1−γ)⁶` is free, and the factor reordering is a `ring` step.**

The composition's right-hand side and the frozen one are the same product of
`16|S|`, `c⁻²T⁻¹`, `m²` and `‖1/μ‖_∞`, differing only in the power of `(1−γ)`
in the denominator.  Since `0 < 1−γ ≤ 1`, the frozen `(1−γ)⁶` makes the bound
*larger*, hence weaker, hence implied. -/
theorem rate_const_le (M : FiniteMDP S A) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s) (πstar : Policy S A)
    (c : ℝ) (hc : 0 < c) (T : ℕ) (hT : 1 ≤ T) :
    invMuSup μ * (16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 3 * T)
        * mismatchCoeff M πstar μ ^ 2)
      ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)
          * mismatchCoeff M πstar μ ^ 2 * invMuSup μ := by
  have hpos : 0 < 1 - M.γ := by linarith
  have hle1 : 1 - M.γ ≤ 1 := by linarith
  have hiv : 0 < invMuSup μ := invMuSup_pos μ hμ
  have hm : 0 < mismatchCoeff M πstar μ := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
  have hScard : (0:ℝ) < (Fintype.card S : ℝ) := by
    have := Fintype.card_pos_iff.mpr ‹Nonempty S›
    exact_mod_cast this
  have hTpos : (0:ℝ) < (T : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
  have h6 : (0:ℝ) < (1 - M.γ) ^ 6 := pow_pos hpos 6
  have hpow : (1 - M.γ) ^ 6 ≤ (1 - M.γ) ^ 3 :=
    pow_le_pow_of_le_one hpos.le hle1 (by norm_num)
  have hd6 : (0:ℝ) < c ^ 2 * (1 - M.γ) ^ 6 * T := by positivity
  have hdle : c ^ 2 * (1 - M.γ) ^ 6 * T ≤ c ^ 2 * (1 - M.γ) ^ 3 * T := by
    have h : c ^ 2 * (1 - M.γ) ^ 6 ≤ c ^ 2 * (1 - M.γ) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    exact mul_le_mul_of_nonneg_right h hTpos.le
  have hfrac : 16 * (Fintype.card S : ℝ) / (c ^ 2 * (1 - M.γ) ^ 3 * T)
      ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T) :=
    div_le_div_of_nonneg_left (by positivity) hd6 hdle
  have hstep : invMuSup μ * (16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 3 * T)
        * mismatchCoeff M πstar μ ^ 2)
      ≤ invMuSup μ * (16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)
        * mismatchCoeff M πstar μ ^ 2) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hfrac (by positivity)) hiv.le
  refine le_trans hstep (le_of_eq ?_)
  ring

/-! ## The frozen statement, reduced -/

set_option linter.unusedVariables false in
/-- **`Goal.mei_theorem4` from its own hypotheses plus `hdom` and `hnondeg`.**

`hdom` is the interface condition `(†)` (see the module docstring): at every
iterate, `mei_theorem4`'s *given* `astar s` dominates the `πstar`-averaged
advantage of the current policy.  It is what lets Mei Lemma 8 be re-derived at
the given `astar` rather than at the argmax `g1_lojasiewicz` chooses for itself,
so that `hcbound` — which speaks only about the given `astar` — applies.

`s₀`/`hnondeg` are inherited from `mei4_rho_rate_of_g3`: they discharge
`g3_strict_suboptimality`, without which `V* − V^π ≡ 0` and the rate spine has
no strict decrease to run on.

The right-hand side is the frozen one **verbatim**; the constant arithmetic is
`rate_const_le`. -/
theorem mei_theorem4_of_astar_compat (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (ρ : Dist S)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (c : ℝ) (hc : 0 < c)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hcbound : ∀ t s, c ≤ (F.toPolicy (θ t) s) (astar s))
    -- THE INTERFACE CONDITION `(†)`.
    (hdom : ∀ t s, advGapInf M (F.toPolicy (θ t)) πstar s
      ≤ advInf M (F.toPolicy (θ t)) s (astar s))
    -- Non-degeneracy, already required by `mei4_rho_rate_of_g3`.
    (s₀ : S) (hnondeg : ∃ π : Policy S A, Vinf M π s₀ < Vstar M s₀) :
    ∀ T : ℕ, 1 ≤ T →
      VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ
        ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)
            * mismatchCoeff M πstar μ ^ 2 * Proofs.invMuSup μ := by
  intro T hT
  have hloja : ∀ t, (⨅ s : S, (F.toPolicy (θ t) s) (astar s))
      / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
      * (VstarDist M μ - VinfDist M (F.toPolicy (θ t)) μ)
    ≤ ‖fderiv ℝ (fun w => VinfDist M (F.toPolicy w) μ) (θ t)‖ := fun t =>
    g1_lojasiewicz_at_astar M F hF hr hγ₀ hγ₁ μ hμ πstar hstar astar hastar (θ t) (hdom t)
  refine le_trans
    (mei4_rho_rate_of_g3 M F hF hr hγ₀ hγ₁ μ hμ ρ πstar hstar θ hstep c hc
      astar hastar hcbound hloja s₀ hnondeg T hT) ?_
  exact rate_const_le M hγ₀ hγ₁ μ hμ πstar c hc T hT

set_option linter.unusedVariables false in
/-- **`Goal.mei_theorem4` under Mei's own optimal-value-gap assumption.**

`hgap` is `Δ*(s) > 0`, the hypothesis Mei's Lemma 9 proof opens with (and which
the frozen `g9_c_positive` already carries).  It implies the interface condition
`(†)` outright (`astar_compat_of_gap`), so the only hypothesis beyond the frozen
ones is non-degeneracy. -/
theorem mei_theorem4_of_astar_gap (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (ρ : Dist S)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (c : ℝ) (hc : 0 < c)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hcbound : ∀ t s, c ≤ (F.toPolicy (θ t) s) (astar s))
    (hgap : ∀ s a, a ≠ astar s → Qstar M s a < Qstar M s (astar s))
    (s₀ : S) (hnondeg : ∃ π : Policy S A, Vinf M π s₀ < Vstar M s₀) :
    ∀ T : ℕ, 1 ≤ T →
      VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ
        ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)
            * mismatchCoeff M πstar μ ^ 2 * Proofs.invMuSup μ :=
  mei_theorem4_of_astar_compat M F hF hr hγ₀ hγ₁ μ hμ ρ πstar hstar θ hstep c hc
    astar hastar hcbound
    (fun t s => astar_compat_of_gap M hr hγ₀ hγ₁ πstar hstar astar hastar hgap
      (F.toPolicy (θ t)) s) s₀ hnondeg

/-! ## Removing `hnondeg`

`hnondeg` was inherited from `mei4_rho_rate_of_g3`, but it is **not** a real
extra hypothesis: it can be eliminated by a classical case split.  Either some
state admits some strictly suboptimal policy — in which case
`mei_theorem4_of_astar_compat` applies directly — or no state does, in which
case `Vinf M π s = Vstar M s` for every policy and every state, so the left-hand
side of the conclusion is exactly `0`, while the right-hand side is a product of
nonnegative factors.  `hdom` is therefore the **only** hypothesis separating
this file from the frozen `Goal.mei_theorem4`. -/

set_option linter.unusedVariables false in
/-- **`Goal.mei_theorem4` from its own hypotheses plus `hdom` alone.**

`hnondeg` is discharged by a case split (see above), leaving the interface
condition `(†)` as the single hypothesis beyond the frozen signature.  The
statement below is the frozen `Goal.mei_theorem4` **verbatim**, with the one
extra binder `hdom` inserted after `hcbound`. -/
theorem mei_theorem4_of_astar_compat' (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (ρ : Dist S)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (c : ℝ) (hc : 0 < c)
    (astar : S → A) (hastar : ∀ s, 0 < (πstar s) (astar s))
    (hcbound : ∀ t s, c ≤ (F.toPolicy (θ t) s) (astar s))
    -- THE INTERFACE CONDITION `(†)` — the only hypothesis beyond the frozen ones.
    (hdom : ∀ t s, advGapInf M (F.toPolicy (θ t)) πstar s
      ≤ advInf M (F.toPolicy (θ t)) s (astar s)) :
    ∀ T : ℕ, 1 ≤ T →
      VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ
        ≤ 16 * Fintype.card S / (c ^ 2 * (1 - M.γ) ^ 6 * T)
            * mismatchCoeff M πstar μ ^ 2 * Proofs.invMuSup μ := by
  classical
  intro T hT
  by_cases hnd : ∃ s₀ : S, ∃ π : Policy S A, Vinf M π s₀ < Vstar M s₀
  · obtain ⟨s₀, hs₀⟩ := hnd
    exact mei_theorem4_of_astar_compat M F hF hr hγ₀ hγ₁ μ hμ ρ πstar hstar θ hstep
      c hc astar hastar hcbound hdom s₀ hs₀ T hT
  · -- every policy is optimal at every state: the left-hand side is `0`.
    push_neg at hnd
    have hzero : VstarDist M ρ - VinfDist M (F.toPolicy (θ T)) ρ = 0 := by
      have heq : ∀ s, Vinf M (F.toPolicy (θ T)) s = Vstar M s := fun s =>
        le_antisymm (vstar_upper_proof M hr hγ₀ hγ₁ (F.toPolicy (θ T)) s)
          (hnd s (F.toPolicy (θ T)))
      unfold VstarDist VinfDist
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero fun s _ => by rw [heq s]; ring
    rw [hzero]
    have hpos : 0 < 1 - M.γ := by linarith
    have hiv : 0 < invMuSup μ := invMuSup_pos μ hμ
    have hm : 0 < mismatchCoeff M πstar μ := mismatch_pos_proof M hγ₀ hγ₁ πstar μ hμ
    have hScard : (0:ℝ) < (Fintype.card S : ℝ) := by
      have := Fintype.card_pos_iff.mpr ‹Nonempty S›
      exact_mod_cast this
    have hTpos : (0:ℝ) < (T : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hT
    have h6 : (0:ℝ) < (1 - M.γ) ^ 6 := pow_pos hpos 6
    positivity

#print axioms mei_theorem4_of_astar_compat
#print axioms mei_theorem4_of_astar_compat'
#print axioms mei_theorem4_of_astar_gap

end Mei4D

end Proofs
end PolicyGradient
