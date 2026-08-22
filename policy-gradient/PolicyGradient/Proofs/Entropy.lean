/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Soft

/-!
# Entropy.lean — the entropy-regularized stack over `VsoftDisc`

`Proofs.VsoftDisc` (in `Soft.lean`) is the *soft Bellman fixed point*: entropy is
collected at every step and discounted along the trajectory, which is Mei et
al.'s `Ṽ`. This file builds on it.
-/

open Finset

namespace PolicyGradient
namespace Proofs

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-! ## 1. The optimal soft value is well-defined -/

/-- Uniform bound on the soft value: `|Ṽ^π(s₀)| ≤ (1 + τ(|A|-1))/(1-γ)`.

Each step contributes at most `γᵗ · (1 + τ(|A|-1))` (`abs_softStepReward_le`),
and the geometric series sums. Mirrors `abs_Vinf_le`. -/
theorem abs_VsoftDisc_le (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    |VsoftDisc M π τ s₀|
      ≤ (1 + τ * ((Fintype.card A : ℝ) - 1)) / (1 - M.γ) := by
  set R : ℝ := 1 + τ * ((Fintype.card A : ℝ) - 1) with hR
  have hgeo : HasSum (fun t : ℕ => M.γ ^ t * R) (R / (1 - M.γ)) := by
    have h := (hasSum_geometric_of_lt_one hγ₀ hγ₁).mul_right R
    simpa [div_eq_inv_mul, mul_comm] using h
  have := tsum_of_norm_bounded (f := fun t => softStepReward M π τ t s₀) hgeo
    (fun t => by
      simpa [Real.norm_eq_abs] using abs_softStepReward_le M π τ hτ hr hγ₀ t s₀)
  simpa [VsoftDisc, Real.norm_eq_abs] using this

/-- Every policy's soft value is at most `(1 + τ(|A|-1))/(1-γ)`. -/
theorem VsoftDisc_le_bound (M : FiniteMDP S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ : S) :
    VsoftDisc M π τ s₀ ≤ (1 + τ * ((Fintype.card A : ℝ) - 1)) / (1 - M.γ) :=
  (le_abs_self _).trans (abs_VsoftDisc_le M π τ hτ hr hγ₀ hγ₁ s₀)

/-- **The soft policy values are bounded above**, uniformly in `π`.

This is load-bearing: `ciSup` over an unbounded family is Mathlib's junk value
`0`, so without this every statement about `VsoftStarDisc` would be vacuous.
Mirrors `Proofs.bddAbove_range_Vinf`. -/
theorem bddAbove_range_VsoftDisc (M : FiniteMDP S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    BddAbove (Set.range fun π : Policy S A => VsoftDisc M π τ s₀) := by
  refine ⟨(1 + τ * ((Fintype.card A : ℝ) - 1)) / (1 - M.γ), ?_⟩
  rintro x ⟨π, rfl⟩
  exact VsoftDisc_le_bound M τ hτ hr hγ₀ hγ₁ π s₀

/-- **The optimal discounted-entropy soft value**, `Ṽ*(s₀) = ⨆_π Ṽ^π(s₀)`.

Unlike `Target.VsoftStar` (which sups the start-state-only `VinfSoft`), this is
the supremum of the genuine soft Bellman fixed point — Mei's `Ṽ*`. -/
noncomputable def VsoftStarDisc (M : FiniteMDP S A) (τ : ℝ) (s₀ : S) : ℝ :=
  ⨆ π : Policy S A, VsoftDisc M π τ s₀

/-- `Ṽ^π(s₀) ≤ Ṽ*(s₀)` — the sup really dominates. Needs `BddAbove`. -/
theorem VsoftDisc_le_VsoftStarDisc (M : FiniteMDP S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (π : Policy S A) (s₀ : S) :
    VsoftDisc M π τ s₀ ≤ VsoftStarDisc M τ s₀ :=
  le_ciSup (bddAbove_range_VsoftDisc M τ hτ hr hγ₀ hγ₁ s₀) π

/-- `Ṽ*(s₀) ≤ (1 + τ(|A|-1))/(1-γ)` — the sup is finite. Needs
`Nonempty (Policy S A)` (via `instNonemptyPolicy`), else `ciSup_le` cannot fire. -/
theorem VsoftStarDisc_le (M : FiniteMDP S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    VsoftStarDisc M τ s₀ ≤ (1 + τ * ((Fintype.card A : ℝ) - 1)) / (1 - M.γ) :=
  ciSup_le fun π => VsoftDisc_le_bound M τ hτ hr hγ₀ hγ₁ π s₀

/-- `Ṽ*` is also bounded below, by `-(1 + τ(|A|-1))/(1-γ)`: it dominates any one
policy's soft value, which is bounded below by `abs_VsoftDisc_le`. Together with
`VsoftStarDisc_le` this pins `Ṽ*` inside a genuine interval, ruling out the
degenerate reading where the `⨆` silently returned `0`. -/
theorem neg_le_VsoftStarDisc (M : FiniteMDP S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    -((1 + τ * ((Fintype.card A : ℝ) - 1)) / (1 - M.γ)) ≤ VsoftStarDisc M τ s₀ := by
  obtain ⟨π⟩ := (inferInstance : Nonempty (Policy S A))
  refine le_trans ?_ (VsoftDisc_le_VsoftStarDisc M τ hτ hr hγ₀ hγ₁ π s₀)
  have := abs_VsoftDisc_le M π τ hτ hr hγ₀ hγ₁ s₀
  rw [abs_le] at this
  exact this.1


/-! ## 2. Soft performance difference

**Verbatim, Mei et al. (arXiv:2005.06392), Eq. (18)** (the soft advantage):

> $\tilde A^{\pi_\theta}(s,a) \coloneqq \tilde Q^{\pi_\theta}(s,a)
>   - \tau\log\pi_\theta(a|s) - \tilde V^{\pi_\theta}(s)$,
> with $\tilde Q^{\pi_\theta}(s,a) \coloneqq r(s,a)
>   + \gamma\sum_{s'}\mathcal P(s'|s,a)\tilde V^{\pi_\theta}(s')$.

Note where the `τ log π` sits: in the **advantage**, not in `Q̃`.

**Verbatim, Lemma 26 (Soft sub-optimality lemma), Eq. (724)**:

> For any policy `π`,
> $\tilde V^{\pi_\tau^*}(\rho)-\tilde V^{\pi}(\rho)
>  = \frac{1}{1-\gamma}\sum_s\left[d_\rho^{\pi}(s)\cdot\tau\cdot
>    D_{\mathrm{KL}}(\pi(\cdot|s)\|\pi_\tau^*(\cdot|s))\right]$.

What is proved below is the **general two-policy** identity that Lemma 26 is the
`π' = π_τ^*` special case of. Two deliberate departures from the paper:

1. Mei's `d_ρ^π` is **normalized** (his Eq. (3) carries a `(1-γ)` factor), so his
   identities carry a compensating `1/(1-γ)`. Our `dinf` is unnormalized (it sums
   to `1/(1-γ)`), so no such factor appears. Same statement, different
   normalization convention — this repo's convention throughout, cf. `perfDiffInf`.
2. Lemma 26 specializes to `π' = π_τ^*` and then rewrites the resulting
   expression as a KL divergence using the softmax-consistency identity
   `π_τ^*(a|s) = exp((Q̃^{π_τ^*}(s,a) - Ṽ^{π_τ^*}(s))/τ)` (his Eqs. (25)–(26)).
   That rewrite needs the optimal soft policy's fixed-point characterization,
   which is not yet available here; the identity below is the step *before* it,
   and is what `perfDiffInf` is for the unregularized case.
-/

/-- The soft action-value `Q̃^π(s,a) = r(s,a) + γ ∑_{s'} P(s'|s,a) Ṽ^π(s')`.

Exactly Mei's `Q̃`: no `τ log π` term — that lives in the advantage. -/
noncomputable def QsoftDisc (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ)
    (s : S) (a : A) : ℝ :=
  M.r s a + M.γ * ∑ s', (M.P s a) s' * VsoftDisc M π τ s'

/-- Mei's **soft advantage**, Eq. (18):
`Ã^π(s,a) = Q̃^π(s,a) - τ·log π(a|s) - Ṽ^π(s)`. -/
noncomputable def advSoft (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ)
    (s : S) (a : A) : ℝ :=
  QsoftDisc M π τ s a - τ * Real.log ((π s) a) - VsoftDisc M π τ s

/-- The soft Bellman equation in `Q̃` form:
`Ṽ^π(s) = ∑ₐ π(a|s)·Q̃^π(s,a) + τ·H(π(·|s))`. -/
theorem VsoftDisc_eq_sum_QsoftDisc (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ)
    (hτ : 0 ≤ τ) (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (s : S) :
    VsoftDisc M π τ s = (∑ a, (π s) a * QsoftDisc M π τ s a) + τ * entropy (π s) := by
  rw [VsoftDisc_bellman M π τ hτ hr hγ₀ hγ₁ s,
    step_expect_eq M π (fun s' => VsoftDisc M π τ s') s]
  unfold softRbar QsoftDisc
  have : ∑ a, (π s) a * (M.r s a + M.γ * ∑ s', (M.P s a) s' * VsoftDisc M π τ s')
      = (∑ a, (π s) a * M.r s a)
        + M.γ * ∑ a, (π s) a * ∑ s', (M.P s a) s' * VsoftDisc M π τ s' := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this]; ring

/-- **The soft advantage of `π` is centered under `π` itself**: `∑ₐ π(a|s)·Ã^π(s,a) = 0`.

This is the sanity check that `advSoft` carries the entropy term in the right
place — the `-τ log π(a|s)` inside the advantage averages under `π` to exactly
the `+τ·H(π(·|s))` that the soft Bellman equation adds. -/
theorem sum_advSoft_self (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ)
    (hτ : 0 ≤ τ) (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (s : S) :
    ∑ a, (π s) a * advSoft M π τ s a = 0 := by
  unfold advSoft
  have hsplit : ∑ a, (π s) a * (QsoftDisc M π τ s a - τ * Real.log ((π s) a)
        - VsoftDisc M π τ s)
      = (∑ a, (π s) a * QsoftDisc M π τ s a)
        - τ * (∑ a, (π s) a * Real.log ((π s) a))
        - (∑ a, (π s) a) * VsoftDisc M π τ s := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit, (π s).sum_eq_one, one_mul,
    VsoftDisc_eq_sum_QsoftDisc M π τ hτ hr hγ₀ hγ₁ s]
  unfold entropy
  ring

/-- The `π'`-averaged soft advantage of `π` at a state — the entropy analogue of
`Proofs.advGapInf`.

`Ã(s) = ∑ₐ π'(a|s)·Ã^π(s,a)`. Expanding, this equals
`∑ₐ π'(a|s)·Q̃^π(s,a) − τ·∑ₐ π'(a|s)·log π(a|s) − Ṽ^π(s)`, so the
`τ`-term is the **cross-entropy of `π'` against `π`**, not `π'`'s own entropy.
That asymmetry is exactly the KL that Lemma 26 exhibits. -/
noncomputable def advGapSoft (M : FiniteMDP S A) (π π' : Policy S A) (τ : ℝ)
    (s : S) : ℝ :=
  ∑ a, (π' s) a * advSoft M π τ s a

/-- The **entropy-difference remainder**: `H(π'(·|s)) − CE(π'(·|s) ‖ π(·|s))`,
written without a `log`-of-a-ratio so that zero probabilities are harmless.
Equal to `−D_KL(π'(·|s) ‖ π(·|s))` wherever both are strictly positive. -/
noncomputable def entGap (π π' : Policy S A) (s : S) : ℝ :=
  ∑ a, (π' s) a * (Real.log ((π s) a) - Real.log ((π' s) a))

/-- **One-step soft performance difference.**

`Ṽ^{π'}(s) − Ṽ^π(s) = advGapSoft + τ·entGap + γ·∑_{s'} step^{π'}(s,s')·(Ṽ^{π'}(s') − Ṽ^π(s'))`.

Mirrors `Proofs.perfDiffInf_step`. The extra `τ·entGap` term is the entropy
correction: `advGapSoft` charges `π'` the cross-entropy `−∑ π' log π`, but `π'`
actually collects its own entropy `−∑ π' log π'`. -/
theorem perfDiffSoft_step (M : FiniteMDP S A) (π π' : Policy S A) (τ : ℝ)
    (hτ : 0 ≤ τ) (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (s : S) :
    VsoftDisc M π' τ s - VsoftDisc M π τ s
      = advGapSoft M π π' τ s + τ * entGap π π' s
        + M.γ * ∑ s', step M π' s s'
            * (VsoftDisc M π' τ s' - VsoftDisc M π τ s') := by
  -- Expand `Ṽ^{π'}(s)` via its own soft Bellman equation.
  have hπ' : VsoftDisc M π' τ s
      = (∑ a, (π' s) a * QsoftDisc M π' τ s a) + τ * entropy (π' s) :=
    VsoftDisc_eq_sum_QsoftDisc M π' τ hτ hr hγ₀ hγ₁ s
  -- Expand `advGapSoft`.
  have hadv : advGapSoft M π π' τ s
      = (∑ a, (π' s) a * QsoftDisc M π τ s a)
        - τ * (∑ a, (π' s) a * Real.log ((π s) a))
        - VsoftDisc M π τ s := by
    unfold advGapSoft advSoft
    rw [show ∑ a, (π' s) a * (QsoftDisc M π τ s a - τ * Real.log ((π s) a)
          - VsoftDisc M π τ s)
        = (∑ a, (π' s) a * QsoftDisc M π τ s a)
          - τ * (∑ a, (π' s) a * Real.log ((π s) a))
          - (∑ a, (π' s) a) * VsoftDisc M π τ s from by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring]
    rw [(π' s).sum_eq_one, one_mul]
  -- The entropy bookkeeping: `τ·H(π') = -τ·(∑ π' log π) + τ·entGap`, since
  -- `entGap = ∑ π' log π - ∑ π' log π'` and `H(π') = -∑ π' log π'`.
  have hent : τ * entropy (π' s)
      = -(τ * (∑ a, (π' s) a * Real.log ((π s) a))) + τ * entGap π π' s := by
    unfold entropy entGap
    rw [show ∑ a, (π' s) a * (Real.log ((π s) a) - Real.log ((π' s) a))
        = (∑ a, (π' s) a * Real.log ((π s) a))
          - ∑ a, (π' s) a * Real.log ((π' s) a) from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring]
    ring
  -- The γ-term: the `Q̃` gap is a discounted push of the value gap.
  have hstep : M.γ * ∑ s', step M π' s s'
        * (VsoftDisc M π' τ s' - VsoftDisc M π τ s')
      = (∑ a, (π' s) a * QsoftDisc M π' τ s a)
        - ∑ a, (π' s) a * QsoftDisc M π τ s a := by
    have hQ : ∀ a, QsoftDisc M π' τ s a - QsoftDisc M π τ s a
        = M.γ * ∑ s', (M.P s a) s'
            * (VsoftDisc M π' τ s' - VsoftDisc M π τ s') := by
      intro a
      unfold QsoftDisc
      rw [show ∑ s', (M.P s a) s' * (VsoftDisc M π' τ s' - VsoftDisc M π τ s')
          = (∑ s', (M.P s a) s' * VsoftDisc M π' τ s')
            - ∑ s', (M.P s a) s' * VsoftDisc M π τ s' from by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s' _ => by ring]
      ring
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun a _ => by rw [← mul_sub, hQ a] :
      ∀ a ∈ (univ : Finset A),
        (π' s) a * QsoftDisc M π' τ s a - (π' s) a * QsoftDisc M π τ s a
        = (π' s) a * (M.γ * ∑ s', (M.P s a) s'
            * (VsoftDisc M π' τ s' - VsoftDisc M π τ s')))]
    unfold step
    calc M.γ * ∑ s', (∑ a, (π' s) a * (M.P s a) s')
            * (VsoftDisc M π' τ s' - VsoftDisc M π τ s')
        = ∑ s', ∑ a, M.γ * ((π' s) a * (M.P s a) s'
            * (VsoftDisc M π' τ s' - VsoftDisc M π τ s')) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ a, ∑ s', M.γ * ((π' s) a * (M.P s a) s'
            * (VsoftDisc M π' τ s' - VsoftDisc M π τ s')) := Finset.sum_comm
      _ = ∑ a, (π' s) a * (M.γ * ∑ s', (M.P s a) s'
            * (VsoftDisc M π' τ s' - VsoftDisc M π τ s')) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s' _ => by ring
  rw [hadv, hπ', hent, hstep]; ring

/-- The occupancy-weighted soft advantage — the entropy analogue of `Proofs.pdInf`.

Note `entGap` is folded in *at each state*, weighted by the same occupancy: the
entropy correction is collected along the trajectory exactly like the reward. -/
noncomputable def pdSoft (M : FiniteMDP S A) (π π' : Policy S A) (τ : ℝ)
    (s₀ : S) : ℝ :=
  ∑ s, dinf M π' s₀ s * (advGapSoft M π π' τ s + τ * entGap π π' s)

/-- `pdSoft` satisfies the same one-step recursion as the soft value gap.

Verbatim the proof of `Proofs.pdInf_step`, with `advGapInf` replaced by
`advGapSoft + τ·entGap`. -/
theorem pdSoft_step (M : FiniteMDP S A) (π π' : Policy S A) (τ : ℝ)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    pdSoft M π π' τ s₀
      = (advGapSoft M π π' τ s₀ + τ * entGap π π' s₀)
        + M.γ * ∑ s', step M π' s₀ s' * pdSoft M π π' τ s' := by
  unfold pdSoft
  set F : S → ℝ := fun s => advGapSoft M π π' τ s + τ * entGap π π' s with hF
  have hd : ∀ s, dinf M π' s₀ s
      = (if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π' s₀ s' * dinf M π' s' s :=
    fun s => dinf_eq M π' hγ₀ hγ₁ s₀ s
  rw [Finset.sum_congr rfl (fun s _ => by rw [hd s] :
    ∀ s ∈ (univ : Finset S), dinf M π' s₀ s * F s
      = ((if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π' s₀ s' * dinf M π' s' s)
          * F s)]
  rw [Finset.sum_congr rfl (fun s _ => by by_cases h : s = s₀ <;> simp [h] <;> ring :
    ∀ s ∈ (univ : Finset S),
      ((if s = s₀ then 1 else 0) + M.γ * ∑ s', step M π' s₀ s' * dinf M π' s' s)
          * F s
      = (if s = s₀ then F s else 0)
        + M.γ * ((∑ s', step M π' s₀ s' * dinf M π' s' s) * F s))]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ s₀ F]
  simp only [mem_univ, if_true]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ s, (∑ s', step M π' s₀ s' * dinf M π' s' s) * F s
      = ∑ s, ∑ s', step M π' s₀ s' * (dinf M π' s' s * F s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s' _ => by ring
    _ = ∑ s', ∑ s, step M π' s₀ s' * (dinf M π' s' s * F s) := Finset.sum_comm
    _ = ∑ s', step M π' s₀ s' * ∑ s, dinf M π' s' s * F s := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [Finset.mul_sum]

/-- **Soft performance difference lemma.**

`Ṽ^{π'}(s₀) - Ṽ^π(s₀) = ∑_s d^{π'}(s₀,s) · [ ∑ₐ π'(a|s)·Ã^π(s,a) + τ·entGap(s) ]`

where `Ã^π` is Mei's soft advantage (Eq. (18)) and
`entGap(s) = ∑ₐ π'(a|s)·(log π(a|s) − log π'(a|s)) = −D_KL(π'(·|s)‖π(·|s))`.

This is the general two-policy identity underlying Mei's **Lemma 26**, quoted
verbatim in the section docstring above. Two conscious departures, also stated
there: (a) our `dinf` is unnormalized, so no `1/(1-γ)` prefactor appears;
(b) Lemma 26 is the `π' = π_τ^*` case, where the softmax-consistency identity
collapses `advGapSoft + τ·entGap` into a single `τ·D_KL`. That collapse needs the
optimal soft policy's fixed-point characterization and is **not** proved here.

Proof: both sides satisfy the same one-step recursion (`perfDiffSoft_step`,
`pdSoft_step`), so their difference `D` obeys `D = γ·∑ step·D`, and
`Proofs.eq_zero_of_contraction` forces `D ≡ 0`. Verbatim the shape of
`Proofs.perfDiffInf`. -/
theorem perfDiffSoft (M : FiniteMDP S A) (π π' : Policy S A) (τ : ℝ)
    (hτ : 0 ≤ τ) (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (s₀ : S) :
    VsoftDisc M π' τ s₀ - VsoftDisc M π τ s₀ = pdSoft M π π' τ s₀ := by
  set D : S → ℝ :=
    fun s => (VsoftDisc M π' τ s - VsoftDisc M π τ s) - pdSoft M π π' τ s with hDdef
  have hD : ∀ s, D s = M.γ * ∑ s', step M π' s s' * D s' := by
    intro s
    have h1 := perfDiffSoft_step M π π' τ hτ hr hγ₀ hγ₁ s
    have h2 := pdSoft_step M π π' τ hγ₀ hγ₁ s
    have hsplit : ∑ s', step M π' s s' * D s'
        = (∑ s', step M π' s s' * (VsoftDisc M π' τ s' - VsoftDisc M π τ s'))
          - ∑ s', step M π' s s' * pdSoft M π π' τ s' := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s' _ => by simp [hDdef]; ring
    rw [hDdef]
    simp only []
    rw [hsplit, h1, h2]
    ring
  have := eq_zero_of_contraction M π' hγ₀ hγ₁ D hD s₀
  rw [hDdef] at this
  simp only [] at this
  linarith

/-- Sanity check: with `τ = 0` the soft performance difference collapses to
`Proofs.perfDiffInf`'s statement shape — `pdSoft` reduces to `pdInf` and
`VsoftDisc` to `Vinf`, because `softRbar M π 0 = r̄` and `softStepReward = stepReward`. -/
theorem VsoftDisc_zero (M : FiniteMDP S A) (π : Policy S A) (s₀ : S) :
    VsoftDisc M π 0 s₀ = Vinf M π s₀ := by
  unfold VsoftDisc Vinf
  refine tsum_congr fun t => ?_
  unfold softStepReward stepReward softRbar
  simp
