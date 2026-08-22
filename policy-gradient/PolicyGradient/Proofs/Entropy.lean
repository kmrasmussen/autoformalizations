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

/-! ## 3. Toward Mei's Lemma 14 — the discounted entropy

**Verbatim, Mei et al. (arXiv:2005.06392), Eq. (16)** (the object):

> $\mathbb{H}(\rho,\pi)\coloneqq\mathbb{E}_{s_0\sim\rho,\,a_t\sim\pi(\cdot|s_t),\,
>   s_{t+1}\sim\mathcal P(\cdot|s_t,a_t)}
>   \left[\sum_{t=0}^{\infty}-\gamma^{t}\log\pi(a_t|s_t)\right]$

**Verbatim, Lemma 14 (Smoothness)**:

> $\mathbb{H}(\rho,\pi_{\theta})$ is $(4+8\log{A})/(1-\gamma)^{3}$-smooth, where
> $A\coloneqq|\mathcal{A}|$ is the total number of actions.

**Correction to the task brief.** Lemma 14 is *not* "`Ṽ` is `β`-smooth". It is
about the discounted entropy `ℍ` alone. The constant `(8+τ(4+8\log A))/(1-γ)³`
does exist in the paper, but only inside the **proof of Theorem 6**, never as a
numbered lemma:

> According to Lemmas 7 and 14, $V^{\pi_{\theta}}(\mu)$ is $8/(1-\gamma)^{3}$-smooth,
> and $\mathbb{H}(\mu,\pi_{\theta})$ is $(4+8\log{A})/(1-\gamma)^{3}$-smooth.
> Therefore, $\tilde{V}^{\pi_{\theta}}(\mu)=V^{\pi_{\theta}}(\mu)+\tau\cdot
> \mathbb{H}(\mu,\pi_{\theta})$ is $\beta$-smooth with
> $\beta=(8+\tau(4+8\log{A}))/(1-\gamma)^{3}$.

`ℍ` is exactly `VsoftDisc` at `r ≡ 0`, `τ = 1` — see `VsoftDisc_zero_reward_eq`
below. Note Mei's `ℍ` carries **no** `(1-γ)` normalization, matching our
unnormalized convention.

### The sharp entropy bound `H ≤ log |A|`

Lemma 14's constant is stated in terms of `log A`, so the repo's existing
`entropy_le_card` (`H ≤ |A| - 1`, adequate for `BddAbove` but not sharp) is not
enough to state it. The sharp bound is proved here. -/

/-- **`H(d) ≤ log |A|`** — the sharp entropy bound (Gibbs' inequality against the
uniform distribution).

`entropy_le_card` gives only `H ≤ |A| - 1`, which suffices for `BddAbove` but is
loose (for `|A| = 10` it is `9` versus `log 10 ≈ 2.30`). Mei's Lemma 14 constant
`(4 + 8 log A)/(1-γ)³` is stated in terms of `log A`, so the sharp form is what
that statement needs.

Proof: `H(d) - log n = ∑ₐ dₐ · log(1/(n·dₐ))`, and `log x ≤ x - 1` bounds each
summand by `dₐ·(1/(n dₐ) - 1) = 1/n - dₐ`, which sums to `0`. The `dₐ = 0` terms
contribute `0` on both sides. -/
theorem entropy_le_log_card {A : Type*} [Fintype A] [Nonempty A] (d : Dist A) :
    entropy d ≤ Real.log (Fintype.card A) := by
  set n : ℕ := Fintype.card A with hn
  have hn0 : 0 < (n : ℝ) := by
    have : 0 < n := Fintype.card_pos
    exact_mod_cast this
  -- Per-action: `-dₐ log dₐ - dₐ log n ≤ 1/n - dₐ`.
  have hterm : ∀ a : A,
      -(d a * Real.log (d a)) - d a * Real.log n ≤ 1 / n - d a := by
    intro a
    rcases eq_or_lt_of_le (d.nonneg a) with h0 | h0
    · -- `d a = 0`: LHS is `0`, RHS is `1/n ≥ 0`.
      rw [← h0]
      simp
    · -- `d a > 0`: use `log x ≤ x - 1` at `x = 1/(n · d a)`.
      have hx : (0:ℝ) < 1 / (n * d a) := by positivity
      have hlog := Real.log_le_sub_one_of_pos hx
      have hexpand : Real.log (1 / (n * d a))
          = -Real.log n - Real.log (d a) := by
        rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
          Real.log_mul (by positivity) (ne_of_gt h0)]
        ring
      rw [hexpand] at hlog
      -- `-log n - log dₐ ≤ 1/(n dₐ) - 1`; multiply by `dₐ > 0`.
      have hmul := mul_le_mul_of_nonneg_left hlog h0.le
      have hrw : d a * (1 / ((n:ℝ) * d a) - 1) = 1 / n - d a := by
        field_simp
      rw [hrw] at hmul
      calc -(d a * Real.log (d a)) - d a * Real.log n
          = d a * (-Real.log n - Real.log (d a)) := by ring
        _ ≤ 1 / n - d a := hmul
  have hsum : entropy d - Real.log n ≤ ∑ _a : A, (1:ℝ) / n - ∑ a, d a := by
    rw [entropy, ← Finset.sum_neg_distrib]
    have hlhs : (∑ a, -(d a * Real.log (d a))) - Real.log n
        = ∑ a, (-(d a * Real.log (d a)) - d a * Real.log n) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, d.sum_eq_one, one_mul]
    rw [hlhs, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun a _ => hterm a
  rw [d.sum_eq_one, Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul] at hsum
  rw [mul_one_div, div_self (ne_of_gt hn0)] at hsum
  linarith

/-- **Mei's discounted entropy `ℍ(s₀, π_θ)`**, his Eq. (16), quoted verbatim in
the section docstring.

Defined as the zero-reward, `τ = 1` soft value: `softRbar M π 1 s = H(π(·|s))`
when `r ≡ 0`, and `E_{a∼π}[-log π(a|s)] = H(π(·|s))` is exactly that. Like Mei's,
this is unnormalized (no `(1-γ)` prefactor). -/
noncomputable def discEntropy (M : FiniteMDP S A) (π : Policy S A) (s₀ : S) : ℝ :=
  ∑' t, M.γ ^ t * ∑ s, visit M π t s₀ s * entropy (π s)

/-- `ℍ` is the soft value of the zero-reward MDP at `τ = 1`. -/
theorem discEntropy_eq_VsoftDisc (M : FiniteMDP S A) (π : Policy S A) (s₀ : S) :
    discEntropy M π s₀
      = VsoftDisc { P := M.P, r := fun _ _ => 0, γ := M.γ } π 1 s₀ := by
  -- `visit` depends on the MDP only through `P`, which is unchanged.
  have hvisit : ∀ (t : ℕ) (x s : S),
      visit M π t x s = visit { P := M.P, r := fun _ _ => 0, γ := M.γ } π t x s := by
    intro t
    induction t with
    | zero => intro x s; rfl
    | succ k ih =>
      intro x s
      simp only [visit_succ, step]
      exact Finset.sum_congr rfl fun s' _ => by rw [ih x s']
  unfold discEntropy VsoftDisc
  refine tsum_congr fun t => ?_
  unfold softStepReward softRbar
  simp only []
  refine congrArg (fun z => M.γ ^ t * z) ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hvisit t s₀ s]
  simp

/-- **`0 ≤ ℍ(s₀,π) ≤ log|A| / (1-γ)`.**

The bound Lemma 14's constant is calibrated against: each step contributes an
entropy in `[0, log|A|]` (`entropy_nonneg`, `entropy_le_log_card`) and the
geometric series sums to `1/(1-γ)`. Mei's own Theorem 6 bound carries
`(1+τ log A)/(1-γ)²`, whose `log A/(1-γ)` factor is this. -/
theorem discEntropy_bounds (M : FiniteMDP S A) (π : Policy S A)
    (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    0 ≤ discEntropy M π s₀
      ∧ discEntropy M π s₀ ≤ Real.log (Fintype.card A) / (1 - M.γ) := by
  set L : ℝ := Real.log (Fintype.card A) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hHb : ∀ s, 0 ≤ entropy (π s) ∧ entropy (π s) ≤ L :=
    fun s => ⟨entropy_nonneg (π s) (fun a => Dist.le_one (π s) a),
      entropy_le_log_card (π s)⟩
  have hterm : ∀ t : ℕ,
      0 ≤ M.γ ^ t * ∑ s, visit M π t s₀ s * entropy (π s)
      ∧ M.γ ^ t * ∑ s, visit M π t s₀ s * entropy (π s) ≤ M.γ ^ t * L := by
    intro t
    have hlo : 0 ≤ ∑ s, visit M π t s₀ s * entropy (π s) :=
      Finset.sum_nonneg fun s _ => mul_nonneg (visit_nonneg M π t s₀ s) (hHb s).1
    have hhi : (∑ s, visit M π t s₀ s * entropy (π s)) ≤ L := by
      calc ∑ s, visit M π t s₀ s * entropy (π s)
          ≤ ∑ s, visit M π t s₀ s * L :=
            Finset.sum_le_sum fun s _ =>
              mul_le_mul_of_nonneg_left (hHb s).2 (visit_nonneg M π t s₀ s)
        _ = L := by rw [← Finset.sum_mul, visit_sum_eq_one, one_mul]
    exact ⟨mul_nonneg (pow_nonneg hγ₀ t) hlo,
      mul_le_mul_of_nonneg_left hhi (pow_nonneg hγ₀ t)⟩
  have hsummable : Summable (fun t => M.γ ^ t * ∑ s, visit M π t s₀ s * entropy (π s)) := by
    refine Summable.of_nonneg_of_le (fun t => (hterm t).1) (fun t => (hterm t).2)
      ((summable_geometric_of_lt_one hγ₀ hγ₁).mul_right L)
  refine ⟨tsum_nonneg fun t => (hterm t).1, ?_⟩
  have hgeo : HasSum (fun t : ℕ => M.γ ^ t * L) (L / (1 - M.γ)) := by
    have h := (hasSum_geometric_of_lt_one hγ₀ hγ₁).mul_right L
    simpa [div_eq_inv_mul, mul_comm] using h
  refine (Summable.tsum_le_tsum (fun t => (hterm t).2) hsummable hgeo.summable).trans ?_
  rw [hgeo.tsum_eq]

/-! ## 4. Toward Mei's Lemma 15 — the soft variational identity

**Verbatim, Lemma 15 (Non-uniform Łojasiewicz)**, Eq. (27):

> Suppose $\mu(s)>0$ for all state $s\in\mathcal{S}$. Then,
> $$\bigg\|\frac{\partial\tilde{V}^{\pi_{\theta}}(\mu)}{\partial\theta}\bigg\|_{2}
>   \geq C(\theta)\cdot\left[\tilde{V}^{\pi_{\tau}^{*}}(\rho)
>   -\tilde{V}^{\pi_{\theta}}(\rho)\right]^{\frac{1}{2}},$$
> where
> $$C(\theta)\coloneqq\frac{\sqrt{2\tau}}{\sqrt{S}}\cdot\min_{s}{\sqrt{\mu(s)}}
>   \cdot\min_{s,a}{\pi_{\theta}(a|s)}
>   \cdot\bigg\|\frac{d_{\rho}^{\pi_{\tau}^{*}}}
>   {d_{\mu}^{\pi_{\theta}}}\bigg\|_{\infty}^{-\frac{1}{2}}.$$

Its engine is **Lemma 26 (Soft sub-optimality lemma)**, quoted verbatim in §2,
which turns the soft sub-optimality gap into a KL divergence. That in turn rests
on the **soft-greedy variational identity** proved here: the soft Bellman
backup is a `logsumexp`, attained at the soft-greedy policy, with the shortfall
of any other policy an exact KL.

**Verbatim, Eq. (519)** (the soft greedy policy):

> $\bar\pi_\theta(\cdot|s)=\mathrm{softmax}(\tilde Q^{\pi_\theta}(s,\cdot)/\tau)$

**Verbatim, Eqs. (25)–(26)** (softmax optimal consistency, the fixed-point form):

> $\pi_\tau^*(a|s)=\exp\{(\tilde Q^{\pi_\tau^*}(s,a)-\tilde V^{\pi_\tau^*}(s))/\tau\}$
> and
> $\tilde V^{\pi_\tau^*}(s)=\tau\log\sum_a\exp\{\tilde Q^{\pi_\tau^*}(s,a)/\tau\}$.

**Where this stops.** What is proved below is the per-state variational identity
and its consequences (`softBackup_eq_logsumexp`, `softBackup_le`,
`softBackup_sub_eq_KL`). Lemma 15 itself is **not** proved: it additionally needs
(a) the existence of `π_τ^*` as a fixed point of the soft-greedy map — a
contraction argument not yet in this repo — and (b) the gradient formula
(Mei's Lemma 10) for `Ṽ` under the tabular softmax, which needs the entropy
analogue of the whole `G7b` derivative ladder. Both are stated here as the
remaining gaps rather than assumed. -/

/-- The **soft backup functional**: what a one-step distribution `q` at state `s`
earns against action-values `Q`, including its own entropy bonus.

`B_τ(q; Q) = ∑ₐ q(a)·Q(a) + τ·H(q)`. The soft Bellman equation says
`Ṽ^π(s) = B_τ(π(·|s); Q̃^π(s,·))` (`VsoftDisc_eq_sum_QsoftDisc`). -/
noncomputable def softBackup (τ : ℝ) (q : Dist A) (Q : A → ℝ) : ℝ :=
  (∑ a, q a * Q a) + τ * entropy q

/-- **The soft backup is maximized by the soft-greedy policy, with value
`τ·log ∑ₐ exp(Q(a)/τ)`.**

This is Mei's Eq. (26) as a *variational* statement rather than a fixed-point
assertion: for `τ > 0`,
`B_τ(softmax(Q/τ); Q) = τ · log ∑ₐ exp(Q(a)/τ)`.

Proof: at `q = softmax(Q/τ)`, `log q(a) = Q(a)/τ - log Z` with `Z = ∑ exp(Q/τ)`,
so `τ·H(q) = -τ ∑ q(a)(Q(a)/τ - log Z) = -∑ q(a)Q(a) + τ log Z`, and the
`∑ q Q` terms cancel exactly. -/
theorem softBackup_softmax (τ : ℝ) (hτ : 0 < τ) (Q : A → ℝ) :
    softBackup τ (softmax (fun a => Q a / τ)) Q
      = τ * Real.log (∑ a, Real.exp (Q a / τ)) := by
  set Z : ℝ := ∑ a', Real.exp (Q a' / τ) with hZ
  have hZpos : 0 < Z := softmax_denom_pos (fun a => Q a / τ)
  set q : Dist A := softmax (fun a => Q a / τ) with hq
  have hlog : ∀ a, Real.log (q a) = Q a / τ - Real.log Z := by
    intro a
    rw [hq, softmax_apply, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZpos),
      Real.log_exp]
  unfold softBackup entropy
  rw [Finset.sum_congr rfl (fun a _ => by rw [hlog a]; ring :
    ∀ a ∈ (univ : Finset A), q a * Real.log (q a)
      = q a * (Q a / τ) - q a * Real.log Z)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, q.sum_eq_one, one_mul]
  have hqQ : ∑ a, q a * (Q a / τ) = (∑ a, q a * Q a) / τ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hqQ]
  field_simp
  ring

/-- **The exact shortfall of any policy against the soft-greedy one is a KL.**

For `τ > 0` and any distribution `q`,
`B_τ(softmax(Q/τ); Q) - B_τ(q; Q) = τ · ∑ₐ q(a)·(log q(a) - log softmax(Q/τ)(a))`,
the right-hand side being `τ·D_KL(q ‖ softmax(Q/τ)) ≥ 0`.

This is the mechanism that puts a KL on the right of **Lemma 26**: the soft
sub-optimality gap is, state by state, exactly `τ` times a KL divergence.
Written without a `log`-of-a-ratio so that `q a = 0` is harmless. -/
theorem softBackup_sub_eq_KL (τ : ℝ) (hτ : 0 < τ) (Q : A → ℝ) (q : Dist A) :
    softBackup τ (softmax (fun a => Q a / τ)) Q - softBackup τ q Q
      = τ * ∑ a, q a
          * (Real.log (q a) - Real.log ((softmax (fun a => Q a / τ)) a)) := by
  set Z : ℝ := ∑ a', Real.exp (Q a' / τ) with hZ
  have hZpos : 0 < Z := softmax_denom_pos (fun a => Q a / τ)
  have hlog : ∀ a, Real.log ((softmax (fun a => Q a / τ)) a) = Q a / τ - Real.log Z := by
    intro a
    rw [softmax_apply, Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZpos),
      Real.log_exp]
  rw [softBackup_softmax τ hτ Q]
  -- The right-hand side, expanded.
  have hrhs : ∑ a, q a
        * (Real.log (q a) - Real.log ((softmax (fun a => Q a / τ)) a))
      = (∑ a, q a * Real.log (q a)) - (∑ a, q a * Q a) / τ + Real.log Z := by
    rw [Finset.sum_congr rfl (fun a _ => by rw [hlog a]; ring :
      ∀ a ∈ (univ : Finset A), q a * (Real.log (q a)
          - Real.log ((softmax (fun a => Q a / τ)) a))
        = q a * Real.log (q a) - q a * (Q a / τ) + q a * Real.log Z)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      q.sum_eq_one, one_mul]
    congr 1
    congr 1
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hrhs, ← hZ]
  unfold softBackup entropy
  field_simp
  ring

/-- **The soft-greedy backup dominates every policy's**: `B_τ(q; Q) ≤ τ·log ∑ exp(Q/τ)`.

Immediate from `softBackup_sub_eq_KL` plus nonnegativity of the KL. The KL is
nonnegative by `log x ≤ x - 1` applied to `x = softmax(Q/τ)(a)/q(a)`, summed. -/
theorem softBackup_le (τ : ℝ) (hτ : 0 < τ) (Q : A → ℝ) (q : Dist A) :
    softBackup τ q Q ≤ τ * Real.log (∑ a, Real.exp (Q a / τ)) := by
  set P : Dist A := softmax (fun a => Q a / τ) with hP
  have hPpos : ∀ a, 0 < P a := fun a => softmax_pos (fun a => Q a / τ) a
  -- `D_KL(q ‖ P) ≥ 0`: each term satisfies `q a (log q a - log P a) ≥ q a - P a`,
  -- since `log(P/q) ≤ P/q - 1` gives `q·log(q/P) ≥ q·(1 - P/q) = q - P`.
  have hterm : ∀ a, q a - P a ≤ q a * (Real.log (q a) - Real.log (P a)) := by
    intro a
    rcases eq_or_lt_of_le (q.nonneg a) with h0 | h0
    · -- `q a = 0`: LHS is `-P a ≤ 0`, RHS is `0`.
      rw [← h0]
      simp only [zero_mul, zero_sub, neg_nonpos, sub_zero]
      linarith [(hPpos a).le]
    · -- `q a > 0`: `log (P a / q a) ≤ P a / q a - 1`, times `q a > 0`.
      have hx : (0:ℝ) < P a / q a := div_pos (hPpos a) h0
      have hlog := Real.log_le_sub_one_of_pos hx
      rw [Real.log_div (ne_of_gt (hPpos a)) (ne_of_gt h0)] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog h0.le
      have hrw : q a * (P a / q a - 1) = P a - q a := by field_simp
      rw [hrw] at hmul
      -- `hmul : q a * (log P a - log q a) ≤ P a - q a`; negate both sides.
      have hneg : q a * (Real.log (q a) - Real.log (P a))
          = -(q a * (Real.log (P a) - Real.log (q a))) := by ring
      rw [hneg]
      linarith [hmul]
  have hKL : 0 ≤ ∑ a, q a * (Real.log (q a) - Real.log (P a)) := by
    have hsum : ∑ a, (q a - P a) ≤ ∑ a, q a * (Real.log (q a) - Real.log (P a)) :=
      Finset.sum_le_sum fun a _ => hterm a
    rw [Finset.sum_sub_distrib, P.sum_eq_one, q.sum_eq_one, sub_self] at hsum
    exact hsum
  have hid := softBackup_sub_eq_KL τ hτ Q q
  rw [softBackup_softmax τ hτ Q] at hid
  nlinarith [mul_nonneg hτ.le hKL]

/-- **The soft Bellman backup of `π` at `s` is `Ṽ^π(s)`** — restating
`VsoftDisc_eq_sum_QsoftDisc` in `softBackup` vocabulary, so the variational
lemmas above apply directly to the soft value. -/
theorem VsoftDisc_eq_softBackup (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ)
    (hτ : 0 ≤ τ) (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (s : S) :
    VsoftDisc M π τ s = softBackup τ (π s) (QsoftDisc M π τ s) :=
  VsoftDisc_eq_sum_QsoftDisc M π τ hτ hr hγ₀ hγ₁ s

/-- **The soft Bellman optimality gap at a state, as an exact KL.**

Combining the previous two: for `τ > 0`,
`τ·log ∑ₐ exp(Q̃^π(s,a)/τ) − Ṽ^π(s)
   = τ·∑ₐ π(a|s)·(log π(a|s) − log softmax(Q̃^π(s,·)/τ)(a)) ≥ 0`.

This is the per-state form of the soft policy-improvement step: a policy is soft
Bellman optimal at `s` exactly when it *is* the soft-greedy policy there. It is
the state-local half of Lemma 26; the trajectory half is `perfDiffSoft`. -/
theorem VsoftDisc_softBellman_gap (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ)
    (hτ : 0 < τ) (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (s : S) :
    τ * Real.log (∑ a, Real.exp (QsoftDisc M π τ s a / τ)) - VsoftDisc M π τ s
      = τ * ∑ a, (π s) a
          * (Real.log ((π s) a)
            - Real.log ((softmax (fun a => QsoftDisc M π τ s a / τ)) a)) := by
  rw [VsoftDisc_eq_softBackup M π τ hτ.le hr hγ₀ hγ₁ s,
    ← softBackup_softmax τ hτ (QsoftDisc M π τ s)]
  exact softBackup_sub_eq_KL τ hτ (QsoftDisc M π τ s) (π s)

/-- **`Ṽ^π(s) ≤ τ·log ∑ₐ exp(Q̃^π(s,a)/τ)`** — the soft value never exceeds its
own soft-greedy backup. -/
theorem VsoftDisc_le_logsumexp (M : FiniteMDP S A) (π : Policy S A) (τ : ℝ)
    (hτ : 0 < τ) (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (s : S) :
    VsoftDisc M π τ s ≤ τ * Real.log (∑ a, Real.exp (QsoftDisc M π τ s a / τ)) := by
  rw [VsoftDisc_eq_softBackup M π τ hτ.le hr hγ₀ hγ₁ s]
  exact softBackup_le τ hτ (QsoftDisc M π τ s) (π s)

end Proofs
end PolicyGradient
