/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Mei6

/-!
# Soft.lean — the entropy-regularized prerequisites

Two frozen infrastructure goals for the entropy track:

* `entropy_bdd_proof` — `H(d) ≤ |A| - 1`, delegating to `entropy_le_card`.
* `vsoftDisc_exists_proof` — existence of the **discounted-entropy soft value**,
  the soft Bellman fixed point `Ṽ^π(s) = r̄(s) + τ·H(π(·|s)) + γ·E[Ṽ^π(s')]`.

The soft value is built the same way `Vinf` is (`Infinite.lean`): as a `tsum` of
per-step discounted contributions along the induced Markov chain, with the
per-state reward `r̄(s)` replaced by `r̄(s) + τ·H(π(·|s))`. The Bellman identity
is then the same split-off-`t=0` argument as `Vinf_bellman`, so no contraction
machinery is needed — the fixed point is constructed, not merely asserted.
-/

open Finset

namespace PolicyGradient
namespace Proofs

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-! ## Goal A — the entropy bound -/

/-- **Frozen goal `Goal.entropy_bdd`.** `H(d) ≤ |A| - 1`.

Already available as `entropy_le_card`, proved during the Theorem 6 refutation
from `x - 1 ≤ x log x`. -/
theorem entropy_bdd_proof {A : Type*} [Fintype A] (d : Dist A) :
    entropy d ≤ (Fintype.card A : ℝ) - 1 :=
  entropy_le_card d

/-! ## Goal B — the discounted-entropy soft value

### The soft per-state reward -/

variable (M : FiniteMDP S A)

/-- The per-state expected reward augmented by the entropy bonus:
`r̃(s) = ∑ₐ π(a|s) r(s,a) + τ·H(π(·|s))`. -/
noncomputable def softRbar (π : Policy S A) (τ : ℝ) (s : S) : ℝ :=
  (∑ a, (π s) a * M.r s a) + τ * entropy (π s)

/-- Every coordinate of a `Dist` is at most `1`. -/
theorem Dist.le_one {ι : Type*} [Fintype ι] (p : Dist ι) (i : ι) : p i ≤ 1 := by
  have hle : p i ≤ ∑ j, p j :=
    Finset.single_le_sum (fun j _ => p.nonneg j) (mem_univ i)
  rw [p.sum_eq_one] at hle
  exact hle

omit [DecidableEq S] in
/-- The soft per-state reward is bounded, uniformly in `s` and `π`. -/
theorem abs_softRbar_le (π : Policy S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (s : S) :
    |softRbar M π τ s| ≤ 1 + τ * ((Fintype.card A : ℝ) - 1) := by
  have hH0 : 0 ≤ entropy (π s) :=
    entropy_nonneg (π s) (fun a => Dist.le_one (π s) a)
  have hH1 : entropy (π s) ≤ (Fintype.card A : ℝ) - 1 := entropy_le_card (π s)
  have hrb : |∑ a, (π s) a * M.r s a| ≤ 1 :=
    Dist.expect_le (π s) _ 1 zero_le_one (fun a => hr s a)
  have h1 : τ * entropy (π s) ≤ τ * ((Fintype.card A : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hH1 hτ
  have h2 : 0 ≤ τ * entropy (π s) := mul_nonneg hτ hH0
  rw [abs_le] at hrb
  rw [softRbar, abs_le]
  exact ⟨by linarith [hrb.1], by linarith [hrb.2]⟩

/-! ### The discounted series -/

/-- The per-step contribution to the *soft* return: the expected soft reward
collected at time `t`, already discounted. Mirrors `stepReward`. -/
noncomputable def softStepReward (π : Policy S A) (τ : ℝ) (t : ℕ) (s₀ : S) : ℝ :=
  M.γ ^ t * ∑ s, visit M π t s₀ s * softRbar M π τ s

theorem abs_softStepReward_le (π : Policy S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (t : ℕ) (s₀ : S) :
    |softStepReward M π τ t s₀|
      ≤ M.γ ^ t * (1 + τ * ((Fintype.card A : ℝ) - 1)) := by
  unfold softStepReward
  rw [abs_mul, abs_of_nonneg (pow_nonneg hγ₀ t)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ₀ t)
  set R : ℝ := 1 + τ * ((Fintype.card A : ℝ) - 1) with hRdef
  calc |∑ s, visit M π t s₀ s * softRbar M π τ s|
      ≤ ∑ s, |visit M π t s₀ s * softRbar M π τ s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, visit M π t s₀ s * |softRbar M π τ s| := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (visit_nonneg M π t s₀ s)]
    _ ≤ ∑ s, visit M π t s₀ s * R := by
        refine Finset.sum_le_sum fun s _ => ?_
        exact mul_le_mul_of_nonneg_left (abs_softRbar_le M π τ hτ hr s)
          (visit_nonneg M π t s₀ s)
    _ = R := by rw [← Finset.sum_mul, visit_sum_eq_one, one_mul]

theorem summable_softStepReward (π : Policy S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    Summable (fun t => softStepReward M π τ t s₀) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hγ₀ hγ₁).mul_right
      (1 + τ * ((Fintype.card A : ℝ) - 1))) ?_
  intro t
  simpa [Real.norm_eq_abs] using abs_softStepReward_le M π τ hτ hr hγ₀ t s₀

/-- **The discounted-entropy soft value function.**

`Ṽ^π(s₀) = ∑ₜ γᵗ E[r(sₜ,aₜ) + τ·H(π(·|sₜ))]`. -/
noncomputable def VsoftDisc (π : Policy S A) (τ : ℝ) (s₀ : S) : ℝ :=
  ∑' t, softStepReward M π τ t s₀

/-! ### The soft Bellman equation

Same shape as `stepReward_succ` / `Vinf_bellman`: the time-`t+1` contribution is
`γ` times the one-step push of the time-`t` contribution. -/

theorem softStepReward_succ (π : Policy S A) (τ : ℝ) (t : ℕ) (s₀ : S) :
    softStepReward M π τ (t + 1) s₀
      = M.γ * ∑ s', step M π s₀ s' * softStepReward M π τ t s' := by
  unfold softStepReward
  have hswap : ∑ s, visit M π (t + 1) s₀ s * softRbar M π τ s
      = ∑ s', step M π s₀ s' * ∑ s, visit M π t s' s * softRbar M π τ s := by
    calc ∑ s, visit M π (t + 1) s₀ s * softRbar M π τ s
        = ∑ s, (∑ s', step M π s₀ s' * visit M π t s' s) * softRbar M π τ s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [step_visit M π t s₀ s]
      _ = ∑ s, ∑ s', step M π s₀ s' * (visit M π t s' s * softRbar M π τ s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun s' _ => ?_
          ring
      _ = ∑ s', step M π s₀ s' * ∑ s, visit M π t s' s * softRbar M π τ s := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [Finset.mul_sum]
  rw [hswap, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

/-- **Soft Bellman equation.**

`Ṽ(s₀) = r̄(s₀) + τ·H(π(·|s₀)) + γ·∑_{s'} step s₀ s' · Ṽ(s')`.

Split off the `t = 0` term of the `tsum` and apply `softStepReward_succ` to the
tail — the argument of `Vinf_bellman`, verbatim. -/
theorem VsoftDisc_bellman (π : Policy S A) (τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) (s₀ : S) :
    VsoftDisc M π τ s₀
      = softRbar M π τ s₀ + M.γ * ∑ s', step M π s₀ s' * VsoftDisc M π τ s' := by
  unfold VsoftDisc
  rw [Summable.tsum_eq_zero_add (summable_softStepReward M π τ hτ hr hγ₀ hγ₁ s₀)]
  congr 1
  · unfold softStepReward
    simp [visit]
  · calc ∑' t, softStepReward M π τ (t + 1) s₀
        = ∑' t, M.γ * ∑ s', step M π s₀ s' * softStepReward M π τ t s' :=
          tsum_congr fun t => softStepReward_succ M π τ t s₀
      _ = M.γ * ∑' t, ∑ s', step M π s₀ s' * softStepReward M π τ t s' := by
          rw [tsum_mul_left]
      _ = M.γ * ∑ s', step M π s₀ s' * VsoftDisc M π τ s' := by
          congr 1
          rw [Summable.tsum_finsetSum (fun s' _ =>
            (summable_softStepReward M π τ hτ hr hγ₀ hγ₁ s').mul_left _)]
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [tsum_mul_left]
          rfl

omit [DecidableEq S] in
/-- Rewriting the `step`-form expectation into the `∑ₐ π(a|s) ∑_{s'} P(s'|s,a)`
form the frozen goal states it in. -/
theorem step_expect_eq (π : Policy S A) (f : S → ℝ) (s : S) :
    ∑ s', step M π s s' * f s' = ∑ a, (π s) a * ∑ s', (M.P s a) s' * f s' := by
  unfold step
  calc ∑ s', (∑ a, (π s) a * (M.P s a) s') * f s'
      = ∑ s', ∑ a, (π s) a * ((M.P s a) s' * f s') := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = ∑ a, ∑ s', (π s) a * ((M.P s a) s' * f s') := Finset.sum_comm
    _ = ∑ a, (π s) a * ∑ s', (M.P s a) s' * f s' := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- **Frozen goal `Goal.vsoftDisc_exists`.**

The soft Bellman fixed point exists: `VsoftDisc` is a witness. -/
theorem vsoftDisc_exists_proof {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S] [Nonempty A]
    (M : FiniteMDP S A) (τ : ℝ) (hτ : 0 < τ)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1) :
    ∃ V : Policy S A → S → ℝ,
      ∀ π s, V π s = (∑ a, (π s) a * M.r s a) + τ * entropy (π s)
        + M.γ * ∑ a, (π s) a * ∑ s', (M.P s a) s' * V π s' := by
  refine ⟨fun π s => VsoftDisc M π τ s, fun π s => ?_⟩
  rw [← step_expect_eq M π (fun s' => VsoftDisc M π τ s') s]
  exact VsoftDisc_bellman M π τ hτ.le hr hγ₀ hγ₁ s

end Proofs
end PolicyGradient
