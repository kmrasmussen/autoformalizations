/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G7b

/-!
# AKM Theorem 5.1 — asymptotic convergence of softmax policy gradient

Investigation of `Goal.softmax_ascent_converges`. What lands here is the
**analytic half** of the argument; the identification of the limit with `V*`
does not, and the docstring on `stationary_gap` records precisely why.
-/

open Finset Filter

namespace PolicyGradient
namespace Proofs

section AKM51

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]
variable {M : FiniteMDP S A}

/-! ### The abstract summability core

Parameterization-free: a real sequence that increases by at least `κ·g t²` each
step and stays bounded above has `∑ g t² < ∞`, hence `g t → 0`. -/

/-- **Summable gains.** If `v` increases by at least `κ * g t ^ 2` at every step
and is bounded above by `B`, then `∑ g t ^ 2` converges. -/
theorem summable_sq_of_ascent {v g : ℕ → ℝ} {κ B : ℝ} (hκ : 0 < κ)
    (hstep : ∀ t, v t + κ * g t ^ 2 ≤ v (t + 1)) (hB : ∀ t, v t ≤ B) :
    Summable (fun t => g t ^ 2) := by
  have htel : ∀ m : ℕ, ∑ t ∈ range m, κ * g t ^ 2 ≤ v m - v 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
        rw [Finset.sum_range_succ]
        linarith [hstep m, ihm]
  have hpart : ∀ n : ℕ, ∑ t ∈ range n, κ * g t ^ 2 ≤ B - v 0 := fun n => by
    linarith [htel n, hB n]
  have hnn : ∀ t, (0:ℝ) ≤ g t ^ 2 := fun t => sq_nonneg _
  refine summable_of_sum_range_le (c := (B - v 0) / κ) hnn ?_
  intro n
  have h := hpart n
  rw [← Finset.mul_sum] at h
  rw [le_div_iff₀ hκ]
  nlinarith [h]

/-- **Vanishing gradients.** Summability of `g t ^ 2` forces `g t → 0`. -/
theorem tendsto_zero_of_summable_sq {g : ℕ → ℝ}
    (h : Summable (fun t => g t ^ 2)) :
    Tendsto (fun t => g t) atTop (nhds 0) := by
  have h0 : Tendsto (fun t => g t ^ 2) atTop (nhds 0) := h.tendsto_atTop_zero
  have habs : Tendsto (fun t => |g t|) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun t => Real.sqrt (g t ^ 2)) atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Real.sqrt_sq_eq_abs] using hsqrt
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

/-! ### The concrete trajectory

`Goal.vec_ascent_step` — the per-step gain `‖∇‖²(1-γ)³/16` — is being proved
concurrently. It is taken here as the hypothesis `hasc` rather than duplicated,
so these results compose the instant it lands. -/

/-- The per-step gain guaranteed by `Goal.vec_ascent_step`, as a hypothesis. -/
abbrev VecAscent (M : FiniteMDP S A) (F : VecPolicy S A (E S A)) (μ : S) : Prop :=
  ∀ w : E S A, Vinf M (F.toPolicy w) μ
      + ((1 - M.γ) ^ 3 / 16) * ‖gradient (fun u => Vinf M (F.toPolicy u) μ) w‖ ^ 2
    ≤ Vinf M (F.toPolicy
        (w + ((1 - M.γ) ^ 3 / 8) • gradient (fun u => Vinf M (F.toPolicy u) μ) w)) μ

/-- The frozen gradient-ascent recursion, as a hypothesis. -/
abbrev AscentTraj (M : FiniteMDP S A) (F : VecPolicy S A (E S A)) (μ : S)
    (θ : ℕ → E S A) : Prop :=
  ∀ t, θ (t + 1)
    = θ t + ((1 - M.γ) ^ 3 / 8) • gradient (fun u => Vinf M (F.toPolicy u) μ) (θ t)

/-- **The value along the frozen trajectory is monotone.** -/
theorem ascent_monotone_vec (F : VecPolicy S A (E S A)) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A) (htraj : AscentTraj M F μ θ) (hasc : VecAscent M F μ) :
    Monotone (fun t => Vinf M (F.toPolicy (θ t)) μ) := by
  refine monotone_nat_of_le_succ fun t => ?_
  have h := hasc (θ t)
  rw [← htraj t] at h
  have hpos : (0:ℝ) < 1 - M.γ := by linarith
  have hκ : (0:ℝ) ≤ (1 - M.γ) ^ 3 / 16 := by positivity
  nlinarith [h, sq_nonneg ‖gradient (fun u => Vinf M (F.toPolicy u) μ) (θ t)‖]

/-- **The gradient norms along the frozen trajectory are square-summable.**

Monotone value (`vec_ascent_step`) bounded above by `1/(1-γ)`
(`Vinf_le_one_div`) telescopes the gains into a convergent series. -/
theorem summable_sq_grad (F : VecPolicy S A (E S A))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A) (htraj : AscentTraj M F μ θ) (hasc : VecAscent M F μ) :
    Summable (fun t => ‖gradient (fun u => Vinf M (F.toPolicy u) μ) (θ t)‖ ^ 2) := by
  have hpos : (0:ℝ) < 1 - M.γ := by linarith
  refine summable_sq_of_ascent (v := fun t => Vinf M (F.toPolicy (θ t)) μ)
    (κ := (1 - M.γ) ^ 3 / 16) (B := 1 / (1 - M.γ))
    (by positivity) (fun t => ?_)
    (fun t => Vinf_le_one_div M hr hγ₀ hγ₁ (F.toPolicy (θ t)) μ)
  have h := hasc (θ t)
  rw [← htraj t] at h
  exact h

/-- **The gradient vanishes along the frozen trajectory.** -/
theorem tendsto_norm_grad_zero (F : VecPolicy S A (E S A))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A) (htraj : AscentTraj M F μ θ) (hasc : VecAscent M F μ) :
    Tendsto (fun t => ‖gradient (fun u => Vinf M (F.toPolicy u) μ) (θ t)‖)
      atTop (nhds 0) :=
  tendsto_zero_of_summable_sq (summable_sq_grad (M := M) F hr hγ₀ hγ₁ μ θ htraj hasc)

/-- **The value converges to some limit `L ≤ V*(μ)`.**

`AKM.ascent_converges` transported to the vector parameterization: monotone and
bounded above by `Vstar`. **Identifying `L = Vstar M μ` is exactly the frozen
goal `softmax_ascent_converges`, and is not supplied here** — see
`stationary_gap`. -/
theorem exists_limit_le_vstar (F : VecPolicy S A (E S A))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A) (htraj : AscentTraj M F μ θ) (hasc : VecAscent M F μ) :
    ∃ L : ℝ, L ≤ Vstar M μ ∧
      Tendsto (fun t => Vinf M (F.toPolicy (θ t)) μ) atTop (nhds L) := by
  have hmono : Monotone (fun t => Vinf M (F.toPolicy (θ t)) μ) :=
    ascent_monotone_vec (M := M) F hγ₁ μ θ htraj hasc
  have hbdd : ∀ t, Vinf M (F.toPolicy (θ t)) μ ≤ Vstar M μ :=
    fun t => vstar_upper_proof M hr hγ₀ hγ₁ _ μ
  have hbdd' : BddAbove (Set.range fun t => Vinf M (F.toPolicy (θ t)) μ) :=
    ⟨Vstar M μ, by rintro x ⟨t, rfl⟩; exact hbdd t⟩
  exact ⟨_, ciSup_le hbdd, tendsto_atTop_ciSup hmono hbdd'⟩

/-! ### Where the argument stops

The four results above are the whole *analytic* half of AKM Theorem 5.1, and
they are unconditional given `vec_ascent_step`. What they do **not** give is
`L = Vstar M μ`. This section pins down, in checked Lean, exactly which one
extra fact closes the gap — and why nothing in this repo supplies it. -/

/-- **The exact missing ingredient, isolated.**

Everything except `hclosed` is discharged above. `hclosed` says the limit value
is *not* strictly suboptimal — equivalently, that no strictly-suboptimal value
is a limit of the ascent trajectory. Given it, the frozen goal follows in three
lines.

This is deliberately a reduction, not a proof: it converts
`softmax_ascent_converges` into a single self-contained statement about limit
points, so the remaining work has a name and a type. -/
theorem tendsto_vstar_of_limit_optimal (F : VecPolicy S A (E S A))
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : S) (θ : ℕ → E S A) (htraj : AscentTraj M F μ θ) (hasc : VecAscent M F μ)
    (hclosed : ∀ L : ℝ,
      Tendsto (fun t => Vinf M (F.toPolicy (θ t)) μ) atTop (nhds L) →
      Vstar M μ ≤ L) :
    Tendsto (fun t => Vinf M (F.toPolicy (θ t)) μ) atTop (nhds (Vstar M μ)) := by
  obtain ⟨L, hLle, hL⟩ := exists_limit_le_vstar (M := M) F hr hγ₀ hγ₁ μ θ htraj hasc
  have : L = Vstar M μ := le_antisymm hLle (hclosed L hL)
  exact this ▸ hL

/-! ### The obstruction, precisely

`hclosed` is not reachable from what this repo has, and the reason is
structural rather than a matter of missing effort.

**1. The Łojasiewicz route is closed off by the start state being a point.**
The repo's route from a small gradient to small suboptimality is
`Proofs.g1_lojasiewicz_of_greedy`, which factors through `mismatchCoeff` and
therefore through `Goal.mismatch_bound`. Both carry `hμ : ∀ s, 0 < μ s`, and
that hypothesis is **not decorative**: `Proofs.mismatch_bound_is_false` is a
machine-checked refutation of `mismatch_bound` without it. The frozen goal
starts from a single state `μ : S`, i.e. the Dirac `pointMass μ`, which is the
maximally-degenerate violation of full support — every state other than `μ` has
`μ s = 0`. So the entire `mismatchCoeff` machinery is inapplicable here *as a
matter of the frozen statement's own shape*, not merely unproved.

The suboptimality `Vstar M μ - Vinf M π μ` is nonetheless still controlled by
occupancy-weighted advantages via `Proofs.perfDiffInf`, whose weights are
`dinf M πstar μ s` — the occupancy of the *comparator*, which is positive
exactly on the states `πstar` reaches from `μ`. That is the correct replacement
for full support, and it is what a proof would have to use. Nothing in the repo
converts `dinf`-weights into `μ`-weights without `hμ`, and by
`mismatch_bound_is_false` nothing can.

**2. Vanishing gradients do not pin the advantage, only a product.**
`Proofs.sum_abs_adv_le_norm` gives, at every `θ`,

  `∑ s, |d^π_μ(s) · π(a*(s)|s) · A^π(s, a*(s))| ≤ √|S| · ‖∇ V‖`,

so `tendsto_norm_grad_zero` forces each **product**
`d^π_μ(s) · π_t(a*|s) · A^{π_t}(s,a*)` to zero. Concluding `A → 0` needs the
`π_t(a*|s)` factor bounded below — which is `Goal.g9_c_positive`, and `g9` is
proved *by citing this very theorem*. The two goals are mutually reducing; the
cycle has to be broken by an argument that is asymptotic in policy space.

Compactness cannot break it. `‖θ t‖ → ∞` along ascent, so the trajectory has no
convergent subsequence in parameter space; and while the closure of the policy
simplex *is* compact, the limit policy generally sits on its boundary, where
`π(a*|s) = 0` and the gradient vanishes for the wrong reason — the softmax
parameterization has genuine stationary points at infinity. `m(t) ≥ m(0)` fails
in 66/400 random MDPs, so monotonicity of `π_t(a*|s)` is unavailable too.

**3. What AKM actually do, and what it would cost.**
AKM's Theorem 5.1 argues in policy space: they show the limit policy exists
along a subsequence (Bolzano–Weierstrass in the compact simplex `Δ(A)^S`, not in
parameter space), that its value equals `L` by continuity of `π ↦ V^π`, and then
that any limit point of softmax ascent satisfies the **greedy condition** — for
every `s` and every `a` in the limit policy's support, `A(s,a) = 0` — from which
`Proofs.optimal_support_greedy_proof` and `vstar_eq_greedy` give `L = V*`. The
step with real content is that the limit policy is greedy, and it requires a
separate argument that suboptimal actions' logits are driven down faster than
optimal ones' — a per-coordinate asymptotic estimate on `θ t` itself, not on
`‖∇V(θ t)‖`. Nothing of that kind exists anywhere in this repo, and Mathlib has
no off-the-shelf form of it.

The three new goals this suggests are named in the agent report. -/

end AKM51

end Proofs
end PolicyGradient
