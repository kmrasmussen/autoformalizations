/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Theorem
import PolicyGradient.Meta.Paper

/-!
# The performance difference lemma, finite horizon

For two policies `π` and `π'`,

  V_m^π(s₀) - V_m^π'(s₀)
    = ∑_{k<m} γ^k ∑_s visit^π k s₀ s · ∑_a π(a|s) · A^π'_{m-1-k}(s,a)

where `A^π'_j(s,a) = Q^π'_j(s,a) - V^π'_{j+1}(s)` is the advantage.

## Notes

Kakade & Langford (2002); Agarwal, Kakade, Lee & Mahajan (JMLR 2021) Lemma 3.2.
The infinite-horizon statement carries a `1/(1-γ)` because it uses the
*normalized* occupancy measure. Our `visit` is unnormalized, so that factor is
absent and the discounting appears as the explicit `∑_{k<m} γ^k`.

The asymmetry is the whole content: the advantage is that of `π'`, but it is
averaged under `π`'s state visitation.

Index convention: `Q_j` pairs with `V_(j+1)`, since `V_(j+1) s = ∑ₐ π(a|s) Q_j s a`.
Verified numerically (`pdl_check.py`) before proving.

## Reuse

This file shares the entire vocabulary of the policy gradient development —
`V`, `Q`, `visit`, `step`, and the `∑ₖ γᵏ ∑ₛ visit k` weighting with the same
`m-1-k` indexing — and its induction turns on `step_visit`, the same
Chapman-Kolmogorov lemma that `step_pgSum` needs.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
variable (M : FiniteMDP S A)

/-- The advantage of policy `π` at horizon `j`: how much better taking `a` now is
than acting under `π`, when `j` further steps remain after the action. -/
noncomputable def adv (π : Policy S A) (j : ℕ) (s : S) (a : A) : ℝ :=
  Q M π j s a - V M π (j + 1) s

/-- The expected advantage of `π'` under `π`'s action distribution at `s`. -/
noncomputable def advGap (π π' : Policy S A) (j : ℕ) (s : S) : ℝ :=
  ∑ a, (π s) a * adv M π' j s a

/-- The visitation-weighted sum of advantage gaps — the right-hand side of the
performance difference lemma. Note the shape is exactly `pgSum`'s, with
`advGap` in place of `localTerm`. -/
noncomputable def pdSum (π π' : Policy S A) (m : ℕ) (s₀ : S) : ℝ :=
  ∑ k ∈ range m, M.γ ^ k * ∑ s, visit M π k s₀ s * advGap M π π' (m - 1 - k) s


/-- One-step lookahead: averaging over the policy-induced transition equals
averaging over actions, then next states. Pure `Finset.sum_comm`, but stated
separately so the main proof need not steer a rewrite through a
partially-normalized goal. -/
theorem step_expect (π ρ : Policy S A) (m : ℕ) (s : S) :
    ∑ s', step M π s s' * V M ρ m s'
      = ∑ a, (π s) a * ∑ s', (M.P s a) s' * V M ρ m s' := by
  unfold step
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

/-- The telescoping step: one step of `π` against one step of `π'`.

`V^π_(m+1) s - V^π'_(m+1) s = advGap m s + γ · ∑_{s'} step^π s s' · (V^π_m s' - V^π'_m s')`

The `Q^π'` terms cancel against the definition of `advGap`; what makes the
bookkeeping work is that `advGap` subtracts `V^π'_(m+1) s` once per action and
the policy sums to one. Verified numerically (`pdl_step.py`, 4.4e-16). -/
theorem perfDiff_succ (π π' : Policy S A) (m : ℕ) (s : S) :
    V M π (m + 1) s - V M π' (m + 1) s
      = advGap M π π' m s
        + M.γ * ∑ s', step M π s s' * (V M π m s' - V M π' m s') := by
  have hone : ∑ a, (π s) a = 1 := (π s).sum_eq_one
  have hgap : advGap M π π' m s
      = (∑ a, (π s) a * Q M π' m s a) - V M π' (m + 1) s := by
    unfold advGap adv
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hone, one_mul]
  have hsplit : (∑ s', step M π s s' * (V M π m s' - V M π' m s'))
      = (∑ s', step M π s s' * V M π m s') - ∑ s', step M π s s' * V M π' m s' := by
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hgap, hsplit, step_expect M π π m s, step_expect M π π' m s]
  rw [V_succ M π m s]
  unfold Q
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, sub_mul,
             Finset.sum_add_distrib, mul_add, add_mul]
  -- Both sides are the same sum up to order/association inside the binders.
  -- `ring` cannot see under `∑`, so normalize products with AC-lemmas first.
  simp only [mul_comm, mul_assoc, mul_left_comm]
  ring

/-- Weighting `pdSum` by one transition advances every visitation index by one.

Exactly `step_pgSum`'s statement with `advGap` in place of `localTerm`, and it
turns on the same `step_visit` (Chapman-Kolmogorov) lemma. -/
theorem step_pdSum (π π' : Policy S A) (m : ℕ) (s₀ : S) :
    ∑ s', step M π s₀ s' * pdSum M π π' m s'
      = ∑ k ∈ range m, M.γ ^ k *
          ∑ s, visit M π (k + 1) s₀ s * advGap M π π' (m - 1 - k) s := by
  unfold pdSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  calc ∑ s', step M π s₀ s' * (M.γ ^ k *
          (visit M π k s' s * advGap M π π' (m - 1 - k) s))
      = (∑ s', step M π s₀ s' * visit M π k s' s) *
          (M.γ ^ k * advGap M π π' (m - 1 - k) s) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
    _ = M.γ ^ k * (visit M π (k + 1) s₀ s * advGap M π π' (m - 1 - k) s) := by
        rw [step_visit M π k s₀ s]; ring

/-- **Performance difference lemma** (finite horizon).

`V_m^π(s₀) - V_m^π'(s₀) = ∑_{k<m} γ^k ∑_s visit^π k s₀ s · advGap_(m-1-k) s`

VERBATIM, Kakade & Langford (ICML 2002), Lemma 6.1 — the paper never calls it
"the performance difference lemma"; it introduces it as "The following lemma is
useful:":

> **Lemma 6.1.** *For any policies* `π̃` *and* `π` *and any starting state
> distribution* `μ`,
> ```
> η_μ(π̃) − η_μ(π)  =  (1/(1−γ)) E_{(a,s) ~ π̃ d_{π̃,μ}} [ A_π(s,a) ]
> ```

with that paper's own definitions, eq. (2.1) and §2:

> It is convenient to define the **γ-discounted future state distribution** (as
> in [8]) for a starting state distribution `μ` as
> ```
> d_{π,μ}(s) ≡ (1 − γ) ∑_{t=0}^∞ γ^t Pr(s_t = s; π, μ)          (2.1)
> ```
> where the `1 − γ` is necessary for normalization.

> `V_π(s) ≡ (1 − γ) E[ ∑_{t=0}^∞ γ^t R(s_t, a_t) | π, s ]`
>
> Note that we are using *normalized* values so `V_π(s) ∈ [0, R]`. […]
> `Q_π(s,a) ≡ (1 − γ) R(s,a) + γ E_{s' ~ P(s'; s,a)}[V_π(s')]`
> […] we define the **advantage** as `A_π(s,a) ≡ Q_π(s,a) − V_π(s)`

and, in the *unnormalized*-value convention this repo actually uses,
VERBATIM, AKM (arXiv:1908.00261) Lemma 3.2 = JMLR 22(98) 2021 **Lemma 2**
(the two are word-for-word identical apart from the number):

> **Lemma 2 (The performance difference lemma (Kakade and Langford, 2002))**
> *For all policies* `π, π′` *and states* `s₀`,
> ```
> V^π(s₀) − V^{π′}(s₀) = (1/(1−γ)) E_{s~d^π_{s₀}} E_{a~π(·|s)} [ A^{π′}(s,a) ]
> ```

⚠ **The `@[paper]` tag says `"Kakade2002" "Performance Difference Lemma"`, but
`Lemma 3.2` is the arXiv number and `Lemma 2` the JMLR one — the docstring
below previously said "JMLR 2021 Lemma 3.2", which is neither.** JMLR renumbered
flat for publication. Minor, but it is the kind of thing this audit is for.

**How the Lean statement departs from the quotes.**

1. **Orientation — matches AKM, and the two papers differ.** Here `advGap π π' j s
   = ∑_a (π s) a * adv M π' j s a`: the **unprimed `π`** supplies both the state
   visitation (`visit M π`) and the action distribution, the **primed `π'`**
   supplies the advantage. That is exactly AKM's Lemma 2. Kakade–Langford's
   Lemma 6.1 has the *reverse* naming — there `π̃` (the new policy) carries the
   occupancy and actions while `π` (the baseline) carries the advantage — so the
   content agrees but the symbols are swapped. Worth stating explicitly, since
   getting this backwards is the classic error with this lemma.
2. **No `1/(1−γ)`, and that is CORRECT here.** Both quotes carry a `1/(1−γ)`
   *because both normalize* `d` by `(1−γ)` in their definitions — the factor and
   the normalization cancel. This repo's `pdSum` uses `∑_k γ^k · visit`, the
   **unnormalized** occupancy, so no `1/(1−γ)` belongs on the right. The
   statement is right; it is the same identity in the unnormalized convention.
   (Contrast `mismatchCoeff`, where the missing `(1−γ)` is *not* compensated —
   see the defect recorded on `mei_theorem4` in `Goal.lean`.)
3. **Finite horizon, with a horizon-indexed advantage.** Both papers state an
   infinite-horizon identity. `pdSum` truncates at `m` and pairs the `k`-th
   visitation term with `advGap (m-1-k)`, i.e. the advantage at the number of
   steps that actually remain — the same correction `pgSum` carries in
   `Theorem.lean`. As `m → ∞` with `k` fixed this recovers the quoted form.
4. **Single start state, not a distribution.** `s₀ : S` rather than `μ ∈ Δ(S)`.
   AKM's Lemma 2 is also stated at a state `s₀`; Kakade–Langford state it at a
   distribution `μ`. Averaging over `μ` is immediate from linearity.
5. **Reward normalization.** Kakade–Langford put `(1−γ)` inside `V` and `Q` too
   (`V_π(s) ∈ [0,R]`); AKM and this repo do not. This repo follows AKM.

Verdict: **MATCHES** AKM Lemma 2 / arXiv Lemma 3.2 exactly, at finite horizon,
in the unnormalized convention, with the orientation the papers require.

The advantage is that of `π'`, but averaged under `π`'s state visitation --
that asymmetry is the whole content of the lemma. -/
@[paper "Kakade2002" "Performance Difference Lemma"]
theorem performance_difference (π π' : Policy S A) (m : ℕ) (s₀ : S) :
    V M π m s₀ - V M π' m s₀ = pdSum M π π' m s₀ := by
  induction m generalizing s₀ with
  | zero => simp [pdSum]
  | succ m ih =>
    rw [perfDiff_succ]
    have hIH : ∑ s', step M π s₀ s' * (V M π m s' - V M π' m s')
        = ∑ s', step M π s₀ s' * pdSum M π π' m s' := by
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [ih s']
    rw [hIH, step_pdSum]
    unfold pdSum
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hidx : m + 1 - 1 - (j + 1) = m - 1 - j := by omega
      rw [hidx, pow_succ]
      ring
    · simp

/-!
### Advantage identities

The advantage of a policy against itself averages to zero — the identity that
makes the policy gradient a *centered* quantity, and the engine of the
performance difference lemma.
-/

/-- `∑ₐ π(a|s) · A^π_j(s,a) = 0`: a policy has no advantage over itself. -/
theorem advGap_self (π : Policy S A) (j : ℕ) (s : S) :
    advGap M π π j s = 0 := by
  unfold advGap adv
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (π s).sum_eq_one, one_mul]
  rw [← V_succ]
  ring

/-- Consequently the performance difference of a policy with itself is zero. -/
theorem pdSum_self (π : Policy S A) (m : ℕ) (s₀ : S) :
    pdSum M π π m s₀ = 0 := by
  unfold pdSum
  refine Finset.sum_eq_zero fun k _ => ?_
  have : ∀ s, visit M π k s₀ s * advGap M π π (m - 1 - k) s = 0 := by
    intro s; rw [advGap_self]; ring
  rw [Finset.sum_congr rfl (fun s _ => this s)]
  simp

end PolicyGradient
