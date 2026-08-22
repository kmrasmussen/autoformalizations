/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Chain
import PolicyGradient.Meta.Paper

/-!
# The policy gradient theorem, finite horizon

Main results:

* `hasDerivAt_V` — the recursive form: `dV_{m+1}` splits into a term where the
  derivative hits the policy at the current state, plus a discounted expectation
  of `dV_m` at the next state. This is the honest version of the step that
  Sutton et al. (NIPS 1999) dispatch as "after several steps of unrolling".
* `policy_gradient` — the closed form, with the derivative of the state
  visitation *absent*. That absence is the content of the theorem.

Both were checked numerically against finite differences before being proved
(`verify_statement.py`, `pg_induction.py`): 18/18 cases, worst error ~2e-10.
Lean can only tell us the proof follows from the definitions; the numerics are
what tell us the definitions are the right ones.
-/

open Finset

namespace PolicyGradient

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]

/-- A differentiable family of policies. -/
structure DiffPolicy (S A : Type*) [Fintype A] where
  /-- The policy at parameter `θ`. -/
  toPolicy : ℝ → Policy S A
  /-- The pointwise derivative `∂π(a|s)/∂θ`. -/
  dπ : ℝ → S → A → ℝ
  /-- `dπ` really is the derivative. -/
  hasDeriv : ∀ θ s a, HasDerivAt (fun t => (toPolicy t s) a) (dπ θ s a) θ

/-- A twice-differentiable policy family: carries the second derivative of the
action probabilities as well as the first.

Needed for the smoothness constant, which is a bound on `∂²V/∂θ²`. -/
structure C2Policy (S A : Type*) [Fintype A] extends DiffPolicy S A where
  /-- The pointwise second derivative `∂²π(a|s)/∂θ²`. -/
  d2π : ℝ → S → A → ℝ
  /-- `d2π` really is the derivative of `dπ`. -/
  hasDeriv2 : ∀ θ s a, HasDerivAt (fun t => dπ t s a) (d2π θ s a) θ

variable (M : FiniteMDP S A) (PF : DiffPolicy S A) (θ : ℝ)

/-- The "local" term: derivative hitting the policy at state `s`, with `m` steps
of value remaining after the action. -/
noncomputable def localTerm (m : ℕ) (s : S) : ℝ :=
  ∑ a, PF.dπ θ s a * Q M (PF.toPolicy θ) m s a

/-!
### The recursive form

`dV_{m+1}(s₀) = localTerm m s₀ + γ · ∑_{s'} step s₀ s' · dV_m(s')`

Proof: product rule on `V_{m+1} = ∑ₐ π(a|s₀) · Q_m(s₀,a)`. The first factor
gives `localTerm`; the second uses that `P` and `r` do not depend on `θ`, so
`dQ_m/dθ = γ ∑_{s'} P(s'|s₀,a) · dV_m(s')`.
-/

/-- The claimed derivative of `V`, defined by the same recursion as `V` itself.
Verified numerically against finite differences (`pg_induction.py`, horizons 0-5,
worst error 2.9e-10) before being proved. -/
noncomputable def dV (m : ℕ) (s : S) : ℝ :=
  match m with
  | 0 => 0
  | m + 1 => localTerm M PF θ m s
      + M.γ * ∑ s', step M (PF.toPolicy θ) s s' * dV m s'

@[simp] theorem dV_zero (s : S) : dV M PF θ 0 s = 0 := rfl

theorem dV_succ (m : ℕ) (s : S) :
    dV M PF θ (m + 1) s
      = localTerm M PF θ m s + M.γ * ∑ s', step M (PF.toPolicy θ) s s' * dV M PF θ m s' :=
  rfl

/-- `Q` is differentiable in `θ`, with `P` and `r` constant in `θ`. -/
theorem hasDerivAt_Q (m : ℕ) (s : S) (a : A)
    (ih : ∀ s', HasDerivAt (fun t => V M (PF.toPolicy t) m s') (dV M PF θ m s') θ) :
    HasDerivAt (fun t => Q M (PF.toPolicy t) m s a)
      (M.γ * ∑ s', (M.P s a) s' * dV M PF θ m s') θ := by
  unfold Q
  have hsum : HasDerivAt
      (fun t => ∑ s', (M.P s a) s' * V M (PF.toPolicy t) m s')
      (∑ s', (M.P s a) s' * dV M PF θ m s') θ := by
    exact HasDerivAt.fun_sum (fun s' _ => ((ih s').const_mul _))
  simpa using (hsum.const_mul M.γ).const_add (M.r s a)

/-- The derivative of the finite-horizon value function, in recursive form.

This is the honest version of the step Sutton et al. dispatch as "after several
steps of unrolling": product rule on `V_{m+1} = ∑ₐ π(a|s)·Q_m(s,a)`, where the
first factor yields `localTerm` and the second is handled by the IH. -/
theorem hasDerivAt_V (m : ℕ) (s : S) :
    HasDerivAt (fun t => V M (PF.toPolicy t) m s) (dV M PF θ m s) θ := by
  induction m generalizing s with
  | zero => simpa [V] using hasDerivAt_const θ (0 : ℝ)
  | succ m ih =>
    rw [dV_succ]
    have hV : ∀ t, V M (PF.toPolicy t) (m + 1) s
        = ∑ a, (PF.toPolicy t s) a * Q M (PF.toPolicy t) m s a := fun t => rfl
    simp only [hV]
    -- product rule termwise: d(π·Q) = dπ·Q + π·dQ
    have hterm : ∀ a ∈ (univ : Finset A),
        HasDerivAt (fun t => (PF.toPolicy t s) a * Q M (PF.toPolicy t) m s a)
          (PF.dπ θ s a * Q M (PF.toPolicy θ) m s a
            + (PF.toPolicy θ s) a * (M.γ * ∑ s', (M.P s a) s' * dV M PF θ m s')) θ := by
      intro a _
      exact (PF.hasDeriv θ s a).mul (hasDerivAt_Q M PF θ m s a (fun s' => ih s'))
    have hsum := HasDerivAt.fun_sum hterm
    -- reconcile the derivative value: localTerm + γ·∑ step·dV = ∑ₐ (dπ·Q + π·γ·∑ P·dV)
    have hval : localTerm M PF θ m s
          + M.γ * ∑ s', step M (PF.toPolicy θ) s s' * dV M PF θ m s'
        = ∑ a, (PF.dπ θ s a * Q M (PF.toPolicy θ) m s a
            + (PF.toPolicy θ s) a * (M.γ * ∑ s', (M.P s a) s' * dV M PF θ m s')) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · -- ∑ s', γ*((∑ a, π a * P a s') * dV s') = ∑ a, π a * (γ * ∑ s', P a s' * dV s')
        -- expand both sides to the SAME double sum, then swap the order.
        unfold step
        have lhs_eq : M.γ * (∑ s', (∑ a, (PF.toPolicy θ s) a * (M.P s a) s') * dV M PF θ m s')
            = ∑ s', ∑ a, M.γ * ((PF.toPolicy θ s) a * ((M.P s a) s' * dV M PF θ m s')) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s' _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
        have rhs_eq : (∑ a, (PF.toPolicy θ s) a * (M.γ * ∑ s', (M.P s a) s' * dV M PF θ m s'))
            = ∑ a, ∑ s', M.γ * ((PF.toPolicy θ s) a * ((M.P s a) s' * dV M PF θ m s')) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s' _ => ?_
          ring
        rw [lhs_eq, rhs_eq, Finset.sum_comm]
    rw [hval]
    exact hsum

/-!
### The closed form (main theorem)
-/

/-- The visitation-weighted sum: `∑_{k<m} γ^k ∑_s visit k s₀ s · localTerm_{m-1-k} s`.

This is what the literature abbreviates as `∑_s d^π(s) ∑_a ∇π(a|s) Q^π(s,a)`.
Index bookkeeping (`m-1-k`) verified numerically to machine epsilon
(`pg_closed.py`, 1.1e-16) before proving. -/
noncomputable def pgSum (m : ℕ) (s₀ : S) : ℝ :=
  ∑ k ∈ range m, M.γ ^ k * ∑ s, visit M (PF.toPolicy θ) k s₀ s * localTerm M PF θ (m - 1 - k) s

/-- Key reindexing lemma: pushing one step of the recursion through `pgSum`.

`∑_{s'} step s₀ s' · pgSum m s'  =  ∑_{k<m} γ^k ∑_s visit (k+1) s₀ s · localTerm_{m-1-k} s`

i.e. weighting by one transition advances every visitation index by one. -/
theorem step_pgSum (m : ℕ) (s₀ : S) :
    ∑ s', step M (PF.toPolicy θ) s₀ s' * pgSum M PF θ m s'
      = ∑ k ∈ range m, M.γ ^ k *
          ∑ s, visit M (PF.toPolicy θ) (k + 1) s₀ s * localTerm M PF θ (m - 1 - k) s := by
  unfold pgSum
  -- Flatten LHS to ∑ s', ∑ k, ∑ s  then swap to ∑ k, ∑ s', ∑ s
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- goal: ∑ s', ∑ s, step s₀ s' * (γ^k * (visit k s' s * lt s))
  --     = γ^k * ∑ s, visit (k+1) s₀ s * lt s
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  calc ∑ s', step M (PF.toPolicy θ) s₀ s' * (M.γ ^ k *
          (visit M (PF.toPolicy θ) k s' s * localTerm M PF θ (m - 1 - k) s))
      = (∑ s', step M (PF.toPolicy θ) s₀ s' * visit M (PF.toPolicy θ) k s' s) *
          (M.γ ^ k * localTerm M PF θ (m - 1 - k) s) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
    _ = M.γ ^ k * (visit M (PF.toPolicy θ) (k + 1) s₀ s * localTerm M PF θ (m - 1 - k) s) := by
        rw [step_visit M (PF.toPolicy θ) k s₀ s]; ring

/-- **Policy gradient theorem** (finite horizon).

VERBATIM, Sutton, McAllester, Singh & Mansour (NIPS 12, 1999) Theorem 1:

> **Theorem 1 (Policy Gradient).** *For any MDP, in either the average-reward or
> start-state formulations,*
> ```
> ∂ρ/∂θ  =  ∑_s d^π(s) ∑_a (∂π(s,a)/∂θ) Q^π(s,a)          (2)
> ```

with, in the start-state formulation (the one this repo uses), the paper's own
definitions immediately preceding it:

> In this formulation, we define `d^π(s)` as a discounted weighting of states
> encountered starting at `s₀` and then following `π`:
> ```
> d^π(s) = ∑_{t=0}^∞ γ^t Pr{s_t = s | s₀, π}
> ```
> ```
> ρ(π) = E{ ∑_{t=1}^∞ γ^{t−1} r_t | s₀, π }
> Q^π(s,a) = E{ ∑_{k=1}^∞ γ^{k−1} r_{t+k} | s_t = s, a_t = a, π }
> ```

and, on what the theorem is *for*:

> the key aspect of both expressions for the gradient is that their are no terms
> of the form `∂d^π(s)/∂θ`: the effect of policy changes on the distribution of
> states does not appear.

("their are" is the paper's own typo, reproduced as printed.)

**How the Lean statement departs from the quote, and why.**

1. **Finite horizon.** Sutton's `d^π` is an infinite sum `∑_{t=0}^∞ γ^t Pr{·}`
   and his `Q^π` is a single infinite-horizon function. `pgSum` truncates at `m`
   and — this is the substantive difference — carries a *horizon-indexed* `Q`:
   the `k`-th visitation term is paired with `localTerm (m-1-k)`, i.e. with `Q`
   at the number of steps that actually remain. As `m → ∞` with `k` fixed,
   `m-1-k → ∞` and the index dependence disappears, recovering (2). The
   finite-horizon form is not a weakening: it is what is true at each `m`, and
   the naive truncation of (2) — a single fixed `Q_m` under every visitation
   term — is false.
2. **`d^π` is unnormalized, and so is `pgSum`.** The paper's `d^π` sums to
   `1/(1−γ)`, not `1`, and (2) carries no `(1−γ)` factor. `pgSum` matches:
   `∑_k γ^k ∑_s visit k s₀ s · (…)`, same `γ^k` weighting, no normalization.
   Later texts writing (2) with a `(1−γ)` use the *normalized* occupancy; this
   repo follows the 1999 convention.
3. **Scalar parameter.** `θ : ℝ` here, so `∂π/∂θ` is `PF.dπ` and the conclusion
   is a `HasDerivAt` rather than a gradient identity. Sutton states (2) for a
   vector `θ` componentwise, which is the same content one coordinate at a time.
4. **Average-reward formulation not covered.** Sutton's "in either the
   average-reward or start-state formulations" is a disjunction; only the
   start-state branch is formalized. The average-reward branch rests on a
   stationary distribution "which we assume exists and is independent of `s₀`
   for all policies" — a hypothesis with no counterpart here.

Verdict: **MATCHES** the paper on the start-state branch, at finite horizon,
with the unnormalized `d^π` convention.

Note what is *not* on the right-hand side: any derivative of `visit`. The state
visitation depends on `θ`, yet its derivative cancels. That cancellation is the
content of the theorem, and here it is a consequence of the induction rather
than an assumption. -/
@[paper "Sutton1999" "Policy Gradient Theorem"]
theorem policy_gradient (m : ℕ) (s₀ : S) :
    HasDerivAt (fun t => V M (PF.toPolicy t) m s₀) (pgSum M PF θ m s₀) θ := by
  have key : ∀ m s, dV M PF θ m s = pgSum M PF θ m s := by
    intro m
    induction m with
    | zero => intro s; simp [dV, pgSum]
    | succ m ih =>
      intro s
      rw [dV_succ]
      -- IH lets us replace dV m by pgSum m inside the discounted expectation
      have hIH : ∑ s', step M (PF.toPolicy θ) s s' * dV M PF θ m s'
          = ∑ s', step M (PF.toPolicy θ) s s' * pgSum M PF θ m s' := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [ih s']
      rw [hIH, step_pgSum]
      -- now both sides are sums over range (m+1); split off k = 0
      unfold pgSum
      -- sum_range_succ' : ∑_{i<n+1} f i = (∑_{i<n} f (i+1)) + f 0
      rw [Finset.sum_range_succ']
      -- target: localTerm m s + γ * ∑ k<m, γ^k ∑ s, visit (k+1) s s * lt
      --       = (∑ i<m, γ^(i+1) ∑ s, visit (i+1) s s * lt) + γ^0 ∑ s, visit 0 s s * lt
      rw [add_comm]
      congr 1
      · -- tail: γ * ∑ γ^i (...) = ∑ γ^(i+1) (...), and (m+1)-1-(i+1) = m-1-i
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hidx : m + 1 - 1 - (j + 1) = m - 1 - j := by omega
        rw [hidx, pow_succ]
        ring
      · -- k = 0: γ^0 * ∑ s', visit 0 s s' * lt s' = localTerm m s
        simp
  rw [← key]
  exact hasDerivAt_V M PF θ m s₀

end PolicyGradient
