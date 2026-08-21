/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Value

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

/-- One-step state-transition matrix induced by `π`. -/
noncomputable def step (M : FiniteMDP S A) (π : Policy S A) (s s' : S) : ℝ :=
  ∑ a, (π s) a * (M.P s a) s'

/-- `visit M π k s₀ s = Pr(s_k = s | s₀)` under `π`. -/
noncomputable def visit (M : FiniteMDP S A) (π : Policy S A) : ℕ → S → S → ℝ
  | 0, s₀, s => if s = s₀ then 1 else 0
  | k + 1, s₀, s => ∑ s', visit M π k s₀ s' * step M π s' s

@[simp] theorem visit_zero (M : FiniteMDP S A) (π : Policy S A) (s₀ s : S) :
    visit M π 0 s₀ s = if s = s₀ then 1 else 0 := rfl

theorem visit_succ (M : FiniteMDP S A) (π : Policy S A) (k : ℕ) (s₀ s : S) :
    visit M π (k + 1) s₀ s = ∑ s', visit M π k s₀ s' * step M π s' s := rfl

/-- A differentiable family of policies. -/
structure DiffPolicy (S A : Type*) [Fintype A] where
  /-- The policy at parameter `θ`. -/
  toPolicy : ℝ → Policy S A
  /-- The pointwise derivative `∂π(a|s)/∂θ`. -/
  dπ : ℝ → S → A → ℝ
  /-- `dπ` really is the derivative. -/
  hasDeriv : ∀ θ s a, HasDerivAt (fun t => (toPolicy t s) a) (dπ θ s a) θ

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

/-- Chapman-Kolmogorov: taking the step first or last gives the same visitation.

`∑ s', step s₀ s' * visit k s' s = visit (k+1) s₀ s = ∑ s', visit k s₀ s' * step s' s`

The right-hand equality is `visit_succ` by definition; the left-hand one is the
content of this lemma, proved by induction on `k`. Verified numerically
(`check_step_pgsum.py`) before proving. -/
theorem step_visit (k : ℕ) (s₀ s : S) :
    ∑ s', step M (PF.toPolicy θ) s₀ s' * visit M (PF.toPolicy θ) k s' s
      = visit M (PF.toPolicy θ) (k + 1) s₀ s := by
  induction k generalizing s₀ s with
  | zero =>
    -- both sides collapse to `step s₀ s`
    simp [visit_zero, visit_succ]
  | succ k ih =>
    -- LHS: ∑ s', step s₀ s' * ∑ t, visit k s' t * step t s
    -- RHS: ∑ s', (∑ t, visit k s₀ t * step t s') * step s' s
    -- Flatten both to double sums, swap on the left, then apply ih.
    simp only [visit_succ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have := ih s₀ t
    calc ∑ s', step M (PF.toPolicy θ) s₀ s' * (visit M (PF.toPolicy θ) k s' t
              * step M (PF.toPolicy θ) t s)
        = (∑ s', step M (PF.toPolicy θ) s₀ s' * visit M (PF.toPolicy θ) k s' t)
              * step M (PF.toPolicy θ) t s := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun s' _ => ?_; ring
      _ = visit M (PF.toPolicy θ) (k + 1) s₀ t * step M (PF.toPolicy θ) t s := by
          rw [this]
      _ = ∑ s', visit M (PF.toPolicy θ) k s₀ s' * step M (PF.toPolicy θ) s' t
              * step M (PF.toPolicy θ) t s := by
          rw [visit_succ, Finset.sum_mul]

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
        rw [step_visit M PF θ k s₀ s]; ring

/-- **Policy gradient theorem** (finite horizon).

Note what is *not* on the right-hand side: any derivative of `visit`. The state
visitation depends on `θ`, yet its derivative cancels. That cancellation is the
content of the theorem, and here it is a consequence of the induction rather
than an assumption. -/
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
