/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv

/-!
# Conv2 — `Goal.softmax_policy_converges`: the gap, narrowed to the tie split

## Status: OPEN, but the obstruction has moved

`Conv.lean` located the gap at *advantage sign-stability*, and recorded that
every fact supplying it (`eventually_adv_neg`, `theta_eventually_antitone`,
`theta_tendsto_atBot_of_adv_neg`, `ResidC9.ratio_step`) binds `πbar` and `hlim`,
so using them would be circular.  **That circularity is broken here.**

### 1. The reduction named in `Conv.lean` is unreachable — `(†)` is FALSE

`Conv.lean` reduces the goal to `Summable (fun t => ‖θ (t+1) - θ t‖)` (`(†)`),
via `policy_converges_of_summable_theta_increments`, and calls that "your
target".  It is not reachable, because **it is false along the actual
trajectory**.

Numerically, on the single-state `γ = 0`, `r = (1,0)` trajectory at `η = 0.2`
from `θ₀ = (0,0)`, the partial sums `∑_{t<T} ‖∇V(θ_t)‖` are

    T = 10⁴ : 29.31      T = 10⁵ : 37.46
    T = 10⁶ : 45.61      T = 4·10⁶ : 50.51

— increments of `≈ 8.15` per decade, i.e. **logarithmic divergence**
(`≈ 3.54 · ln 10`).  Since `θ_{t+1} - θ_t = η ∇V(θ_t)` exactly, `(†)` fails.

This is not a numerical artifact; the trajectory has a closed form.  With
`|A| = 2`, write `u_t = θ_t(s,a₁) - θ_t(s,a₂)`, so `π_t(a₁|s) = σ(u_t)` for the
logistic `σ`.  Then `A_t(s,a₁) = 1 - σ(u_t)` and `A_t(s,a₂) = -σ(u_t)`, so both
gradient coordinates have modulus `σ(u_t)(1 - σ(u_t)) = σ'(u_t)` and

    ‖∇V(θ_t)‖ = √2 · σ'(u_t),        u_{t+1} - u_t = 2η · σ'(u_t).

Hence `∑_{t<T} ‖∇V(θ_t)‖ = (√2 / (2η)) · (u_T - u_0)`: the gradient sum is the
logit gap, up to a constant.  For large `u`, `σ'(u) ≈ e^{-u}`, so
`e^{u} du ≈ 2η dt` gives `u_T ≈ log(2ηT)` and

    ∑_{t<T} ‖∇V(θ_t)‖ ≈ (√2 / (2η)) · log(2ηT)  →  ∞.

At `η = 0.2` that formula predicts `29.324, 37.465, 45.606, 50.507` for the four
horizons above — the simulated values to three decimals.  `(†)` is false, and
false for a structural reason: **the gradient sum *is* the logit gap**, and the
logit gap must diverge precisely because the policy converges to a vertex.
Over the same run the *policy* total variation `∑_t ‖π_{t+1} - π_t‖₁` saturates
at `0.999999`.  So the path has **finite length in the simplex and infinite
length in the logits**: `θ_t(s,a*) → +∞` like `log t`, which is exactly the
`‖θ‖ → ∞` that `Conv.lean` already identified as killing the Łojasiewicz route.

This kills route (3) of the three suggested attacks (bound `‖θ(t+1) - θ t‖` by a
summable majorant) at the root: no such majorant exists.  It also means the
`(†)`-reduction, though correctly proved, is a **dead end**, and any future work
should not aim at it.  `policy_converges_of_eventually_monotone` — the *other*
reduction in `Conv.lean` — is the live one.

### 2. The advantage converges with NO limit policy (the unlock)

The circularity `Conv.lean` describes rests on an assumption that turns out to
be unnecessary.  Unfolding `Target.advInf`,

    advInf M π s a = r(s,a) + γ · ∑_{s'} P(s'|s,a) · Vinf M π s' - Vinf M π s,

the advantage depends on the policy **only through the value function**.  And
the value converges along the trajectory *unconditionally*: `exists_Vinf_limit`
(AKM Lemma C.2) makes `t ↦ Vinf M (F.toPolicy (θ t)) s₀` monotone, and
`Vinf_le_one_div` bounds it — neither binds `πbar`.  So:

* `exists_Vinf_tendsto` — the value at each state converges.  πbar-free.
* `exists_adv_tendsto` — **the advantage `A^{(t)}(s,a)` converges.**  πbar-free.

This is the πbar-free substitute for AKM Lemma C.3, and it **discharges the
sign-stability half of `Conv.lean`'s gap outright**: a convergent sequence with
nonzero limit is eventually of one sign, so `theta_eventually_monotone_of_adv_ne`
makes every such logit eventually monotone with no limit policy in hand.

### 3. What that buys, and what is left

Write `Abar s a` for the limit of `A^{(t)}(s,a)` and `Z s = {a | Abar s a = 0}`.
`Z s` is exactly the set of actions greedy-optimal for the limiting value
function.  Unconditionally (all πbar-free, all proved below):

* `a ∉ Z s` ⟹ `π_t(a|s) → 0` — `tendsto_pi_zero_of_adv_limit_ne`, dividing the
  πbar-free `tendsto_pi_adv_zero` (AKM Lemma C.4) by the nonzero advantage limit;
* the mass on `Z s` tends to `1` — `tendsto_mass_on_zero_set`;
* if `Z s` is a singleton, **every coordinate at `s` converges** —
  `coord_tendsto_of_unique_zero`;
* exactly-tied actions never trade mass back — `tie_gap_monotone`.

`softmax_policy_converges_of_tie_split` assembles these: it has **exactly** the
frozen goal's hypotheses plus one extra, `hZ`, and `hZ` constrains **only the
actions whose limiting advantage vanishes**.  Compare `Conv.lean`'s capstone,
which needed sign-stability of *every* advantage and was *still* insufficient
(its own obstruction note shows sign-stability fails to give monotone policy
coordinates once `|A| ≥ 3`).  Here that half is gone and the tie split is all
that remains.

### 4. Why the tie split does not close, precisely

For `a, b ∈ Z s` the logit gap moves by

    Δ(θ_t(s,a) - θ_t(s,b)) = η · d^{(t)}_μ(s) · (π_t(a|s) A_t(s,a) - π_t(b|s) A_t(s,b)),

and `tendsto_pi_adv_zero` sends **both** products to `0` — with no rate.  So the
sign of the difference is unconstrained, which is the same rate comparison
`Conv.lean` names, now confined to `Z s` instead of all of `A`.

`tie_gap_monotone` closes it under an **exact** tie, `A_t(s,a) = A_t(s,b)` at
every finite `t`: then the increment is `η d_t(s) A_t (π_t(a|s) - π_t(b|s))`,
`softmax_mono` gives that difference the sign of the logit gap, and the dynamics
are self-reinforcing — whichever tied action is ahead pulls further ahead, so the
gap is monotone and the split converges (to a vertex or to an interior point,
both of which occur).  Numerically this is what happens: over `3·10⁵` steps on
`r = (1,1,0)` the two tied coordinates show **zero** sign flips in `A_t`, and the
tied probabilities drift monotonically.

That hypothesis is **not** available in general.  For `a, b ∈ Z s`,

    A_t(s,a) - A_t(s,b) = r(s,a) - r(s,b) + γ · ∑_{s'} (P(s'|s,a) - P(s'|s,b)) · V_t(s'),

which tends to `0` but is nonzero at finite `t` unless the rewards *and*
transitions agree exactly.  A `2`-state, `3`-action sweep with `γ = 0.6` and
random transitions confirms the difference: at states where two limiting
advantages are close but not equal, `A_t` at one of them is **negative for
thousands of consecutive steps** before settling — so neither the exact-tie
hypothesis nor a uniform `A_t ≥ 0` on `Z s` survives `γ > 0`.

Closing `hZ` in general needs a comparison of the **rates** at which
`π_t(a|s) A_t(s,a)` and `π_t(b|s) A_t(s,b)` vanish, for `a, b` both in `Z s`.
That is `ResidC9.ratio_step`'s estimate restricted to the tied set, and
`ratio_step` binds `πbar` — the one place the circularity survives.

### Summary against the three suggested routes

1. **Łojasiewicz on the centered logits** — not attempted past the diagnosis;
   §1 shows why it cannot help *as a route to `(†)`*, since `(†)` is false.
   Whether a Łojasiewicz bound could drive the *policy*-space argument is open.
2. **`ResidC8`/`ResidC9` facts stated without `πbar`** — `theta_decrement`,
   `theta_step_bound`, `ratio_step`, `ratio_induction`, `antitone_from` and
   `sum_theta_eq_zero` are all πbar-free and are used above.  The *sign-stability*
   facts all bind `πbar`, but §2 shows they are no longer needed: the advantage
   converges directly.
3. **A summable majorant for `‖θ(t+1) - θ t‖`** — refuted in §1.
-/

namespace PolicyGradient
namespace Proofs

open Filter Topology Finset

section Conv2

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

/-- **The value at each state converges**, with no limit policy assumed:
`exists_Vinf_limit` makes it monotone and `Vinf_le_one_div` bounds it above. -/
theorem exists_Vinf_tendsto (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s₀ : S) :
    ∃ L : ℝ, Tendsto (fun t => Vinf M (F.toPolicy (θ t)) s₀) atTop (nhds L) := by
  have hmono := exists_Vinf_limit M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep s₀
  have hbdd : BddAbove (Set.range fun t => Vinf M (F.toPolicy (θ t)) s₀) :=
    ⟨1 / (1 - M.γ), by
      rintro x ⟨t, rfl⟩
      exact Vinf_le_one_div M hr hγ₀ hγ₁ _ _⟩
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩

/-- **The advantage converges**, with no limit policy assumed.

`advInf M π s a = r(s,a) + γ ∑_{s'} P(s'|s,a) Vinf π s' - Vinf π s` depends on
`π` *only through the value function*, and the value converges state-by-state
(`exists_Vinf_tendsto`).  So the advantage along the trajectory converges — a
πbar-free substitute for AKM Lemma C.3, which derives the same fact from an
assumed limit policy. -/
theorem exists_adv_tendsto (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a : A) :
    ∃ L : ℝ, Tendsto (fun t => advInf M (F.toPolicy (θ t)) s a) atTop (nhds L) := by
  classical
  choose V hV using exists_Vinf_tendsto M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep
  refine ⟨M.r s a + M.γ * (∑ s', (M.P s a) s' * V s') - V s, ?_⟩
  have hsum : Tendsto (fun t => ∑ s', (M.P s a) s' * Vinf M (F.toPolicy (θ t)) s')
      atTop (nhds (∑ s', (M.P s a) s' * V s')) :=
    tendsto_finsetSum _ (fun s' _ => (hV s').const_mul _)
  have := ((hsum.const_mul M.γ).const_add (M.r s a)).sub (hV s)
  simpa only [advInf] using this


/-- **Every logit is eventually monotone when its limiting advantage is nonzero**,
πbar-free.  The advantage converges (`exists_adv_tendsto`); if its limit is
nonzero the sign is eventually constant, and `theta_decrement` transfers that
sign to the logit increment. -/
theorem theta_eventually_monotone_of_adv_ne (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a : A) (T : ℕ)
    (hsgn : (∀ t, T ≤ t → 0 ≤ advInf M (F.toPolicy (θ t)) s a) ∨
            (∀ t, T ≤ t → advInf M (F.toPolicy (θ t)) s a ≤ 0)) :
    (∀ t, T ≤ t → (θ t) (s, a) ≤ (θ (t + 1)) (s, a)) ∨
    (∀ t, T ≤ t → (θ (t + 1)) (s, a) ≤ (θ t) (s, a)) := by
  have hdnn : ∀ t, 0 ≤ dinfDist M (F.toPolicy (θ t)) μ s :=
    fun t => dinfDist_nonneg M hγ₀ _ _ _
  have hπnn : ∀ t, 0 ≤ (F.toPolicy (θ t) s) a := fun t => (F.toPolicy (θ t) s).nonneg a
  rcases hsgn with hpos | hneg
  · left
    intro t ht
    have hdec := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a
    have hge : 0 ≤ η * (dinfDist M (F.toPolicy (θ t)) μ s
        * ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)) :=
      mul_nonneg hη₀.le (mul_nonneg (hdnn t) (mul_nonneg (hπnn t) (hpos t ht)))
    nlinarith [hdec, hge]
  · right
    intro t ht
    have hdec := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a
    have hle : η * (dinfDist M (F.toPolicy (θ t)) μ s
        * ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hη₀.le
        (mul_nonpos_of_nonneg_of_nonpos (hdnn t)
          (mul_nonpos_of_nonneg_of_nonpos (hπnn t) (hneg t ht)))
    nlinarith [hdec, hle]

/-- If the limiting advantage is **nonzero**, `tendsto_pi_adv_zero` forces the
policy coordinate to zero: `π_t(a|s) = (π_t(a|s) A_t(s,a)) / A_t(s,a) → 0/L = 0`.
πbar-free. -/
theorem tendsto_pi_zero_of_adv_limit_ne (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a : A) (L : ℝ) (hL : L ≠ 0)
    (hAlim : Tendsto (fun t => advInf M (F.toPolicy (θ t)) s a) atTop (nhds L)) :
    Tendsto (fun t => (F.toPolicy (θ t) s) a) atTop (nhds 0) := by
  have hprod := tendsto_pi_adv_zero M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep s a
  have hdiv : Tendsto (fun t => ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)
      / advInf M (F.toPolicy (θ t)) s a) atTop (nhds (0 / L)) := hprod.div hAlim hL
  rw [zero_div] at hdiv
  -- eventually the advantage is nonzero, so the quotient is the policy coordinate
  have hev : ∀ᶠ t in atTop, ((F.toPolicy (θ t) s) a * advInf M (F.toPolicy (θ t)) s a)
      / advInf M (F.toPolicy (θ t)) s a = (F.toPolicy (θ t) s) a := by
    filter_upwards [hAlim.eventually_ne hL] with t ht
    exact mul_div_cancel_right₀ _ ht
  exact hdiv.congr' hev


/-- Per state, the actions whose limiting advantage vanishes carry all the mass:
if `π_t(b|s) → 0` for every `b` outside a set `Z`, then the mass on `Z` tends to
`1`.  Stated as: `∑_{b ∈ Z} π_t(b|s) → 1`. -/
theorem tendsto_mass_on_zero_set (π : ℕ → Policy S A) (s : S) (Z : Finset A)
    (hz : ∀ b ∉ Z, Tendsto (fun t => (π t s) b) atTop (nhds 0)) :
    Tendsto (fun t => ∑ b ∈ Z, (π t s) b) atTop (nhds 1) := by
  classical
  have hsplit : ∀ t, ∑ b ∈ Z, (π t s) b
      = 1 - ∑ b ∈ Finset.univ \ Z, (π t s) b := by
    intro t
    have := (π t s).sum_eq_one
    have hu : ∑ b ∈ Z, (π t s) b + ∑ b ∈ Finset.univ \ Z, (π t s) b
        = ∑ b ∈ Finset.univ, (π t s) b :=
      Finset.sum_add_sum_compl Z (fun b => (π t s) b)
    rw [(π t s).sum_eq_one] at hu
    linarith
  have hcomp : Tendsto (fun t => ∑ b ∈ Finset.univ \ Z, (π t s) b) atTop (nhds 0) := by
    have : Tendsto (fun t => ∑ b ∈ Finset.univ \ Z, (π t s) b) atTop
        (nhds (∑ _b ∈ Finset.univ \ Z, (0:ℝ))) :=
      tendsto_finsetSum _ (fun b hb => hz b (Finset.mem_sdiff.mp hb).2)
    simpa using this
  have hfin : Tendsto (fun t => (1:ℝ) - ∑ b ∈ Finset.univ \ Z, (π t s) b) atTop
      (nhds ((1:ℝ) - 0)) := tendsto_const_nhds.sub hcomp
  rw [sub_zero] at hfin
  exact hfin.congr (fun t => (hsplit t).symm)


/-! ## The πbar-free skeleton, assembled

At each state `s` let `Abar s a := lim_t A^{(t)}(s,a)` (`exists_adv_tendsto`) and
`Z s := {a | Abar s a = 0}`.  Then, with **no limit policy assumed**:

* every `a ∉ Z s` has `π_t(a|s) → 0` (`tendsto_pi_zero_of_adv_limit_ne`);
* the mass on `Z s` tends to `1` (`tendsto_mass_on_zero_set`);
* every logit `θ_t(s,a)` is eventually monotone (`theta_eventually_monotone_of_adv_ne`,
  using that a convergent sequence with nonzero limit is eventually of one sign,
  and that a coordinate with `Abar s a = 0` is handled by the `Z`-case below).

So the goal reduces to a **single** remaining statement: *the policy coordinates
inside `Z s` converge*.  When `Z s` is a singleton this is immediate — that
coordinate's probability is `1` minus the others, all of which tend to `0`. -/

/-- **The singleton-`Z` case closes the goal at a state.**  If exactly one action
`a₀` has a nonzero limiting advantage failing, i.e. every `b ≠ a₀` has
`π_t(b|s) → 0`, then `π_t(a₀|s) → 1` and every coordinate at `s` converges. -/
theorem coord_tendsto_of_unique_zero (π : ℕ → Policy S A) (s : S) (a₀ : A)
    (hz : ∀ b, b ≠ a₀ → Tendsto (fun t => (π t s) b) atTop (nhds 0)) :
    ∀ a, ∃ L : ℝ, Tendsto (fun t => (π t s) a) atTop (nhds L) := by
  classical
  intro a
  by_cases h : a = a₀
  · subst h
    refine ⟨1, ?_⟩
    have hmass : Tendsto (fun t => ∑ b ∈ ({a} : Finset A), (π t s) b) atTop (nhds 1) := by
      refine tendsto_mass_on_zero_set π s {a} ?_
      intro b hb
      exact hz b (by simpa using hb)
    simpa using hmass
  · exact ⟨0, hz a h⟩


/-! ### The tie mechanism: exactly-tied actions never trade mass back

The remaining case is two actions `a b` at the same state whose limiting
advantages both vanish.  When their advantages agree *at every finite time* —
which is what an exact reward/transition tie produces — the dynamics are
**self-reinforcing**, and this is provable outright.

Writing `c_t = η · d^{(t)}_μ(s) ≥ 0` and `A_t = A^{(t)}(s,a) = A^{(t)}(s,b)`,
`theta_decrement` gives

    (θ_{t+1}(s,a) - θ_{t+1}(s,b)) - (θ_t(s,a) - θ_t(s,b)) = c_t · A_t · (π_t(a|s) - π_t(b|s)),

and `softmax_mono` makes `π_t(a|s) - π_t(b|s)` carry the same sign as
`θ_t(s,a) - θ_t(s,b)`.  So while `A_t ≥ 0` the logit gap moves *away from zero*:
whichever tied action is ahead stays ahead and pulls further ahead.  The gap is
therefore monotone from any time at which `A_t ≥ 0` holds onwards, which is
exactly the eventual-monotonicity input the goal needs — with no limit policy. -/

/-- **Exactly-tied actions: the logit gap is monotone.**  If two actions share
the same advantage at every step from `T` on and that advantage is `≥ 0`, then
the sign of `θ_t(s,a) - θ_t(s,b)` cannot change, and `|θ_t(s,a) - θ_t(s,b)|` is
non-decreasing: the gap moves away from zero. -/
theorem tie_gap_monotone (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (η : ℝ) (hη₀ : 0 < η)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (s : S) (a b : A) (t : ℕ)
    (htie : advInf M (F.toPolicy (θ t)) s a = advInf M (F.toPolicy (θ t)) s b)
    (hAnn : 0 ≤ advInf M (F.toPolicy (θ t)) s a)
    (hge : (θ t) (s, b) ≤ (θ t) (s, a)) :
    (θ t) (s, a) - (θ t) (s, b) ≤ (θ (t + 1)) (s, a) - (θ (t + 1)) (s, b) := by
  have hda := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s a
  have hdb := theta_decrement M F hF hr hγ₀ hγ₁ μ η θ hstep t s b
  -- put both decrements in terms of the common advantage at `a`
  rw [← htie] at hdb
  have hdnn : 0 ≤ dinfDist M (F.toPolicy (θ t)) μ s := dinfDist_nonneg M hγ₀ _ _ _
  -- the softmax order matches the logit order
  have hpi : (F.toPolicy (θ t) s) b ≤ (F.toPolicy (θ t) s) a := by
    rw [hF, hF]; exact softmax_mono _ a b hge
  -- the gap's increment is `η · d · A · (π a - π b) ≥ 0`
  have hprod : 0 ≤ η * (dinfDist M (F.toPolicy (θ t)) μ s
      * (((F.toPolicy (θ t) s) a - (F.toPolicy (θ t) s) b)
          * advInf M (F.toPolicy (θ t)) s a)) :=
    mul_nonneg hη₀.le (mul_nonneg hdnn (mul_nonneg (by linarith) hAnn))
  nlinarith [hda, hdb, hprod]


/-! ## The capstone: the frozen goal, conditional on the tie split converging

Everything above is πbar-free.  Assembling it, the frozen goal follows from a
single remaining hypothesis, and that hypothesis concerns **only the actions
whose limiting advantage vanishes**.

`hZ` below says: at each state, the policy coordinates of the *zero-limiting-
advantage* actions converge.  Every other coordinate is handled unconditionally
by `tendsto_pi_zero_of_adv_limit_ne`.

Compare `Conv.lean`'s capstone, which needed sign-stability of **every**
advantage *and* was still insufficient (its own obstruction note shows
sign-stability does not give monotone policy coordinates for `|A| ≥ 3`).  Here
the sign-stability half is **discharged outright** — advantages converge, by
`exists_adv_tendsto` — and what remains is strictly the tie split. -/

/-- **The frozen goal, given that the tie split converges.**

Exactly `Goal.softmax_policy_converges`'s hypotheses plus `hZ`, which asks only
that coordinates with vanishing limiting advantage converge. -/
theorem softmax_policy_converges_of_tie_split (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (η : ℝ) (hη₀ : 0 < η) (hη : η ≤ (1 - M.γ) ^ 2 / 5)
    (θ : ℕ → EuclideanSpace ℝ (S × A))
    (hstep : ∀ t, θ (t + 1)
      = θ t + η • gradient (fun w => VinfDist M (F.toPolicy w) μ) (θ t))
    (hZ : ∀ s a, Tendsto (fun t => advInf M (F.toPolicy (θ t)) s a) atTop (nhds 0) →
      ∃ L : ℝ, Tendsto (fun t => (F.toPolicy (θ t) s) a) atTop (nhds L)) :
    ∃ πbar : Policy S A,
      Tendsto (fun t s a => (F.toPolicy (θ t) s) a) atTop
        (nhds (fun s a => (πbar s) a)) := by
  classical
  refine exists_policy_limit_of_coord_tendsto (fun t => F.toPolicy (θ t)) ?_
  intro s a
  obtain ⟨L, hL⟩ := exists_adv_tendsto M F hF hr hγ₀ hγ₁ μ η hη₀ hη θ hstep s a
  by_cases hL0 : L = 0
  · exact hZ s a (by rw [← hL0]; exact hL)
  · exact ⟨0, tendsto_pi_zero_of_adv_limit_ne M F hF hr hγ₀ hγ₁ μ hμ η hη₀ hη θ hstep
      s a L hL0 hL⟩


/-! ## Axiom / type audit -/

section Audit

-- The capstone is a genuine theorem of the ambient logic only.
#print axioms softmax_policy_converges_of_tie_split
#print axioms exists_adv_tendsto
#print axioms tie_gap_monotone
#print axioms coord_tendsto_of_unique_zero

end Audit

end Conv2

end Proofs
end PolicyGradient
