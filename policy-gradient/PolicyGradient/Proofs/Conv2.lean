/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.Conv

/-! # Conv2 — scratch -/

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

end Conv2

end Proofs
end PolicyGradient
