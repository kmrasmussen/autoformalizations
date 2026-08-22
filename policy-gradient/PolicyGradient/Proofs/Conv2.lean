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

end Conv2

end Proofs
end PolicyGradient
