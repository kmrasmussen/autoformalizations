/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Proofs.G1Cpl

/-!
# G1Wire.lean — closing `g1_lojasiewicz` (Mei 2020, Lemma 8)

All the mathematics already exists.  This file supplies the one missing
combinatorial ingredient and performs the assembly.

* `exists_prod_argmax_selector` — a finite argmax of `a ↦ π(a|s) · A^π(s,a)`
  over `A`, at every state.  This is the selector `b` at which the aggregate
  bound is tight; it is **not** `exists_argmax_selector`, which maximises
  `advInf` over `supp πstar` instead.
* `g1_lojasiewicz_proof` — feed `b` to `exists_astar_g1_aggregate_bound` to get
  the witness `astar` together with the aggregate bound at `b`, then feed both
  to `g1_lojasiewicz_of_selector`.
-/

open Finset

namespace PolicyGradient
namespace Proofs

section Wire

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
variable [Nonempty S] [Nonempty A]

open scoped BigOperators

/-- **A product-argmax selector exists.**  At every state there is an action
maximising `π(a|s) · A^π(s,a)` over all of `A`.

This is the selector `g1_lojasiewicz_of_selector` wants: the gradient step
`sum_abs_adv_le_norm` is indifferent to *which* action each state contributes,
so the bound may be taken at the action that makes it tightest.  Contrast
`exists_argmax_selector`, which maximises `advInf` over `supp πstar` — a
different argmax, and the one routed through `πstar` that `Q*` ties can
break. -/
theorem exists_prod_argmax_selector (M : FiniteMDP S A) (π : Policy S A) :
    ∃ b : S → A, ∀ s a,
      (π s) a * advInf M π s a ≤ (π s) (b s) * advInf M π s (b s) := by
  classical
  have hchoice : ∀ s : S, ∃ a : A, ∀ a' : A,
      (π s) a' * advInf M π s a' ≤ (π s) a * advInf M π s a := by
    intro s
    obtain ⟨a, _, hmax⟩ :=
      Finset.exists_max_image (univ : Finset A)
        (fun a => (π s) a * advInf M π s a) univ_nonempty
    exact ⟨a, fun a' => hmax a' (mem_univ a')⟩
  choose f hf using hchoice
  exact ⟨f, fun s a => hf s a⟩

/-- **G1 — Mei et al. (2020), Lemma 8: the non-uniform Łojasiewicz inequality.**

The frozen `PolicyGradient.g1_lojasiewicz` statement, proved.

Assembly: build the product-argmax selector `b`, hand it to
`exists_astar_g1_aggregate_bound` (which produces an `astar` in `supp πstar`
together with the aggregate bound *at* `b`), then hand both to the bridge
`g1_lojasiewicz_of_selector`. -/
@[paper "Mei2020" "Lemma 8"]
theorem g1_lojasiewicz_proof (M : FiniteMDP S A)
    (F : VecPolicy S A (EuclideanSpace ℝ (S × A)))
    (hF : ∀ θ s a, (F.toPolicy θ s) a = softmax (fun a' => θ (s, a')) a)
    (hr : ∀ s a, |M.r s a| ≤ 1) (hγ₀ : 0 ≤ M.γ) (hγ₁ : M.γ < 1)
    (μ : Dist S) (hμ : ∀ s, 0 < μ s)
    (πstar : Policy S A) (hstar : ∀ s, Vinf M πstar s = Vstar M s)
    (θ : EuclideanSpace ℝ (S × A)) :
    ∃ astar : S → A, (∀ s, 0 < (πstar s) (astar s)) ∧
      (⨅ s : S, (F.toPolicy θ s) (astar s))
          / (Real.sqrt (Fintype.card S) * mismatchCoeff M πstar μ)
          * (VstarDist M μ - VinfDist M (F.toPolicy θ) μ)
        ≤ ‖fderiv ℝ (fun t => VinfDist M (F.toPolicy t) μ) θ‖ := by
  classical
  obtain ⟨b, hb⟩ := exists_prod_argmax_selector M (F.toPolicy θ)
  obtain ⟨astar, hastar, hagg⟩ :=
    exists_astar_g1_aggregate_bound M hr hγ₀ hγ₁ μ hμ (F.toPolicy θ) πstar hstar b hb
  exact ⟨astar, hastar,
    g1_lojasiewicz_of_selector M F hF hr hγ₀ hγ₁ μ hμ πstar hstar astar hastar θ b hagg⟩

#print axioms g1_lojasiewicz_proof

end Wire

end Proofs
end PolicyGradient
