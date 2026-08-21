# Mathlib tsum/derivative API — verified names (rev db584cd6, Lean 4.33.0)

Looked up in the local clone before writing proofs. Many "obvious" names are
wrong in this revision; each wrong guess costs a build cycle, so they are
recorded here.

## Structural surprise: SummationFilter

This revision migrated `Summable`/`tsum` to carry a **`SummationFilter`** `L`.
`∑' i, f i` elaborates to `tsum f (unconditional _)`, and `unconditional` has
`LeAtTop`/`NeBot` instances, so `[L.NeBot]` hypotheses discharge automatically.
Consequence: many former bare `tsum_*` lemmas moved into the `Summable.`
namespace and now take a `Summable` hypothesis.

Worse for searching: those names are `to_additive`-generated, so they **never
appear literally in the source**. `grep "theorem Summable.tsum_add"` returns
nothing and you wrongly conclude the lemma is missing. Grep for *usages*, or
read the multiplicative original (`Multipliable.tprod_mul`).
They are also `protected` — always write the full name or use dot-notation.

## The main tool

```lean
theorem hasDerivAt_tsum (hu : Summable u) (hg : ∀ n y, HasDerivAt (g n) (g' n y) y)
    (hg' : ∀ n y, ‖g' n y‖ ≤ u n) (hg0 : Summable fun n => g n y₀) (y : 𝕜) :
    HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y
```
`Mathlib/Analysis/Calculus/SmoothSeries.lean:133`

The bound `hg'` is **global and uniform in `y`** — not just near our `θ`. If the
score is only locally bounded (softmax logits are unbounded!) we must instead use
`hasDerivAt_tsum_of_isPreconnected` (:89) on a ball, supplying `IsOpen`,
`IsPreconnected`, and membership. **This is the decision point for our proof.**

Also: `summable_of_summable_hasDerivAt` (:113) propagates summability;
`deriv_tsum_apply` (:168) is the pointwise `deriv` version; the `HasDerivAt`
flavour of `differentiable_tsum` is `differentiable_tsum'` (:157), with a prime.

## Geometric series

```lean
summable_geometric_of_lt_one (h₁ : 0 ≤ r) (h₂ : r < 1) : Summable fun n : ℕ => r ^ n
tsum_geometric_of_lt_one    (h₁ : 0 ≤ r) (h₂ : r < 1) : ∑' n, r ^ n = (1 - r)⁻¹
```
`Mathlib/Analysis/SpecificLimits/Basic.lean:324,329` — note **two** hypotheses,
not `|r| < 1`.

```lean
Summable.of_norm_bounded (hg : Summable g) (h : ∀ i, ‖f i‖ ≤ g i) : Summable f
```
`Mathlib/Analysis/Normed/Group/InfiniteSum.lean:111` — summability of the *bound*
comes first. `Summable.of_nonneg_of_le` also exists but lives, surprisingly, in
`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:530`.

If the derivative bound grows like `t` (likely for us — `∂_θ` of a discounted
return carries a `∑_{k≤t}` score factor, giving a `(t+1)` prefactor):
```lean
summable_pow_mul_geometric_of_norm_lt_one (k : ℕ) (hr : ‖r‖ < 1) :
    Summable (fun n => (n : R) ^ k * r ^ n)
tsum_coe_mul_geometric_of_norm_lt_one (hr : ‖r‖ < 1) : ∑' n, n * r ^ n = r / (1 - r) ^ 2
```
`Mathlib/Analysis/SpecificLimits/Normed.lean:488,547`

## Splitting off the first term (our `Finset.sum_range_succ'` analogue)

```lean
tsum_eq_zero_add' (hf : Summable fun n => f (n + 1)) : ∑' b, f b = f 0 + ∑' b, f (b + 1)
Summable.tsum_eq_zero_add (hf : Summable f)          : ∑' b, f b = f 0 + ∑' b, f (b + 1)
Summable.sum_add_tsum_nat_add (k) (h : Summable f) :
    (∑ i ∈ range k, f i) + ∑' i, f (i + k) = ∑' i, f i
summable_nat_add_iff (k) : Summable (fun n => f (n + k)) ↔ Summable f
```
`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:192,237,233,221`

## Finite sum ↔ tsum (our finite states × infinite time)

```lean
Summable.tsum_finsetSum (hf : ∀ i ∈ s, Summable (f i)) :
    ∑' b, ∑ i ∈ s, f i b = ∑ i ∈ s, ∑' b, f i b
```
`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:729`. Only needs summability per
element — cheap, because the outer sum is finite. To go the other way,
`rw [← Summable.tsum_finsetSum]` and discharge the side goals.

## Swapping two tsums

```lean
Summable.tsum_comm (h : Summable (Function.uncurry f)) : ∑' (c) (b), f b c = ∑' (b) (c), f b c
```
`Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean:259` (one hypothesis,
in the `CompleteT0Space` section — automatic for ℝ). The three-hypothesis
version is `Summable.tsum_comm'` (:174).

## Names that were WRONG in my first guess

| guessed | reality |
|---|---|
| `tsum_add` / `tsum_sub` | `Summable.tsum_add` / `Summable.tsum_sub` (protected) |
| `Summable.tsum_eq` | does not exist → `HasSum.tsum_eq` |
| `tsum_geometric_mul` | does not exist → compose `tsum_mul_left` + `tsum_geometric_of_lt_one` |
| `tsum_eq_zero_add` | `tsum_eq_zero_add'` or `Summable.tsum_eq_zero_add` |
| `tsum_sum` / `Finset.sum_tsum` | neither exists → `Summable.tsum_finsetSum` |
| `tsum_comm` | `Summable.tsum_comm` (bare version is ℝ≥0∞-only) |
| `deriv_tsum` | exists but is function-level; pointwise is `deriv_tsum_apply` |
| `abs_add` | `abs_add_le` |

`tsum_mul_left` / `tsum_mul_right` DO exist bare for ℝ with **no** summability
hypothesis (`InfiniteSum/Ring.lean:115`) — they case-split on `a = 0`.
