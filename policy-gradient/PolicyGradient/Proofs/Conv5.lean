/-
# AKM 5.1 / Mei Lemma 9 for general `γ`.

`hlead` of `Proofs.Conv3.softmax_policy_converges_of_leader` is **per-state**:
the `∃ T` is inside the `∀ s`, so each state may pick its own leader and time.
-/
import PolicyGradient.Proofs.Conv3

namespace PolicyGradient
namespace Proofs
namespace Conv5

open Filter Topology Finset

end Conv5
end Proofs
end PolicyGradient
