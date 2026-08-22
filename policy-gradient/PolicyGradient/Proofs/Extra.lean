/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target
import PolicyGradient.Proofs.G1
import PolicyGradient.Proofs.G2
import PolicyGradient.Proofs.G2b
import PolicyGradient.Proofs.G7b
import PolicyGradient.Proofs.Mei4
import PolicyGradient.Proofs.Mei6
import PolicyGradient.Proofs.VecStep
import PolicyGradient.Proofs.AKM51

/-!
# Proofs/Extra.lean — additional proof modules

**New work goes in its own file under `PolicyGradient/Proofs/`, not appended to
`Proofs.lean`.**

Two agents appending before the same `end Proofs` produced this repo's first
merge conflict, and then its second and third. Separate files make that class of
collision structurally impossible — git never has to reconcile two edits to one
region.

To add a module: create `PolicyGradient/Proofs/<Topic>.lean` with
`import PolicyGradient.Target` and `namespace PolicyGradient.Proofs`, then add
one `import` line here. Import lines at distinct positions still conflict far
less often than bodies appended at a shared anchor.

`Proofs.lean` keeps the work that predates this split; it is not being
retroactively carved up while agents hold branches against it.
-/

namespace PolicyGradient
namespace Proofs

/-! No modules yet — add `import PolicyGradient.Proofs.<Topic>` above as they
land. -/

end Proofs
end PolicyGradient
