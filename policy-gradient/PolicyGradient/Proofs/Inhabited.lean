/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target
import PolicyGradient.Proofs
import PolicyGradient.Theorem

/-!
# Proofs/Inhabited.lean -- existence witnesses for the quantified types

CHECK 5 asks Lean's instance search whether each structure a frozen goal
quantifies over is `Nonempty`. Without these, every goal mentioning such a type
is reported as possibly vacuous -- correctly, since a structure that cannot be
built makes every goal over it vacuous at once.

Most of these objects already existed as concrete constructions (`Witness.lean`
builds an MDP; `g5_g6_softmax_family` builds a `VecPolicy`). What was missing was
registering them as *instances*, so the check could find them. That gap is the
point of having the check: the facts were present and unusable.
-/

namespace PolicyGradient

open Finset

/-- A distribution exists: the point mass. -/
noncomputable instance instNonemptyDist {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] : Nonempty (Dist A) :=
  ⟨PolicyGradient.Proofs.pointMass (Classical.arbitrary A)⟩

/-- An MDP exists: zero rewards, point-mass transitions, `γ = 0`. -/
noncomputable instance instNonemptyFiniteMDP {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [Nonempty S] [Nonempty A] :
    Nonempty (FiniteMDP S A) :=
  ⟨{ P := fun _ _ => PolicyGradient.Proofs.pointMass (Classical.arbitrary S)
     r := fun _ _ => 0
     γ := 0 }⟩

/-- A differentiable policy family exists: the constant one, derivative `0`.

Note this witness is deliberately *degenerate* — it is the same constant family
that made a bare `Nonempty (VecPolicy ...)` an unacceptable goal (see
`Goal.lean`'s note on `g5_g6_softmax_family`). That is fine here and not a
contradiction: inhabitation asks whether the type can be built at all, which is
what rules out vacuity. A *goal* about such a family must additionally pin which
family it means, and `g5_g6_softmax_family` does exactly that. -/
noncomputable instance instNonemptyDiffPolicy {S A : Type*} [Fintype A]
    [DecidableEq A] [Nonempty A] : Nonempty (DiffPolicy S A) :=
  ⟨{ toPolicy := fun _ _ => PolicyGradient.Proofs.pointMass (Classical.arbitrary A)
     dπ := fun _ _ _ => 0
     hasDeriv := fun _ _ _ => hasDerivAt_const _ _ }⟩

/-- A twice-differentiable family exists: the same constant one. -/
noncomputable instance instNonemptyC2Policy {S A : Type*} [Fintype A]
    [DecidableEq A] [Nonempty A] : Nonempty (C2Policy S A) :=
  ⟨{ toPolicy := fun _ _ => PolicyGradient.Proofs.pointMass (Classical.arbitrary A)
     dπ := fun _ _ _ => 0
     hasDeriv := fun _ _ _ => hasDerivAt_const _ _
     d2π := fun _ _ _ => 0
     hasDeriv2 := fun _ _ _ => hasDerivAt_const _ _ }⟩

/-- A vector-parameter family exists.

`g5_g6_softmax_family` constructs the *softmax* one, which is the object the
goals are about; this only records that the type is inhabited. -/
noncomputable instance instNonemptyVecPolicy {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq A] [Nonempty A] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Nonempty (VecPolicy S A E) :=
  ⟨{ toPolicy := fun _ _ => PolicyGradient.Proofs.pointMass (Classical.arbitrary A)
     dπ := fun _ _ _ => 0
     hasFDeriv := fun _ _ _ => hasFDerivAt_const _ _ }⟩

end PolicyGradient
