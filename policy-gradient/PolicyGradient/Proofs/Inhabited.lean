/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import PolicyGradient.Target
import PolicyGradient.Proofs

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

end PolicyGradient
