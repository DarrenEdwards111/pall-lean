/-
# Dynamic Contextual Entanglement Width (DCEW) -- definition only

This file records a paper-faithful definition of a dynamic complexity measure
in the N-Frame / observer language, together with the two properties such a
measure would need in order to separate P from NP.  Both properties are stated
as open predicates.  No separation theorem is asserted here.
-/

namespace DynamicCEW

/-- An observer is represented abstractly by its sustained contextual width as
a function of input length. -/
abbrev ObserverWidth := Nat -> Nat

/-- `DCEWatMost deciders n b` says that some observer deciding the language
achieves width at most `b` at input length `n`. -/
def DCEWatMost (deciders : ObserverWidth -> Prop) (n b : Nat) : Prop :=
  exists f : ObserverWidth, deciders f /\ f n <= b

/-- P-side predicate: a language has a polynomial-width observer family. -/
def P_side_bound (deciders : ObserverWidth -> Prop) : Prop :=
  exists c : Nat, forall n : Nat, DCEWatMost deciders n (n ^ c + 1)

/-- NP-side predicate.  For SAT, proving this is the real lower-bound theorem:
no polynomial dynamic observer width suffices. -/
def NP_side_lower_bound (satDeciders : ObserverWidth -> Prop) : Prop :=
  forall c : Nat, exists n : Nat, Not (DCEWatMost satDeciders n (n ^ c))

/-- Names the conjunction that would yield the observer-width separation. -/
def WouldYieldSeparation
    (pDeciders satDeciders : ObserverWidth -> Prop) : Prop :=
  P_side_bound pDeciders /\ NP_side_lower_bound satDeciders

end DynamicCEW
