/-
# Dynamic Contextual Entanglement Width (DCEW) — DEFINITION ONLY

This file records a paper-faithful definition of a *dynamics* complexity measure
in the N-Frame / observer language, together with the two properties such a
measure would need in order to separate P from NP — stated explicitly as
**open conjectures**.

HONEST STATUS (please read before reusing):
  * `P_side_bound` is the easy direction: true by construction for a suitably
    calibrated radius-1 local-update neighborhood (matches the paper's
    "P = bounded-CEW observers").
  * `NP_side_lower_bound` is, by unfolding the min-over-observers, **logically
    equivalent to P ≠ NP**. Writing this definition does NOT advance it.
  * There is deliberately **no `theorem` deriving a separation**, and **no
    `axiom`** standing in for either conjecture. `WouldYieldSeparation` only
    *names* the conjunction; it is not asserted or proved anywhere.

This is a freestanding abstract definition (no imports, no dependence on the
rest of the development). It is a specification, not a result.
-/

namespace DynamicCEW

/-- An observer is modelled abstractly by its sustained contextual-entanglement
width as a function of input length: `f n` = max instantaneous entanglement the
observer must hold live while deciding inputs of length `n`. -/
abbrev ObserverWidth := Nat → Nat

/-- `DCEWatMost deciders n b`: some observer that decides the language
(i.e. satisfies the predicate `deciders`) achieves width `≤ b` at length `n`.
The dynamic CEW of the language at length `n` is the least such `b`; we use the
`≤ b` predicate form to stay in pure `Nat` with no infimum machinery. -/
def DCEWatMost (deciders : ObserverWidth → Prop) (n b : Nat) : Prop :=
  ∃ f : ObserverWidth, deciders f ∧ f n ≤ b

/-- OPEN CONJECTURE (P-side, the easy direction).
For a language in P there is a poly-width decider:
some observer satisfies `deciders` with width `≤ n^c + 1` at every length.
True by construction for a calibrated radius-1 locality model. -/
def P_side_bound (deciders : ObserverWidth → Prop) : Prop :=
  ∃ c : Nat, ∀ n : Nat, DCEWatMost deciders n (n ^ c + 1)

/-- OPEN CONJECTURE (NP-side).  ***This is equivalent to P ≠ NP.***
It says: for every polynomial bound there is an input length at which *no*
SAT-decider stays within it — i.e. no poly-width (= no efficient) observer
decides SAT, i.e. SAT ∉ P.  Left OPEN; proved nowhere in this file. -/
def NP_side_lower_bound (satDeciders : ObserverWidth → Prop) : Prop :=
  ∀ c : Nat, ∃ n : Nat, ¬ DCEWatMost satDeciders n (n ^ c)

/-- Names the conjunction that *would* yield a separation if both conjectures
held under the same observer-width semantics.  This is **not** asserted and
**not** proved: `NP_side_lower_bound` is itself `P ≠ NP`.  No theorem in this
file discharges it and no axiom stands in for it. -/
def WouldYieldSeparation
    (pDeciders satDeciders : ObserverWidth → Prop) : Prop :=
  P_side_bound pDeciders ∧ NP_side_lower_bound satDeciders

end DynamicCEW
