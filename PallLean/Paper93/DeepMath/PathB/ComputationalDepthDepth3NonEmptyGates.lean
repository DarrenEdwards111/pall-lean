import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BottomNonempty

/-!
# Tight switching, step 88: the non-empty-gates predicate (branch `razborov-recoverRho-wip`)

The merge's count-reduction `|gs| → 1` is a genuine reduction only when the gate lists are non-empty (the
`gAnd []`/`gOr []` degeneracy grows the count `0 → 1`).  We abstract "all gate lists non-empty" as
`NonEmptyGates`, and bridge it from the alternation invariant: every `AltO`/`AltA` tower has non-empty gates.

* `NonEmptyGates` — every internal gate list is non-empty.
* `AltO_NonEmptyGates` / `AltA_NonEmptyGates` — alternating towers have non-empty gates.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open Layered

variable {n : ℕ}

/-- Every internal gate list of the tower is non-empty. -/
inductive NonEmptyGates : Layered n → Prop where
  | dnf (cs : List (Clause n)) : NonEmptyGates (dnf cs)
  | cnf (cs : List (Clause n)) : NonEmptyGates (cnf cs)
  | gAnd (gs : List (Layered n)) (hne : gs ≠ []) (h : ∀ g ∈ gs, NonEmptyGates g) :
      NonEmptyGates (gAnd gs)
  | gOr (gs : List (Layered n)) (hne : gs ≠ []) (h : ∀ g ∈ gs, NonEmptyGates g) :
      NonEmptyGates (gOr gs)

mutual
theorem AltO_NonEmptyGates : ∀ {k : ℕ} {C : Layered n}, AltO k C → NonEmptyGates C
  | _, _, AltO.dnf cs => NonEmptyGates.dnf cs
  | _, _, AltO.gOr _ gs hne h =>
      NonEmptyGates.gOr gs hne (fun g hg => AltA_NonEmptyGates (h g hg))
theorem AltA_NonEmptyGates : ∀ {k : ℕ} {C : Layered n}, AltA k C → NonEmptyGates C
  | _, _, AltA.cnf cs => NonEmptyGates.cnf cs
  | _, _, AltA.gAnd _ gs hne h =>
      NonEmptyGates.gAnd gs hne (fun g hg => AltO_NonEmptyGates (h g hg))
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.AltO_NonEmptyGates
