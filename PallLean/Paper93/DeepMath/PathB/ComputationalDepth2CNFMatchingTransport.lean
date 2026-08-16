import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFFinalDispatcher
import Mathlib.Data.Fintype.EquivFin

/-!
# Transporting an arbitrary large matching to private-pair coordinates

The large-matching semantics were proved on canonical coordinates `MatchVar m r`.  This file proves that the choice
of coordinates is immaterial.  Any finite variable type of cardinality `2m+r` is equivalent to the canonical type;
assignments transport in both directions, matched-clause satisfaction is preserved by definition, and the exact
`3^m·2^r` branch enumeration transfers back.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingTransport

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoCNFLargeMatchingSemantics

variable {V : Type*} [Fintype V]

/-- Canonical private-pair coordinates exist from the cardinal decomposition alone. -/
noncomputable def coordinateEquiv (m r : ℕ) (hcard : Fintype.card V = 2 * m + r) :
    V ≃ MatchVar m r :=
  Fintype.equivOfCardEq (by simpa [MatchVar, Nat.mul_comm] using hcard)

/-- Rename an arbitrary assignment into canonical matching coordinates. -/
def toCanonical {m r : ℕ} (rename : V ≃ MatchVar m r) (x : V → Bool) : MatchVar m r → Bool :=
  fun v => x (rename.symm v)

/-- Rename a canonical assignment back to the original variable type. -/
def fromCanonical {m r : ℕ} (rename : V ≃ MatchVar m r) (x : MatchVar m r → Bool) : V → Bool :=
  fun v => x (rename v)

theorem fromCanonical_toCanonical {m r : ℕ} (rename : V ≃ MatchVar m r) (x : V → Bool) :
    fromCanonical rename (toCanonical rename x) = x := by
  funext v
  simp [fromCanonical, toCanonical]

theorem toCanonical_fromCanonical {m r : ℕ} (rename : V ≃ MatchVar m r)
    (x : MatchVar m r → Bool) : toCanonical rename (fromCanonical rename x) = x := by
  funext v
  simp [fromCanonical, toCanonical]

/-- Signed matched-clause semantics transported to arbitrary variables. -/
def evalTransportedMatchedClause {m r : ℕ} (rename : V ≃ MatchVar m r)
    (signs : Fin m → Bool × Bool) (x : V → Bool) (i : Fin m) : Prop :=
  evalMatchedClause signs (toCanonical rename x) i

/-- Decode a canonical branch directly as an assignment on the original variables. -/
def transportedAssignmentOfBranch {m r : ℕ} (rename : V ≃ MatchVar m r)
    {signs : Fin m → Bool × Bool} (branch : MatchingBranch signs r) : V → Bool :=
  fromCanonical rename (assignmentOfBranch branch)

theorem transportedAssignment_satisfies {m r : ℕ} (rename : V ≃ MatchVar m r)
    {signs : Fin m → Bool × Bool} (branch : MatchingBranch signs r) (i : Fin m) :
    evalTransportedMatchedClause rename signs (transportedAssignmentOfBranch rename branch) i := by
  simpa [evalTransportedMatchedClause, transportedAssignmentOfBranch, toCanonical_fromCanonical] using
    assignmentOfBranch_satisfies branch i

/-- Every satisfying assignment on arbitrary variables is recovered by a canonical branch after renaming. -/
theorem transported_assignment_recovered {m r : ℕ} (rename : V ≃ MatchVar m r)
    (signs : Fin m → Bool × Bool) (x : V → Bool)
    (hx : ∀ i, evalTransportedMatchedClause rename signs x i) :
    transportedAssignmentOfBranch rename
      (branchOfAssignment signs (toCanonical rename x) hx) = x := by
  unfold transportedAssignmentOfBranch
  rw [assignmentOfBranch_branchOfAssignment, fromCanonical_toCanonical]

/-- The transported branch family retains the exact canonical count. -/
theorem transported_branch_count {m : ℕ} (signs : Fin m → Bool × Bool) (r : ℕ) :
    Fintype.card (MatchingBranch signs r) = 3 ^ m * 2 ^ r := card_matchingBranch signs r

end PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingTransport

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingTransport.coordinateEquiv
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingTransport.transported_assignment_recovered
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingTransport.transported_branch_count
