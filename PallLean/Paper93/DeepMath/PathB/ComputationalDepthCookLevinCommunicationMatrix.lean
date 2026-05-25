import PallLean.Paper93.DeepMath.PathB.ComputationalDepthToyRectangleLowerBounds

/-
# CNF-derived Cook-Levin communication matrix

This file replaces the pure toy equality matrix with a matrix built from an
actual CNF formula:

  rows    = clauses of the formula;
  columns = a finite list of candidate assignments;
  entry   = whether that assignment satisfies that clause.

For a Cook-Levin family, this gives the concrete communication matrix shape for
family member `F.formula n`.  The real lower-bound obligation is now an explicit
minor certificate: the clause/assignment matrix contains an equality/identity
minor.  Once such a minor is proved for a family, the same rectangle lower-bound
argument from the toy model transfers.

No Cook-Levin lower bound is asserted here.  The file proves the bridge:

  equality minor in the CNF clause/assignment matrix
  + generator-induced too-small cover
  -> Cook-Levin communication obstruction
  -> hard metacomplexity socket / route closure.
-/

namespace SATDepthMachine

/-! ## CNF clause/assignment communication matrix -/

/-- Evaluate a clause against an assignment.  This is the same Boolean used by
CNF evaluation, exposed as the entry predicate for the communication matrix. -/
def ClauseSatisfiedByAssignment (c : Clause) (a : RawAssignment) : Bool :=
  Clause.eval a c

/-- The concrete clause/assignment communication matrix of a CNF formula against
a finite candidate-assignment list. -/
def ClauseAssignmentMatrix
    (φ : CNF) (assignments : List RawAssignment) :
    BoolMatrix φ.clauses.length assignments.length :=
  fun ci aj =>
    ClauseSatisfiedByAssignment (φ.clauses.get ci) (assignments.get aj)

/-- A 1-rectangle in the concrete clause/assignment matrix. -/
abbrev ClauseAssignmentOneRectangle
    (φ : CNF) (assignments : List RawAssignment)
    (R : Rectangle φ.clauses.length assignments.length) : Prop :=
  OneRectangle (ClauseAssignmentMatrix φ assignments) R

/-! ## Equality minor certificates -/

/-- An equality/identity minor inside a CNF clause/assignment matrix.

`rowPick i` chooses the clause playing row `i`; `colPick j` chooses the candidate
assignment playing column `j`.  The `minor_eq` field says the selected submatrix
is exactly equality. -/
structure ClauseAssignmentEqualityMinor
    (φ : CNF) (assignments : List RawAssignment) (n : Nat) where
  rowPick : Fin n -> Fin φ.clauses.length
  colPick : Fin n -> Fin assignments.length
  minor_eq : ∀ i j : Fin n,
    ClauseAssignmentMatrix φ assignments (rowPick i) (colPick j) =
      EqualityMatrix n i j

/-- Pull back a rectangle from the CNF clause/assignment matrix to the equality
minor coordinates. -/
def ClauseAssignmentEqualityMinor.pullbackRectangle
    {φ : CNF} {assignments : List RawAssignment} {n : Nat}
    (M : ClauseAssignmentEqualityMinor φ assignments n)
    (R : Rectangle φ.clauses.length assignments.length) : Rectangle n n where
  rowSet := fun i => R.rowSet (M.rowPick i)
  colSet := fun j => R.colSet (M.colPick j)

/-- Pullback preserves containment. -/
theorem ClauseAssignmentEqualityMinor.pullback_contains
    {φ : CNF} {assignments : List RawAssignment} {n : Nat}
    (M : ClauseAssignmentEqualityMinor φ assignments n)
    (R : Rectangle φ.clauses.length assignments.length)
    (i j : Fin n) :
    (M.pullbackRectangle R).Contains i j ↔
      R.Contains (M.rowPick i) (M.colPick j) := by
  rfl

/-- A 1-rectangle in the CNF matrix pulls back to a 1-rectangle in the equality
minor. -/
theorem ClauseAssignmentEqualityMinor.pullback_oneRectangle
    {φ : CNF} {assignments : List RawAssignment} {n : Nat}
    (M : ClauseAssignmentEqualityMinor φ assignments n)
    {R : Rectangle φ.clauses.length assignments.length}
    (hR : OneRectangle (ClauseAssignmentMatrix φ assignments) R) :
    OneRectangle (EqualityMatrix n) (M.pullbackRectangle R) := by
  intro i j hij
  have hcell : R.Contains (M.rowPick i) (M.colPick j) := hij
  have hOne : ClauseAssignmentMatrix φ assignments
      (M.rowPick i) (M.colPick j) = true :=
    hR (M.rowPick i) (M.colPick j) hcell
  rw [M.minor_eq i j] at hOne
  exact hOne

/-! ## Indexed diagonal covers transferred through the minor -/

/-- Indexed cover of the equality-minor diagonal using rectangles from the
ambient CNF clause/assignment matrix. -/
structure ClauseAssignmentMinorIndexedCover
    (φ : CNF) (assignments : List RawAssignment) (n : Nat)
    (M : ClauseAssignmentEqualityMinor φ assignments n) where
  cover : List (Rectangle φ.clauses.length assignments.length)
  one_rectangles : ∀ k : Fin cover.length,
    OneRectangle (ClauseAssignmentMatrix φ assignments) (cover.get k)
  pick : Fin n -> Fin cover.length
  covers_diag : ∀ i : Fin n,
    (cover.get (pick i)).Contains (M.rowPick i) (M.colPick i)

/-- The diagonal-to-ambient-rectangle picker is injective: if the same ambient
1-rectangle covers two selected diagonal minor cells, the equality minor forces
the two indices to be equal. -/
theorem ClauseAssignmentMinorIndexedCover.pick_injective
    {φ : CNF} {assignments : List RawAssignment} {n : Nat}
    {M : ClauseAssignmentEqualityMinor φ assignments n}
    (C : ClauseAssignmentMinorIndexedCover φ assignments n M) :
    Function.Injective C.pick := by
  intro i j hpick
  have hi : (C.cover.get (C.pick i)).Contains (M.rowPick i) (M.colPick i) :=
    C.covers_diag i
  have hj0 : (C.cover.get (C.pick i)).Contains (M.rowPick j) (M.colPick j) := by
    simpa [hpick] using C.covers_diag j
  have hR : OneRectangle (EqualityMatrix n)
      (M.pullbackRectangle (C.cover.get (C.pick i))) :=
    M.pullback_oneRectangle (C.one_rectangles (C.pick i))
  exact eq_of_same_oneRectangle_contains_two_diagonal hR hi hj0

/-- The equality-minor lower bound transfers to the concrete CNF
clause/assignment matrix: any indexed ambient 1-cover of the minor diagonal
needs at least `n` rectangles. -/
theorem clauseAssignmentEqualityMinor_indexedCover_lowerBound
    {φ : CNF} {assignments : List RawAssignment} {n : Nat}
    {M : ClauseAssignmentEqualityMinor φ assignments n}
    (C : ClauseAssignmentMinorIndexedCover φ assignments n M) :
    n ≤ C.cover.length := by
  have hcard := Fintype.card_le_of_injective C.pick C.pick_injective
  simpa [Fintype.card_fin] using hcard

/-! ## Cook-Levin family matrix profiles -/

/-- Concrete communication profile for member `n` of a Cook-Levin family:
finite candidate assignments plus an equality minor in the resulting
clause/assignment matrix. -/
structure CookLevinClauseAssignmentProfile
    (F : CookLevinTraceFamily) (n minorSize : Nat) where
  assignments : List RawAssignment
  minor : ClauseAssignmentEqualityMinor (F.formula n) assignments minorSize

/-- Generator-induced cover of a Cook-Levin clause/assignment equality minor. -/
structure GeneratorInducedClauseAssignmentCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    (n minorSize : Nat) where
  profile : CookLevinClauseAssignmentProfile F n minorSize
  cover : ClauseAssignmentMinorIndexedCover
    (F.formula n) profile.assignments minorSize profile.minor
  small_if_witness :
    (∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a) -> cover.cover.length < minorSize

/-- The transferred equality-minor lower bound blocks witness output. -/
theorem no_witness_of_generatorInducedClauseAssignmentCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    {n minorSize : Nat}
    (C : GeneratorInducedClauseAssignmentCover D F L G n minorSize) :
    ¬ ∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a := by
  intro hwit
  have hLower : minorSize ≤ C.cover.cover.length :=
    clauseAssignmentEqualityMinor_indexedCover_lowerBound C.cover
  exact Nat.not_lt_of_ge hLower (C.small_if_witness hwit)

/-- Convert the concrete clause/assignment-matrix contradiction into the generic
Cook-Levin family obstruction certificate. -/
def familyGeneratorObstruction_of_clauseAssignmentCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    {n minorSize : Nat}
    (C : GeneratorInducedClauseAssignmentCover D F L G n minorSize) :
    FamilyGeneratorObstruction D F L G n where
  measure := 0
  lowerBound := 1
  violatesBound := Nat.zero_lt_one
  blocked := no_witness_of_generatorInducedClauseAssignmentCover D F L G C

/-- Family-level concrete CNF clause/assignment matrix obstruction. -/
def CookLevinClauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      ∃ (n minorSize : Nat),
        Nonempty (GeneratorInducedClauseAssignmentCover D F L G n minorSize)

/-- Concrete clause/assignment matrix obstruction gives the generic Cook-Levin
communication obstruction. -/
theorem CookLevinCommunicationObstruction_of_clauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinClauseAssignmentMatrixObstruction D F) :
    CookLevinCommunicationObstruction D F := by
  intro L G
  rcases h L G with ⟨n, minorSize, hC⟩
  refine ⟨n, ?_⟩
  exact ⟨familyGeneratorObstruction_of_clauseAssignmentCover D F L G
    (Classical.choice hC)⟩

/-- Concrete clause/assignment matrix obstruction implies the hard
metacomplexity socket. -/
theorem hardSocket_of_CookLevinClauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinClauseAssignmentMatrixObstruction D F) :
    HardMetacomplexitySocket D :=
  hardSocket_of_CookLevinCommunicationObstruction D F
    (CookLevinCommunicationObstruction_of_clauseAssignmentMatrixObstruction D F h)

/-- Concrete clause/assignment matrix obstruction closes the route. -/
theorem ktRoute_finalClosure_of_CookLevinClauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinClauseAssignmentMatrixObstruction D F) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardSocket_of_CookLevinClauseAssignmentMatrixObstruction D F h)

/-! ## Axiom trace -/

#print axioms ClauseAssignmentEqualityMinor.pullback_oneRectangle
#print axioms ClauseAssignmentMinorIndexedCover.pick_injective
#print axioms clauseAssignmentEqualityMinor_indexedCover_lowerBound
#print axioms no_witness_of_generatorInducedClauseAssignmentCover
#print axioms CookLevinCommunicationObstruction_of_clauseAssignmentMatrixObstruction
#print axioms hardSocket_of_CookLevinClauseAssignmentMatrixObstruction
#print axioms ktRoute_finalClosure_of_CookLevinClauseAssignmentMatrixObstruction

end SATDepthMachine
