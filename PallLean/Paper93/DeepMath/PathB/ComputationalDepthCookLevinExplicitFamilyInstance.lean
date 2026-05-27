import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinCommunicationMatrix

/-
Explicit Cook-Levin-style family instance with concrete CNFs and concrete
candidate assignments, plus an equality-minor certificate and route wiring.
-/

namespace SATDepthMachine

lemma RawAssignment.lookup_eq_get (a : RawAssignment) (i : Nat) (h : i < a.length) :
    RawAssignment.lookup a i = some (a.get ⟨i, h⟩) := by
  induction a generalizing i with
  | nil => cases h
  | cons b rest ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp [RawAssignment.lookup]
          exact ih i (Nat.succ_lt_succ_iff.mp h)

lemma RawAssignment.lookup_ofFn {n : Nat} (f : Fin n -> Bool) (i : Fin n) :
    RawAssignment.lookup (List.ofFn f) i.val = some (f i) := by
  have h := RawAssignment.lookup_eq_get (List.ofFn f) i.val (by simpa using i.isLt)
  rw [h]
  simp

lemma RawAssignment.lookup_replicate_true {n : Nat} (i : Fin n) :
    RawAssignment.lookup (List.replicate n true) i.val = some true := by
  have h := RawAssignment.lookup_eq_get (List.replicate n true) i.val (by simpa using i.isLt)
  rw [h]
  simp

/-- One positive unit clause. -/
def singletonPosClause (i : Nat) : Clause := [{ var := i, pol := Polarity.pos }]

/-- Explicit trace-style CNF family member at size `n`: clauses `[x_0],...,[x_{n-1}]`. -/
def explicitTraceCNF (n : Nat) : CNF where
  vars := n
  clauses := List.ofFn (fun i : Fin n => singletonPosClause i.val)

/-- Canonical satisfying assignment for `explicitTraceCNF n`. -/
def explicitTraceWitness (n : Nat) : RawAssignment :=
  List.replicate n true

theorem explicitTraceCNF_satisfies_witness (n : Nat) :
    Satisfies (explicitTraceCNF n) (explicitTraceWitness n) := by
  constructor
  · simp [explicitTraceCNF, explicitTraceWitness]
  · simp [explicitTraceCNF, explicitTraceWitness, CNF.eval, singletonPosClause,
      Clause.eval, Lit.eval, RawAssignment.lookup_replicate_true]

theorem explicitTraceCNF_satisfiable (n : Nat) :
    Satisfiable (explicitTraceCNF n) :=
  ⟨explicitTraceWitness n, explicitTraceCNF_satisfies_witness n⟩

/-- Concrete Cook-Levin-style family instance backed by `explicitTraceCNF`. -/
def explicitCookLevinTraceFamily : CookLevinTraceFamily where
  Source := Nat
  source := fun n => n
  timeBound := fun n => n + 1
  formula := explicitTraceCNF
  satisfiable := explicitTraceCNF_satisfiable

/-- Candidate assignments: one-hot vectors `e_0,...,e_{n-1}`. -/
def oneHotAssignment (n : Nat) (j : Fin n) : RawAssignment :=
  List.ofFn (fun i : Fin n => decide (i = j))

/-- Finite candidate list used for the explicit equality-minor certificate. -/
def explicitCandidateAssignments (n : Nat) : List RawAssignment :=
  List.ofFn (fun j : Fin n => oneHotAssignment n j)

/-- On the selected rows/columns, the clause/assignment matrix is exactly equality. -/
theorem explicit_clauseAssignmentMatrix_eq_equality
    (n : Nat) (i j : Fin n) :
    ClauseAssignmentMatrix (explicitTraceCNF n) (explicitCandidateAssignments n)
      ⟨i.val, by simp [explicitTraceCNF, i.isLt]⟩
      ⟨j.val, by simp [explicitCandidateAssignments, j.isLt]⟩
      = EqualityMatrix n i j := by
  simp [ClauseAssignmentMatrix, ClauseSatisfiedByAssignment, explicitTraceCNF,
    explicitCandidateAssignments, oneHotAssignment, singletonPosClause,
    EqualityMatrix, Clause.eval, Lit.eval, RawAssignment.lookup_ofFn]

/-- Concrete equality-minor certificate in the explicit family matrix. -/
def explicitClauseAssignmentEqualityMinor (n : Nat) :
    ClauseAssignmentEqualityMinor
      (explicitTraceCNF n)
      (explicitCandidateAssignments n)
      n where
  rowPick := fun i => ⟨i.val, by simp [explicitTraceCNF, i.isLt]⟩
  colPick := fun j => ⟨j.val, by simp [explicitCandidateAssignments, j.isLt]⟩
  minor_eq := explicit_clauseAssignmentMatrix_eq_equality n

/-- Profile packaging for the explicit family at size `n`. -/
def explicitCookLevinClauseAssignmentProfile (n : Nat) :
    CookLevinClauseAssignmentProfile explicitCookLevinTraceFamily n n where
  assignments := explicitCandidateAssignments n
  minor := explicitClauseAssignmentEqualityMinor n

/--
Concrete route landing theorem on this explicit family:
any generator-induced cover on this family yields a Cook-Levin communication
obstruction via the existing matrix bridge.
-/
theorem explicitCookLevinCommunicationObstruction_of_clauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (h : CookLevinClauseAssignmentMatrixObstruction D explicitCookLevinTraceFamily) :
    CookLevinCommunicationObstruction D explicitCookLevinTraceFamily :=
  CookLevinCommunicationObstruction_of_clauseAssignmentMatrixObstruction
    D explicitCookLevinTraceFamily h

/-- Same landing, phrased directly as the hard socket. -/
theorem hardSocket_of_explicitCookLevinClauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (h : CookLevinClauseAssignmentMatrixObstruction D explicitCookLevinTraceFamily) :
    HardMetacomplexitySocket D :=
  hardSocket_of_CookLevinClauseAssignmentMatrixObstruction
    D explicitCookLevinTraceFamily h

/-- Same landing, phrased as final route closure. -/
theorem ktRoute_finalClosure_of_explicitCookLevinClauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (h : CookLevinClauseAssignmentMatrixObstruction D explicitCookLevinTraceFamily) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure_of_CookLevinClauseAssignmentMatrixObstruction
    D explicitCookLevinTraceFamily h

#print axioms explicitTraceCNF_satisfies_witness
#print axioms explicit_clauseAssignmentMatrix_eq_equality
#print axioms explicitCookLevinCommunicationObstruction_of_clauseAssignmentMatrixObstruction

end SATDepthMachine
