import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinCommunicationMatrix

/-
# Communication-to-poly-time bridge

This file isolates the exact bridge that would make the communication route
touch polynomial-time SAT search.

The proved communication lower bound has the form

  equality minor -> every indexed 1-cover has length at least `minorSize`.

To affect a polynomial-time search machine, one still has to construct the
opposite side from the machine's actual run:

  if the machine outputs a satisfying witness, its transcript induces an
  indexed 1-cover of length smaller than `minorSize`.

That transcript-to-cover implication is the hard mathematical bridge.  This
file does not assert it globally.  It packages it as a concrete certificate and
proves the downstream consequences:

* one certificate blocks one search machine on one satisfiable formula;
* certificates for every canonical search machine imply the final expanded
  lower-bound target;
* a Cook-Levin-family version recovers the existing route closure.
-/

namespace SATDepthMachine

/-! ## Machine-level communication certificates -/

/-- A communication certificate attached directly to one canonical search
machine on one satisfiable CNF.

The `small_if_output` field is the load-bearing transcript-to-cover theorem:
from an actual satisfying output by the machine, construct a too-small indexed
1-cover of an equality minor in the clause/assignment matrix.  The rectangle
lower bound then contradicts it.
-/
structure MachineInducedClauseAssignmentCover
    (C : CanonicalMachineSurface)
    (M : SearchMachine C.toMachineModel)
    (φ : CNF)
    (minorSize : Nat) where
  satisfiable : Satisfiable φ
  assignments : List RawAssignment
  minor : ClauseAssignmentEqualityMinor φ assignments minorSize
  cover : ClauseAssignmentMinorIndexedCover φ assignments minorSize minor
  small_if_output :
    (∃ a : RawAssignment,
      C.toMachineModel.searchRun M.code φ = some a ∧ Satisfies φ a) ->
      cover.cover.length < minorSize

/-- A machine-level communication certificate blocks satisfying output by the
machine on that formula. -/
theorem no_output_of_machineInducedClauseAssignmentCover
    (C : CanonicalMachineSurface)
    (M : SearchMachine C.toMachineModel)
    {φ : CNF} {minorSize : Nat}
    (H : MachineInducedClauseAssignmentCover C M φ minorSize) :
    ¬ ∃ a : RawAssignment,
      C.toMachineModel.searchRun M.code φ = some a ∧ Satisfies φ a := by
  intro hout
  have hLower : minorSize ≤ H.cover.cover.length :=
    clauseAssignmentEqualityMinor_indexedCover_lowerBound H.cover
  exact Nat.not_lt_of_ge hLower (H.small_if_output hout)

/-- One machine-level certificate gives the expanded final-target failure
predicate for that search machine. -/
theorem searchMachineFailsOnSomeSAT_of_machineInducedClauseAssignmentCover
    (C : CanonicalMachineSurface)
    (M : SearchMachine C.toMachineModel)
    {φ : CNF} {minorSize : Nat}
    (H : MachineInducedClauseAssignmentCover C M φ minorSize) :
    SearchMachineFailsOnSomeSAT C M :=
  ⟨φ, H.satisfiable,
    no_output_of_machineInducedClauseAssignmentCover C M H⟩

/-! ## Universal communication-to-poly-time bridge -/

/-- The direct communication-to-poly-time bridge.

This is the exact theorem the communication route would need: every canonical
polynomial-time search machine has some satisfiable formula whose actual run
induces a too-small communication cover against a proved equality-minor lower
bound.
-/
def UniversalCommunicationToPolyTimeBridge
    (C : CanonicalMachineSurface) : Prop :=
  ∀ M : SearchMachine C.toMachineModel,
    ∃ (φ : CNF) (minorSize : Nat),
      Nonempty (MachineInducedClauseAssignmentCover C M φ minorSize)

/-- The universal communication bridge proves the expanded final lower-bound
target: every canonical search machine fails on some satisfiable CNF. -/
theorem forall_searchMachineFails_of_universalCommunicationBridge
    (C : CanonicalMachineSurface)
    (h : UniversalCommunicationToPolyTimeBridge C) :
    ∀ M : SearchMachine C.toMachineModel,
      SearchMachineFailsOnSomeSAT C M := by
  intro M
  rcases h M with ⟨φ, minorSize, hcover⟩
  exact searchMachineFailsOnSomeSAT_of_machineInducedClauseAssignmentCover
    C M (Classical.choice hcover)

/-- If the communication-to-poly-time bridge is proved, the canonical SAT
decision lower bound follows through the already established final target. -/
theorem noCanonicalSATDecisionInP_of_universalCommunicationBridge
    (C : CanonicalMachineSurface)
    (h : UniversalCommunicationToPolyTimeBridge C) :
    ¬ CanonicalSATDecisionInP C :=
  noCanonicalSATDecisionInP_of_forall_searchMachineFails C
    (forall_searchMachineFails_of_universalCommunicationBridge C h)

/-- Self-hosted version of the same bridge closure. -/
theorem noSelfHostedIntendedSATDecisionInP_of_universalCommunicationBridge
    (C : CanonicalMachineSurface)
    (h : UniversalCommunicationToPolyTimeBridge C) :
    ¬ UniversalIntendedSATDecisionInP
      (selfHostedUniversalCanonicalSurface C) :=
  noSelfHostedIntendedSATDecisionInP_of_forall_searchMachineFails C
    (forall_searchMachineFails_of_universalCommunicationBridge C h)

/-! ## Cook-Levin-family specialization -/

/-- A family-specialized bridge: every canonical search machine has a
communication certificate on some member of the chosen Cook-Levin family. -/
def CookLevinFamilyCommunicationToPolyTimeBridge
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily) : Prop :=
  ∀ M : SearchMachine D.surface.toMachineModel,
    ∃ (n minorSize : Nat),
      Nonempty
        (MachineInducedClauseAssignmentCover D.surface M (F.formula n)
          minorSize)

/-- A Cook-Levin-family bridge is a direct universal communication bridge. -/
theorem universalCommunicationBridge_of_CookLevinFamilyBridge
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinFamilyCommunicationToPolyTimeBridge D F) :
    UniversalCommunicationToPolyTimeBridge D.surface := by
  intro M
  rcases h M with ⟨n, minorSize, hcover⟩
  exact ⟨F.formula n, minorSize, hcover⟩

/-- Cook-Levin-family communication-to-poly-time bridge closes the canonical
SAT decision target. -/
theorem noCanonicalSATDecisionInP_of_CookLevinFamilyCommunicationBridge
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinFamilyCommunicationToPolyTimeBridge D F) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_universalCommunicationBridge D.surface
    (universalCommunicationBridge_of_CookLevinFamilyBridge D F h)

/-- Convert the existing generator-induced Cook-Levin cover certificate into
the new machine-level bridge certificate. -/
def machineCover_of_generatorInducedClauseAssignmentCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    {n minorSize : Nat}
    (H : GeneratorInducedClauseAssignmentCover D F L G n minorSize) :
    MachineInducedClauseAssignmentCover D.surface G.machine
      (F.formula n) minorSize where
  satisfiable := F.satisfiable n
  assignments := H.profile.assignments
  minor := H.profile.minor
  cover := H.cover
  small_if_output := H.small_if_witness

/-- The existing clause/assignment-matrix obstruction is strong enough to supply
the family-specialized machine bridge, by viewing each search machine as a
short-fast generator at its own code length. -/
theorem CookLevinFamilyBridge_of_clauseAssignmentMatrixObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinClauseAssignmentMatrixObstruction D F) :
    CookLevinFamilyCommunicationToPolyTimeBridge D F := by
  intro M
  let L := D.programLength M.code
  let G : ShortFastCandidateGenerator D.toDescriptionMachineModel L :=
    shortFastGenerator_of_searchMachine D.toDescriptionMachineModel M
  rcases h L G with ⟨n, minorSize, hcover⟩
  refine ⟨n, minorSize, ?_⟩
  exact ⟨machineCover_of_generatorInducedClauseAssignmentCover D F L G
    (Classical.choice hcover)⟩

/-- Re-express the previous closure through the explicit machine-level
communication-to-poly-time bridge. -/
theorem noCanonicalSATDecisionInP_of_clauseAssignmentMatrixObstruction_viaBridge
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinClauseAssignmentMatrixObstruction D F) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_CookLevinFamilyCommunicationBridge D F
    (CookLevinFamilyBridge_of_clauseAssignmentMatrixObstruction D F h)

/-! ## Axiom trace -/

#print axioms no_output_of_machineInducedClauseAssignmentCover
#print axioms searchMachineFailsOnSomeSAT_of_machineInducedClauseAssignmentCover
#print axioms forall_searchMachineFails_of_universalCommunicationBridge
#print axioms noCanonicalSATDecisionInP_of_universalCommunicationBridge
#print axioms noSelfHostedIntendedSATDecisionInP_of_universalCommunicationBridge
#print axioms universalCommunicationBridge_of_CookLevinFamilyBridge
#print axioms noCanonicalSATDecisionInP_of_CookLevinFamilyCommunicationBridge
#print axioms CookLevinFamilyBridge_of_clauseAssignmentMatrixObstruction
#print axioms noCanonicalSATDecisionInP_of_clauseAssignmentMatrixObstruction_viaBridge

end SATDepthMachine
