import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicPACAttempt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedTargets
import PallLean.Paper93.DeepMath.PathB.NFrameVariationalAmplituhedronBridge

/-
# N-frame Lagrangian PAC invariant

`ComputationalDepthHolographicPACAttempt` used an arbitrary
`FrameLagrangian.action`, so the low-action obstruction could be vacuous: choose
an action/bound with no low-action reconstruction at all.

This file replaces that with a non-vacuous invariant based on the actual
N-frame log-det Lagrangian from `NFrameVariationalAmplituhedronBridge`:

  `logDetNFrameAction α β λ E χ Φ 𝒥 A`.

The invariant carries an identity/reference low-action witness, so the
obstruction is no longer "there are no low-action bulk objects."  The only
allowed obstruction is the SAT-faithful one:

  no low-action N-frame PAC reconstruction that tracks a real machine output
  satisfying the formula.

That is still a conditional lower-bound socket, not a proof of P vs NP.  The
point is to remove the degenerate arbitrary-action escape and make the remaining
PAC/holographic theorem land on the paper's N-frame Lagrangian.
-/

namespace SATDepthMachine

/-! ## N-frame PAC boundary and bulk data -/

/-- Boundary data for a PAC/holographic reconstruction, now carrying the actual
N-frame fields used by the paper's Lagrangian: local edge set, parity labels,
phase field, and selected principal-minor family. -/
structure NFramePACBoundary (dim : Nat) where
  sampleBudget : Nat
  observableCode : Nat
  edgeSet : Finset (Fin dim × Fin dim)
  parityLabels : Fin dim -> Int
  phaseField : Fin dim -> Real
  principalFamily : Finset (Finset (Fin dim))

/-- Bulk data reconstructed from the boundary: a coded reconstruction plus the
matrix `A` on which the N-frame log-det action is evaluated. -/
structure NFramePACBulk (dim : Nat) where
  reconstructionCode : Nat
  descriptionLength : Nat
  matrix : Matrix (Fin dim) (Fin dim) Real

/-- The identity/reference bulk object.  This is used to certify that the
low-action side of an invariant is nonempty, so the obstruction cannot be a
trivial empty-domain obstruction. -/
def NFramePACBulk.identity (dim : Nat) : NFramePACBulk dim where
  reconstructionCode := 0
  descriptionLength := 0
  matrix := 1

/-! ## The actual N-frame Lagrangian invariant -/

/-- The paper-faithful PAC action: not an arbitrary function, but the real
log-det N-frame action already formalized for the variational route. -/
noncomputable def nFramePACLogDetAction
    {dim : Nat}
    (alpha beta lam : Real)
    (boundary : NFramePACBoundary dim)
    (bulk : NFramePACBulk dim) : Real :=
  PallLean.Paper93.DeepMath.PathB.logDetNFrameAction alpha beta lam
    boundary.edgeSet
    boundary.parityLabels
    boundary.phaseField
    boundary.principalFamily
    bulk.matrix

/-- A non-vacuous N-frame/PAC invariant.

The `identity_low_action` field rules out the degenerate move that made the
previous holographic PAC socket too weak: the invariant must include at least one
low-action bulk object, namely the identity/reference bulk.  Any obstruction
must therefore target SAT-faithful reconstructions, not all reconstructions. -/
structure NFrameLagrangianPACInvariant where
  dim : Nat
  alpha : Real
  beta : Real
  lam : Real
  actionBound : Real
  boundary : NFramePACBoundary dim
  lam_pos : 0 < lam
  identity_low_action :
    nFramePACLogDetAction alpha beta lam boundary
      (NFramePACBulk.identity dim) <= actionBound

/-- Evaluate the invariant on a reconstructed bulk object. -/
noncomputable def NFrameLagrangianPACInvariant.action
    (I : NFrameLagrangianPACInvariant)
    (bulk : NFramePACBulk I.dim) : Real :=
  nFramePACLogDetAction I.alpha I.beta I.lam I.boundary bulk

/-- The action is definitionally the paper's log-det N-frame action. -/
theorem nFrameLagrangianPACInvariant_action_eq_logDet
    (I : NFrameLagrangianPACInvariant)
    (bulk : NFramePACBulk I.dim) :
    I.action bulk =
      PallLean.Paper93.DeepMath.PathB.logDetNFrameAction I.alpha I.beta I.lam
        I.boundary.edgeSet
        I.boundary.parityLabels
        I.boundary.phaseField
        I.boundary.principalFamily
        bulk.matrix := rfl

/-- Non-vacuity: every admissible invariant has at least one low-action bulk
object.  Hence the meaningful obstruction cannot be `no low-action bulk exists`.
-/
theorem exists_lowActionBulk_of_nFrameLagrangianPACInvariant
    (I : NFrameLagrangianPACInvariant) :
    ∃ bulk : NFramePACBulk I.dim, I.action bulk <= I.actionBound :=
  ⟨NFramePACBulk.identity I.dim, I.identity_low_action⟩

/-! ## SAT-faithful low-action reconstruction -/

/-- A SAT-faithful low-action reconstruction.

This is the non-vacuous target: the low-action bulk must track the actual code
and description length of the search machine, and the machine must output a
real satisfying assignment for the formula. -/
structure SATFaithfulNFramePACReconstruction
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF) where
  bulk : NFramePACBulk I.dim
  low_action : I.action bulk <= I.actionBound
  witness : RawAssignment
  machine_outputs :
    D.surface.toMachineModel.searchRun M.code phi = some witness
  witness_satisfies : Satisfies phi witness
  reconstruction_uses_machine_code :
    bulk.reconstructionCode = M.code
  description_tracks_code :
    bulk.descriptionLength = D.programLength M.code

/-- The obstruction now forbids only SAT-faithful low-action reconstructions,
not all low-action N-frame bulk objects. -/
def NoSATFaithfulNFramePACReconstruction
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF) : Prop :=
  ¬ Nonempty (SATFaithfulNFramePACReconstruction D I M phi)

/-! ## Non-vacuous transport package -/

/-- The N-frame/PAC breakthrough target after removing the vacuous-action
escape.

`transport` says a complete polynomial-time SAT search machine yields a
SAT-faithful low-action reconstruction for some satisfiable formula.

`obstruction` says no such SAT-faithful low-action reconstruction exists.

The invariant itself is non-vacuous by
`exists_lowActionBulk_of_nFrameLagrangianPACInvariant`, so this cannot be closed
by choosing a degenerate action/bound with an empty low-action domain. -/
structure NFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant) : Prop where
  transport :
    ∀ M : SearchMachine D.surface.toMachineModel,
      SearchCorrect D.surface.toMachineModel M ->
        ∃ phi : CNF,
          Satisfiable phi ∧
            Nonempty (SATFaithfulNFramePACReconstruction D I M phi)
  obstruction :
    ∀ M : SearchMachine D.surface.toMachineModel,
      ∀ phi : CNF,
        Satisfiable phi ->
          NoSATFaithfulNFramePACReconstruction D I M phi
  avoids_largeness : AvoidsNaturalProofLargeness D

/-- The breakthrough package rules out every complete canonical search machine.
-/
theorem forall_not_searchCorrect_of_nFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (h : NFramePACLagrangianBreakthrough D I) :
    ∀ M : SearchMachine D.surface.toMachineModel,
      ¬ SearchCorrect D.surface.toMachineModel M := by
  intro M hcorrect
  rcases h.transport M hcorrect with ⟨phi, hsat, hrec⟩
  exact h.obstruction M phi hsat hrec

/-- Therefore the non-vacuous N-frame/PAC breakthrough gives canonical deep SAT
search. -/
theorem canonicalDeepSATSearch_of_nFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (h : NFramePACLagrangianBreakthrough D I) :
    CanonicalDeepSATSearch D.surface :=
  (canonicalDeepSATSearch_iff_forall_not_searchCorrect D.surface).mpr
    (forall_not_searchCorrect_of_nFramePACLagrangianBreakthrough D I h)

/-- Conditional closure to no canonical polynomial-time SAT decision. -/
theorem noCanonicalSATDecisionInP_of_nFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (h : NFramePACLagrangianBreakthrough D I) :
    ¬ CanonicalSATDecisionInP D.surface :=
  canonicalNoDecider_of_deepSATSearch D.surface
    (canonicalDeepSATSearch_of_nFramePACLagrangianBreakthrough D I h)

/-- Conditional closure to the hard metacomplexity socket. -/
theorem hardMetacomplexitySocket_of_nFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (h : NFramePACLagrangianBreakthrough D I) :
    HardMetacomplexitySocket D :=
  hardMetacomplexitySocket_of_noCanonicalSATDecisionInP D
    (noCanonicalSATDecisionInP_of_nFramePACLagrangianBreakthrough D I h)

/-- The N-frame/PAC breakthrough induces the earlier non-natural PAC socket, but
the load-bearing content is now pinned to an actual log-det N-frame invariant.
-/
def nonNaturalPACLearnerTransport_of_nFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (h : NFramePACLagrangianBreakthrough D I) :
    NonNaturalPACLearnerTransport D where
  not_standard_natural := by
    intro hs
    exact hs
  not_circular_sat_learning := by
    intro hs
    exact hs
  avoids_largeness := h.avoids_largeness
  useful_transport :=
    hardMetacomplexitySocket_of_nFramePACLagrangianBreakthrough D I h

/-- Full conditional route closure from the non-vacuous N-frame/PAC invariant
package. -/
theorem ktRoute_finalClosure_of_nFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (h : NFramePACLagrangianBreakthrough D I) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardMetacomplexitySocket_of_nFramePACLagrangianBreakthrough D I h)

/-- Concrete existential form of the remaining N-frame/PAC theorem.  This is
still conditional: constructing the invariant and the breakthrough package is
the actual lower-bound problem. -/
def ConcreteNFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface) : Prop :=
  ∃ I : NFrameLagrangianPACInvariant,
    NFramePACLagrangianBreakthrough D I

/-- Existential breakthrough closure. -/
theorem ktRoute_finalClosure_of_concreteNFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (h : ConcreteNFramePACLagrangianBreakthrough D) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D := by
  rcases h with ⟨I, hI⟩
  exact ktRoute_finalClosure_of_nFramePACLagrangianBreakthrough D I hI

/-! ## Guard: the full breakthrough is P-vs-NP strength -/

/-- Concrete N-frame/PAC breakthrough implies no canonical polynomial-time SAT
decision.  This is the explicit guard theorem: the full breakthrough is not a
smaller lemma. -/
theorem noCanonicalSATDecisionInP_of_concreteNFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (h : ConcreteNFramePACLagrangianBreakthrough D) :
    ¬ CanonicalSATDecisionInP D.surface := by
  rcases h with ⟨I, hI⟩
  exact noCanonicalSATDecisionInP_of_nFramePACLagrangianBreakthrough D I hI

/-- Therefore any canonical SAT decider refutes the claimed concrete
N-frame/PAC breakthrough package. -/
theorem not_concreteNFramePACLagrangianBreakthrough_of_canonicalSATDecisionInP
    (D : DescribedCanonicalSurface)
    (hdec : CanonicalSATDecisionInP D.surface) :
    ¬ ConcreteNFramePACLagrangianBreakthrough D := by
  intro hbreak
  exact (noCanonicalSATDecisionInP_of_concreteNFramePACLagrangianBreakthrough
    D hbreak) hdec

/-- Named guard predicate for paper-facing statements. -/
def NFramePACLagrangianBreakthroughIsPneqNPStrength
    (D : DescribedCanonicalSurface) : Prop :=
  ConcreteNFramePACLagrangianBreakthrough D ->
    ¬ CanonicalSATDecisionInP D.surface

/-- The guard predicate holds by the closure theorem above. -/
theorem nFramePACLagrangianBreakthrough_is_pneqnp_strength
    (D : DescribedCanonicalSurface) :
    NFramePACLagrangianBreakthroughIsPneqNPStrength D :=
  noCanonicalSATDecisionInP_of_concreteNFramePACLagrangianBreakthrough D

/-! ## Restricted SAT-faithful reconstruction tests -/

/-- Search machines whose run never outputs on a restricted formula class. -/
def NoOutputOnRestrictedClass
    (D : DescribedCanonicalSurface)
    (R : CNF -> Prop)
    (M : SearchMachine D.surface.toMachineModel) : Prop :=
  ∀ phi : CNF, R phi ->
    D.surface.toMachineModel.searchRun M.code phi = none

/-- The low-action bulk associated to a machine code.  This is the admissibility
side needed to build a SAT-faithful reconstruction from an actual machine output
without choosing a degenerate arbitrary action. -/
structure MachineLowActionCodeBulk
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel) where
  bulk : NFramePACBulk I.dim
  low_action : I.action bulk <= I.actionBound
  reconstruction_uses_machine_code :
    bulk.reconstructionCode = M.code
  description_tracks_code :
    bulk.descriptionLength = D.programLength M.code

/-- A deliberately weak restricted model: the machine never outputs on `R`, but
its code still has a low-action N-frame/PAC bulk representation. -/
def NoOutputLowActionMachineClass
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (R : CNF -> Prop)
    (M : SearchMachine D.surface.toMachineModel) : Prop :=
  NoOutputOnRestrictedClass D R M ∧
    Nonempty (MachineLowActionCodeBulk D I M)

/-- No-output machines cannot have SAT-faithful N-frame/PAC reconstructions on
the restricted class.  This is the first real restricted obstruction. -/
theorem noSATFaithfulNFramePACReconstruction_of_noOutputOnRestrictedClass
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (R : CNF -> Prop)
    (M : SearchMachine D.surface.toMachineModel)
    {phi : CNF}
    (hno : NoOutputOnRestrictedClass D R M)
    (hR : R phi) :
    NoSATFaithfulNFramePACReconstruction D I M phi := by
  intro hrec
  rcases hrec with ⟨rec⟩
  have hnone := hno phi hR
  have hsome : none = some rec.witness := by
    simpa [hnone] using rec.machine_outputs
  cases hsome

/-- If a restricted-correct machine has a low-action code bulk, then every
satisfiable restricted instance gives a SAT-faithful reconstruction. -/
theorem satFaithfulNFramePACReconstruction_of_restrictedCorrect
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (R : CNF -> Prop)
    (M : SearchMachine D.surface.toMachineModel)
    (hlow : MachineLowActionCodeBulk D I M)
    (hcorrect : RestrictedSearchCorrect D.surface.toMachineModel R M)
    {phi : CNF}
    (hR : R phi)
    (hsat : Satisfiable phi) :
    Nonempty (SATFaithfulNFramePACReconstruction D I M phi) := by
  rcases hcorrect phi hR hsat with ⟨a, hrun, hsatisfies⟩
  exact ⟨{
    bulk := hlow.bulk
    low_action := hlow.low_action
    witness := a
    machine_outputs := hrun
    witness_satisfies := hsatisfies
    reconstruction_uses_machine_code :=
      hlow.reconstruction_uses_machine_code
    description_tracks_code :=
      hlow.description_tracks_code
  }⟩

/-! ## Restricted breakthrough surface -/

/-- Restricted N-frame/PAC breakthrough for a machine class.

This is the bounded-model analogue of the full breakthrough: transport from
restricted correctness to a SAT-faithful reconstruction, plus an obstruction
against such reconstructions for machines in the class. -/
structure RestrictedNFramePACLagrangianBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (R : CNF -> Prop)
    (MachineClass : SearchMachine D.surface.toMachineModel -> Prop) : Prop where
  transport :
    ∀ M : SearchMachine D.surface.toMachineModel,
      MachineClass M ->
        RestrictedSearchCorrect D.surface.toMachineModel R M ->
          ∃ phi : CNF,
            R phi ∧ Satisfiable phi ∧
              Nonempty (SATFaithfulNFramePACReconstruction D I M phi)
  obstruction :
    ∀ M : SearchMachine D.surface.toMachineModel,
      MachineClass M ->
        ∀ phi : CNF,
          R phi ->
            Satisfiable phi ->
              NoSATFaithfulNFramePACReconstruction D I M phi

/-- Restricted shallow search inside a chosen machine class. -/
def RestrictedShallowSearchInClass
    (D : DescribedCanonicalSurface)
    (R : CNF -> Prop)
    (MachineClass : SearchMachine D.surface.toMachineModel -> Prop) : Prop :=
  ∃ M : SearchMachine D.surface.toMachineModel,
    MachineClass M ∧
      RestrictedSearchCorrect D.surface.toMachineModel R M

/-- A restricted breakthrough rules out restricted shallow search inside the
chosen machine class. -/
theorem noRestrictedShallowSearchInClass_of_restrictedNFramePACBreakthrough
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (R : CNF -> Prop)
    (MachineClass : SearchMachine D.surface.toMachineModel -> Prop)
    (h : RestrictedNFramePACLagrangianBreakthrough D I R MachineClass) :
    ¬ RestrictedShallowSearchInClass D R MachineClass := by
  intro hshallow
  rcases hshallow with ⟨M, hclass, hcorrect⟩
  rcases h.transport M hclass hcorrect with ⟨phi, hR, hsat, hrec⟩
  exact h.obstruction M hclass phi hR hsat hrec

/-! ## The first provable restricted instance -/

/-- The no-output/low-action machine class satisfies the restricted
N-frame/PAC breakthrough whenever the restricted formula class contains at least
one satisfiable instance.

This is intentionally weak, but non-vacuous: the obstruction is proved from the
machine semantics (`searchRun = none`), while transport uses restricted
correctness and the low-action code bulk. -/
theorem restrictedBreakthrough_of_noOutputLowActionMachineClass
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (R : CNF -> Prop)
    (hinstance : ∃ phi : CNF, R phi ∧ Satisfiable phi) :
    RestrictedNFramePACLagrangianBreakthrough D I R
      (NoOutputLowActionMachineClass D I R) where
  transport := by
    intro M hclass hcorrect
    rcases hinstance with ⟨phi, hR, hsat⟩
    exact ⟨phi, hR, hsat,
      satFaithfulNFramePACReconstruction_of_restrictedCorrect
        D I R M (Classical.choice hclass.2) hcorrect hR hsat⟩
  obstruction := by
    intro M hclass phi hR _hsat
    exact noSATFaithfulNFramePACReconstruction_of_noOutputOnRestrictedClass
      D I R M hclass.1 hR

/-- Concrete restricted conclusion for the first weak model: no no-output
low-action machine can be restricted-correct on a nonempty satisfiable class. -/
theorem noRestrictedCorrect_noOutputLowActionMachines
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (R : CNF -> Prop)
    (hinstance : ∃ phi : CNF, R phi ∧ Satisfiable phi) :
    ¬ RestrictedShallowSearchInClass D R
      (NoOutputLowActionMachineClass D I R) :=
  noRestrictedShallowSearchInClass_of_restrictedNFramePACBreakthrough
    D I R (NoOutputLowActionMachineClass D I R)
    (restrictedBreakthrough_of_noOutputLowActionMachineClass D I R hinstance)

/-! ## Axiom trace -/

#print axioms nFrameLagrangianPACInvariant_action_eq_logDet
#print axioms exists_lowActionBulk_of_nFrameLagrangianPACInvariant
#print axioms forall_not_searchCorrect_of_nFramePACLagrangianBreakthrough
#print axioms canonicalDeepSATSearch_of_nFramePACLagrangianBreakthrough
#print axioms noCanonicalSATDecisionInP_of_nFramePACLagrangianBreakthrough
#print axioms hardMetacomplexitySocket_of_nFramePACLagrangianBreakthrough
#print axioms nonNaturalPACLearnerTransport_of_nFramePACLagrangianBreakthrough
#print axioms ktRoute_finalClosure_of_nFramePACLagrangianBreakthrough
#print axioms ktRoute_finalClosure_of_concreteNFramePACLagrangianBreakthrough
#print axioms noCanonicalSATDecisionInP_of_concreteNFramePACLagrangianBreakthrough
#print axioms not_concreteNFramePACLagrangianBreakthrough_of_canonicalSATDecisionInP
#print axioms nFramePACLagrangianBreakthrough_is_pneqnp_strength
#print axioms noSATFaithfulNFramePACReconstruction_of_noOutputOnRestrictedClass
#print axioms satFaithfulNFramePACReconstruction_of_restrictedCorrect
#print axioms noRestrictedShallowSearchInClass_of_restrictedNFramePACBreakthrough
#print axioms restrictedBreakthrough_of_noOutputLowActionMachineClass
#print axioms noRestrictedCorrect_noOutputLowActionMachines

end SATDepthMachine
