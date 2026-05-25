import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicPACAttempt
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

end SATDepthMachine
