import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicPACAttempt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictedTargets
import PallLean.Paper93.DeepMath.PathB.NFrameVariationalAmplituhedronBridge
import PallLean.Paper93.DeepMath.PathB.WilliamsCompressedCertificateTransport

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

/-- The identity matrix with arbitrary bookkeeping codes attached.

This object is intentionally diagnostic: the current log-det action reads only
the matrix field, so changing `reconstructionCode` and `descriptionLength` does
not change the action. -/
def NFramePACBulk.identityMatrixWithBookkeeping
    (dim code desc : Nat) : NFramePACBulk dim where
  reconstructionCode := code
  descriptionLength := desc
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

/-! ## Gödel/Williams tower transport -/

/-- A resource-bounded Gödel/Williams tower.

This is the formal socket for the book's "Gödel hierarchy tower" idea in the
Williams style: the lower-bound argument must not be a natural property of
truth tables.  It must instead force a forbidden resource-bounded hierarchy
collapse. -/
structure ResourceBoundedGodelWilliamsTower where
  baseSystemCode : Nat
  metaSystemCode : Nat
  diagonalSentenceCode : Nat
  hierarchyCollapse : Prop
  hierarchyNoCollapse : ¬ hierarchyCollapse

/-- A Williams-style non-natural step over a fixed Gödel tower.

The step says that a fast SAT-like procedure, plus a small-representation
hypothesis, plus the meta-simulation needed to climb the tower, would collapse
the hierarchy.  The tower's diagonal theorem then rejects that collapse. -/
structure WilliamsGodelNonNaturalStep
    (T : ResourceBoundedGodelWilliamsTower) where
  fastCircuitSAT : Prop
  smallRepresentation : Prop
  metaSimulation : Prop
  collapse_of_fastSAT_smallRepresentation :
    fastCircuitSAT ->
      smallRepresentation ->
        metaSimulation ->
          T.hierarchyCollapse

/-- The abstract Williams/Gödel contradiction. -/
theorem false_of_williamsGodelNonNaturalStep
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (hfast : W.fastCircuitSAT)
    (hsmall : W.smallRepresentation)
    (hmeta : W.metaSimulation) :
    False :=
  T.hierarchyNoCollapse
    (W.collapse_of_fastSAT_smallRepresentation hfast hsmall hmeta)

/-! ## The four load-bearing Gödel/Williams components -/

/-- Component 1: the N-frame Lagrangian supplies the fast SAT-like structured
view needed by the Williams step. -/
def NFrameSuppliesFastCircuitSAT
    (_D : DescribedCanonicalSurface)
    (_I : NFrameLagrangianPACInvariant)
    (_T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep _T) : Prop :=
  W.fastCircuitSAT

/-- Component 2: the N-frame/Gödel tower supplies the meta-simulation needed to
move from the base system to the stronger diagonal level. -/
def NFrameSuppliesMetaSimulation
    (_D : DescribedCanonicalSurface)
    (_I : NFrameLagrangianPACInvariant)
    (_T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep _T) : Prop :=
  W.metaSimulation

/-- Component 3: any canonical polynomial-time SAT decider yields the
small-representation hypothesis consumed by the Williams step. -/
def CanonicalDeciderYieldsSmallRepresentation
    (D : DescribedCanonicalSurface)
    (_I : NFrameLagrangianPACInvariant)
    (_T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep _T) : Prop :=
  CanonicalSATDecisionInP D.surface -> W.smallRepresentation

/-- Component 4: the collapse step is Williams-style and non-natural in shape:
it derives a forbidden hierarchy collapse from algorithmic/meta-simulation
ingredients, rather than from a large constructive property of truth tables. -/
def WilliamsGodelCollapseIsNonBlackBox
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T) : Prop :=
  W.fastCircuitSAT ->
    W.smallRepresentation ->
      W.metaSimulation ->
        T.hierarchyCollapse

/-- A `WilliamsGodelNonNaturalStep` contains the non-black-box collapse map as
data.  Constructing such a real step is the Williams-method theorem. -/
theorem williamsGodelCollapseIsNonBlackBox
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T) :
    WilliamsGodelCollapseIsNonBlackBox T W :=
  W.collapse_of_fastSAT_smallRepresentation

/-- The N-frame Lagrangian as a Williams/Gödel transport layer.

This is the positive, non-natural version of the route.  The N-frame invariant
must supply the fast/structured view and the meta-simulation step.  A canonical
polynomial-time SAT decider would supply the small representation.  Williams'
method then converts those three ingredients into a hierarchy collapse, rather
than into a large constructive property. -/
structure NFrameGodelWilliamsProgram
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T) : Prop where
  nframe_supplies_fastCircuitSAT : W.fastCircuitSAT
  nframe_supplies_metaSimulation : W.metaSimulation
  decider_to_smallRepresentation :
    CanonicalSATDecisionInP D.surface ->
      W.smallRepresentation

/-- Assemble the route program from the four named components, except that the
collapse map itself already lives in `W`. -/
theorem nFrameGodelWilliamsProgram_of_components
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (hfast : NFrameSuppliesFastCircuitSAT D I T W)
    (hmeta : NFrameSuppliesMetaSimulation D I T W)
    (hsmall : CanonicalDeciderYieldsSmallRepresentation D I T W) :
    NFrameGodelWilliamsProgram D I T W where
  nframe_supplies_fastCircuitSAT := hfast
  nframe_supplies_metaSimulation := hmeta
  decider_to_smallRepresentation := hsmall

/-- Direct closure from the four named components. -/
theorem noCanonicalSATDecisionInP_of_nFrameGodelWilliamsComponents
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (hfast : NFrameSuppliesFastCircuitSAT D I T W)
    (hmeta : NFrameSuppliesMetaSimulation D I T W)
    (hsmall : CanonicalDeciderYieldsSmallRepresentation D I T W)
    (hcollapse : WilliamsGodelCollapseIsNonBlackBox T W) :
    ¬ CanonicalSATDecisionInP D.surface := by
  intro hdec
  exact T.hierarchyNoCollapse (hcollapse hfast (hsmall hdec) hmeta)

/-- Guard theorem: if a canonical polynomial-time SAT decider exists, the four
Gödel/Williams components cannot all be true at once.  Thus those components are
exactly the breakthrough content, not routine Lean wiring. -/
theorem not_all_nFrameGodelWilliamsComponents_of_canonicalSATDecisionInP
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (hdec : CanonicalSATDecisionInP D.surface) :
    ¬ (NFrameSuppliesFastCircuitSAT D I T W ∧
        NFrameSuppliesMetaSimulation D I T W ∧
        CanonicalDeciderYieldsSmallRepresentation D I T W ∧
        WilliamsGodelCollapseIsNonBlackBox T W) := by
  intro hall
  rcases hall with ⟨hfast, hmeta, hsmall, hcollapse⟩
  exact T.hierarchyNoCollapse (hcollapse hfast (hsmall hdec) hmeta)

/-- Conditional route closure from the four explicit Gödel/Williams
components. -/
theorem ktRoute_finalClosure_of_nFrameGodelWilliamsComponents
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (hfast : NFrameSuppliesFastCircuitSAT D I T W)
    (hmeta : NFrameSuppliesMetaSimulation D I T W)
    (hsmall : CanonicalDeciderYieldsSmallRepresentation D I T W)
    (hcollapse : WilliamsGodelCollapseIsNonBlackBox T W) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardMetacomplexitySocket_of_noCanonicalSATDecisionInP D
      (noCanonicalSATDecisionInP_of_nFrameGodelWilliamsComponents
        D I T W hfast hmeta hsmall hcollapse))

/-! ## Restricted Williams test: ACC0-style target -/

/-- Abstract ACC0-style target for the Williams algorithmic method.

This intentionally lives at the known Williams scale: an NEXP language class,
small ACC0-circuit representation, a faster circuit-SAT procedure, easy
witnesses, and a nondeterministic hierarchy contradiction.  It is not a
P-vs-NP target. -/
structure ACC0WilliamsTarget where
  NEXPLanguage : Type
  HasACC0Circuits : NEXPLanguage -> Prop
  FastACC0CircuitSAT : Prop
  ACC0MetaSimulation : Prop
  EasyWitnessCompression : Prop
  HierarchyCollapse : Prop
  easyWitness_of_fastSAT_smallCircuits_meta :
    FastACC0CircuitSAT ->
      (∀ L : NEXPLanguage, HasACC0Circuits L) ->
        ACC0MetaSimulation ->
          EasyWitnessCompression
  hierarchyCollapse_of_easyWitness_smallCircuits_meta :
    EasyWitnessCompression ->
      (∀ L : NEXPLanguage, HasACC0Circuits L) ->
        ACC0MetaSimulation ->
          HierarchyCollapse
  hierarchyContradiction : ¬ HierarchyCollapse

/-- Forget the ACC0-specific names into the existing Williams circuit-class
surface. -/
def ACC0WilliamsTarget.toCircuitClass
    (A : ACC0WilliamsTarget) :
    PallLean.Paper93.DeepMath.PathB.WilliamsCircuitClass where
  NEXPLanguage := A.NEXPLanguage
  HasSmallCircuits := A.HasACC0Circuits
  FastCircuitSAT := A.FastACC0CircuitSAT
  EasyWitnessCompression := A.EasyWitnessCompression
  HierarchyCollapse := A.HierarchyCollapse

/-- The restricted small-representation hypothesis is `NEXP ⊆ ACC0` for this
abstract target. -/
def ACC0WilliamsTarget.smallRepresentation
    (A : ACC0WilliamsTarget) : Prop :=
  PallLean.Paper93.DeepMath.PathB.NEXPSubsetCircuitClass A.toCircuitClass

/-- View the ACC0 target as a Gödel/Williams tower. -/
def ACC0WilliamsTarget.toGodelWilliamsTower
    (A : ACC0WilliamsTarget) :
    ResourceBoundedGodelWilliamsTower where
  baseSystemCode := 0
  metaSystemCode := 1
  diagonalSentenceCode := 2
  hierarchyCollapse := A.HierarchyCollapse
  hierarchyNoCollapse := A.hierarchyContradiction

/-- View the ACC0 target as the non-natural Williams step used by the N-frame
component split. -/
def ACC0WilliamsTarget.toGodelWilliamsStep
    (A : ACC0WilliamsTarget) :
    WilliamsGodelNonNaturalStep A.toGodelWilliamsTower where
  fastCircuitSAT := A.FastACC0CircuitSAT
  smallRepresentation := A.smallRepresentation
  metaSimulation := A.ACC0MetaSimulation
  collapse_of_fastSAT_smallRepresentation := by
    intro hfast hsmall hmeta
    exact A.hierarchyCollapse_of_easyWitness_smallCircuits_meta
      (A.easyWitness_of_fastSAT_smallCircuits_meta hfast hsmall hmeta)
      hsmall
      hmeta

/-- The ACC0 target also produces the repository's existing Williams transport,
once the meta-simulation infrastructure is available. -/
def ACC0WilliamsTarget.toWilliamsTransport
    (A : ACC0WilliamsTarget)
    (hmeta : A.ACC0MetaSimulation) :
    PallLean.Paper93.DeepMath.PathB.WilliamsAlgorithmicTransport
      A.toCircuitClass where
  easyWitness_of_fastSAT_and_smallCircuits := by
    intro hfast hsmall
    exact A.easyWitness_of_fastSAT_smallCircuits_meta hfast hsmall hmeta
  hierarchyCollapse_of_easyWitness_and_smallCircuits := by
    intro heasy hsmall
    exact A.hierarchyCollapse_of_easyWitness_smallCircuits_meta
      heasy hsmall hmeta
  hierarchyContradiction := A.hierarchyContradiction

/-- The restricted Williams conclusion: fast ACC0 circuit-SAT plus the
meta-simulation infrastructure gives the NEXP-vs-ACC0-style lower bound. -/
theorem acc0_nexp_not_subset_of_fastSAT_and_metaSimulation
    (A : ACC0WilliamsTarget)
    (hfast : A.FastACC0CircuitSAT)
    (hmeta : A.ACC0MetaSimulation) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      A.toCircuitClass :=
  PallLean.Paper93.DeepMath.PathB.nexp_not_subset_of_williams_transport
    A.toCircuitClass
    hfast
    (A.toWilliamsTransport hmeta)

/-- N-frame restricted ACC0 program: the N-frame Lagrangian supplies the two
algorithmic ingredients Williams can use at the restricted NEXP/circuit-class
scale. -/
structure NFrameACC0WilliamsRestrictedProgram
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (A : ACC0WilliamsTarget) : Prop where
  nframe_fast_acc0_sat :
    NFrameSuppliesFastCircuitSAT D I
      A.toGodelWilliamsTower A.toGodelWilliamsStep
  nframe_meta_simulation :
    NFrameSuppliesMetaSimulation D I
      A.toGodelWilliamsTower A.toGodelWilliamsStep

/-- A completed restricted N-frame/ACC0 Williams program yields the restricted
Williams lower bound.  This is the test case that can actually be expected from
the algorithmic method: NEXP-vs-a-circuit-class, not P vs NP. -/
theorem acc0_nexp_not_subset_of_nFrameACC0WilliamsRestrictedProgram
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (A : ACC0WilliamsTarget)
    (h : NFrameACC0WilliamsRestrictedProgram D I A) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      A.toCircuitClass :=
  acc0_nexp_not_subset_of_fastSAT_and_metaSimulation
    A h.nframe_fast_acc0_sat h.nframe_meta_simulation

/-- Guard for the restricted test: if the target class already contains NEXP,
then the restricted N-frame/Williams program cannot exist. -/
theorem not_nFrameACC0WilliamsRestrictedProgram_of_nexp_subset_acc0
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (A : ACC0WilliamsTarget)
    (hsubset :
      PallLean.Paper93.DeepMath.PathB.NEXPSubsetCircuitClass
        A.toCircuitClass) :
    ¬ NFrameACC0WilliamsRestrictedProgram D I A := by
  intro h
  exact
    (acc0_nexp_not_subset_of_nFrameACC0WilliamsRestrictedProgram
      D I A h) hsubset

/-! ## Concrete ACC0-like surface -/

/-- A concrete ACC0-like circuit object: bounded depth, bounded size, bounded
modulus, and a Boolean semantics on its input arity.

This is deliberately still lightweight; the point is to stop treating `ACC0` as
only a name while avoiding a full circuit-complexity library inside this file.
-/
structure ACC0LikeCircuit where
  inputArity : Nat
  depth : Nat
  size : Nat
  modulusBound : Nat
  semantics : (Fin inputArity -> Bool) -> Bool

/-- A nonuniform ACC0-like circuit family with explicit constant-depth,
polynomial-size, and finite-modulus bounds. -/
structure ACC0LikeCircuitFamily where
  circuit : Nat -> ACC0LikeCircuit
  depthBound : Nat
  sizeExponent : Nat
  modulusBound : Nat
  depth_le : ∀ n : Nat, (circuit n).depth <= depthBound
  size_le : ∀ n : Nat, (circuit n).size <= n ^ sizeExponent
  modulus_le : ∀ n : Nat, (circuit n).modulusBound <= modulusBound

/-- Abstract NEXP language codes for the restricted Williams test. -/
structure ConcreteNEXPLanguage where
  code : Nat
  accepts : Nat -> Prop

/-- Global ACC0-like class parameters. -/
structure ConcreteACC0Surface where
  depthBound : Nat
  sizeExponent : Nat
  modulusBound : Nat

/-- A concrete NEXP language has ACC0-like circuits if it has a bounded family
under the chosen surface parameters. -/
def ConcreteNEXPHasACC0Circuits
    (S : ConcreteACC0Surface)
    (_L : ConcreteNEXPLanguage) : Prop :=
  ∃ F : ACC0LikeCircuitFamily,
    F.depthBound <= S.depthBound ∧
      F.sizeExponent <= S.sizeExponent ∧
        F.modulusBound <= S.modulusBound

/-- The real Williams theorem package for the concrete ACC0-like surface.

These fields are the known algorithmic-method ingredients: fast ACC0 circuit
SAT, meta-simulation/easy witnesses, and the hierarchy contradiction.  They are
not consequences of the N-frame Lagrangian by definition; that is exactly what
the next theorem must prove if the N-frame route is to reproduce a restricted
Williams lower bound. -/
structure ConcreteACC0WilliamsPackage
    (S : ConcreteACC0Surface) where
  FastACC0CircuitSAT : Prop
  ACC0MetaSimulation : Prop
  EasyWitnessCompression : Prop
  HierarchyCollapse : Prop
  easyWitness_of_fastSAT_smallCircuits_meta :
    FastACC0CircuitSAT ->
      (∀ L : ConcreteNEXPLanguage, ConcreteNEXPHasACC0Circuits S L) ->
        ACC0MetaSimulation ->
          EasyWitnessCompression
  hierarchyCollapse_of_easyWitness_smallCircuits_meta :
    EasyWitnessCompression ->
      (∀ L : ConcreteNEXPLanguage, ConcreteNEXPHasACC0Circuits S L) ->
        ACC0MetaSimulation ->
          HierarchyCollapse
  hierarchyContradiction : ¬ HierarchyCollapse

/-- Instantiate the abstract ACC0 Williams target with an actual ACC0-like
circuit-family surface. -/
def concreteACC0WilliamsTarget
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S) :
    ACC0WilliamsTarget where
  NEXPLanguage := ConcreteNEXPLanguage
  HasACC0Circuits := ConcreteNEXPHasACC0Circuits S
  FastACC0CircuitSAT := P.FastACC0CircuitSAT
  ACC0MetaSimulation := P.ACC0MetaSimulation
  EasyWitnessCompression := P.EasyWitnessCompression
  HierarchyCollapse := P.HierarchyCollapse
  easyWitness_of_fastSAT_smallCircuits_meta :=
    P.easyWitness_of_fastSAT_smallCircuits_meta
  hierarchyCollapse_of_easyWitness_smallCircuits_meta :=
    P.hierarchyCollapse_of_easyWitness_smallCircuits_meta
  hierarchyContradiction := P.hierarchyContradiction

/-- Concrete version of component 1: the N-frame Lagrangian supplies fast ACC0
circuit SAT for the concrete circuit-family surface. -/
def NFrameSuppliesConcreteACC0FastCircuitSAT
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S) : Prop :=
  NFrameSuppliesFastCircuitSAT D I
    (concreteACC0WilliamsTarget S P).toGodelWilliamsTower
    (concreteACC0WilliamsTarget S P).toGodelWilliamsStep

/-- Concrete version of component 2: the N-frame/Gödel layer supplies the
meta-simulation for the concrete ACC0-like target. -/
def NFrameSuppliesConcreteACC0MetaSimulation
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S) : Prop :=
  NFrameSuppliesMetaSimulation D I
    (concreteACC0WilliamsTarget S P).toGodelWilliamsTower
    (concreteACC0WilliamsTarget S P).toGodelWilliamsStep

/-- Assemble the concrete ACC0 ingredients into the restricted N-frame/Williams
program. -/
theorem nFrameACC0WilliamsRestrictedProgram_of_concreteACC0Ingredients
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hfast : NFrameSuppliesConcreteACC0FastCircuitSAT D I S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    NFrameACC0WilliamsRestrictedProgram D I
      (concreteACC0WilliamsTarget S P) where
  nframe_fast_acc0_sat := hfast
  nframe_meta_simulation := hmeta

/-- The concrete restricted test: if the N-frame layer really supplies fast ACC0
circuit SAT and meta-simulation for the concrete surface, the Williams theorem
gives the restricted NEXP-vs-ACC0-style lower bound. -/
theorem concreteACC0_nexp_not_subset_of_nFrame_fastSAT_meta
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hfast : NFrameSuppliesConcreteACC0FastCircuitSAT D I S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      (concreteACC0WilliamsTarget S P).toCircuitClass :=
  acc0_nexp_not_subset_of_nFrameACC0WilliamsRestrictedProgram
    D I (concreteACC0WilliamsTarget S P)
    (nFrameACC0WilliamsRestrictedProgram_of_concreteACC0Ingredients
      D I S P hfast hmeta)

/-- Guard for the concrete surface: if NEXP is contained in the concrete
ACC0-like class, the N-frame layer cannot supply both algorithmic ingredients.
-/
theorem not_both_nFrameConcreteACC0Ingredients_of_nexp_subset
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hsubset :
      PallLean.Paper93.DeepMath.PathB.NEXPSubsetCircuitClass
        (concreteACC0WilliamsTarget S P).toCircuitClass) :
    ¬ (NFrameSuppliesConcreteACC0FastCircuitSAT D I S P ∧
        NFrameSuppliesConcreteACC0MetaSimulation D I S P) := by
  intro h
  exact
    (concreteACC0_nexp_not_subset_of_nFrame_fastSAT_meta
      D I S P h.1 h.2) hsubset

/-! ## SYM+-easiness diagnostic for the ACC0 test -/

/-- The two symmetric probes used to test whether the N-frame/SPDP profile is an
easiness detector for the Williams ACC0 algorithm.  `majority` and `mod3` are
SYM+-easy in the algorithmic-method sense, but can still carry maximal SPDP
profile rank. -/
inductive SYMPlusProbe where
  | majority
  | mod3

/-- A computed or proved probe witnessing that a SYM+-easy function has maximal
SPDP profile rank.

This does not refute ACC0 fast-SAT itself.  It refutes the narrower mechanism
"N-frame supplies ACC0 fast-SAT because SPDP/log-det rank detects SYM+-easiness".
-/
structure SYMPlusEasyMaximalSPDPProbe where
  probe : SYMPlusProbe
  arity : Nat
  symPlusEasy : Prop
  spdpRank : Nat
  maxProfileRank : Nat
  symPlusEasy_proof : symPlusEasy
  spdpRank_maximal : spdpRank = maxProfileRank
  maxProfileRank_pos : 0 < maxProfileRank

/-- What a rank-as-easiness detector would need on a SYM+ probe: SYM+-easy
probes must read as nonmaximal/low rank. -/
def SPDPProbeReadsSYMPlusEasyAsNonmaximal
    (probe : SYMPlusEasyMaximalSPDPProbe) : Prop :=
  probe.symPlusEasy -> probe.spdpRank < probe.maxProfileRank

/-- A SYM+-easy maximal-rank probe refutes rank-as-easiness detection. -/
theorem not_spdpProbeReadsSYMPlusEasyAsNonmaximal
    (probe : SYMPlusEasyMaximalSPDPProbe) :
    ¬ SPDPProbeReadsSYMPlusEasyAsNonmaximal probe := by
  intro hdetects
  have hlt : probe.maxProfileRank < probe.maxProfileRank := by
    simpa [probe.spdpRank_maximal] using hdetects probe.symPlusEasy_proof
  exact (Nat.lt_irrefl probe.maxProfileRank) hlt

/-- The specific mechanism under test: N-frame supplies concrete ACC0 fast-SAT
through an SPDP/log-det detector that reads SYM+-easy probes as nonmaximal.

The point of naming this separately is to avoid overclaiming.  The negative
theorem below does not say Williams' ACC0 algorithm fails; it says this N-frame
rank mechanism cannot be the source of that algorithm. -/
def NFrameConcreteACC0FastSATViaSPDPDetector
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (probe : SYMPlusEasyMaximalSPDPProbe) : Prop :=
  NFrameSuppliesConcreteACC0FastCircuitSAT D I S P ∧
    SPDPProbeReadsSYMPlusEasyAsNonmaximal probe

/-- A SYM+-easy maximal-rank probe rules out the SPDP-detector route to
N-frame-supplied ACC0 fast-SAT. -/
theorem not_nFrameConcreteACC0FastSATViaSPDPDetector
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (probe : SYMPlusEasyMaximalSPDPProbe) :
    ¬ NFrameConcreteACC0FastSATViaSPDPDetector D I S P probe := by
  intro h
  exact not_spdpProbeReadsSYMPlusEasyAsNonmaximal probe h.2

/-! ## Positive ACC0 route through SYM+ normal forms -/

/-- A SYM+ normal form: a symmetric combiner applied to a bounded collection of
AND-like local terms.  This is the surface exploited by the
Yao-Beigel-Tarui/Williams ACC0 algorithmic method. -/
structure SYMPlusNormalForm (arity : Nat) where
  andGateCount : Nat
  symmetricCombinerCode : Nat
  evaluate : (Fin arity -> Bool) -> Bool

/-- A concrete ACC0-like circuit has a SYM+ presentation when the normal form
agrees with the circuit's Boolean semantics. -/
structure ACC0CircuitHasSYMPlusNormalForm
    (C : ACC0LikeCircuit) where
  normalForm : SYMPlusNormalForm C.inputArity
  agrees : ∀ x : Fin C.inputArity -> Bool,
    normalForm.evaluate x = C.semantics x

/-- A family has efficient SYM+ normal forms when every length has a normal
form and the number of AND-like terms is polynomially bounded. -/
structure ACC0FamilyHasEfficientSYMPlusNormalForms
    (F : ACC0LikeCircuitFamily) where
  normalForm :
    ∀ n : Nat, ACC0CircuitHasSYMPlusNormalForm (F.circuit n)
  andGateExponent : Nat
  andGateCount_le :
    ∀ n : Nat,
      ((normalForm n).normalForm).andGateCount <= n ^ andGateExponent

/-- The current loose `SYMPlusNormalForm` surface allows a semantic normal form
for every circuit: put the circuit semantics directly in `evaluate`.  This is a
useful guard theorem, not a breakthrough.  It shows that the loose surface is
too weak to certify a genuine Yao-Beigel-Tarui-style normal form. -/
def semanticSYMPlusNormalForm
    (C : ACC0LikeCircuit) :
    ACC0CircuitHasSYMPlusNormalForm C where
  normalForm := {
    andGateCount := C.size
    symmetricCombinerCode := 0
    evaluate := C.semantics
  }
  agrees := by
    intro x
    rfl

/-- Every ACC0-like circuit family has loose semantic SYM+ normal forms. -/
def semanticACC0FamilyHasEfficientSYMPlusNormalForms
    (F : ACC0LikeCircuitFamily) :
    ACC0FamilyHasEfficientSYMPlusNormalForms F where
  normalForm := fun n => semanticSYMPlusNormalForm (F.circuit n)
  andGateExponent := F.sizeExponent
  andGateCount_le := by
    intro n
    exact F.size_le n

/-- The concrete ACC0 family belongs to the chosen surface bounds. -/
def ACC0FamilyBoundedBySurface
    (S : ConcreteACC0Surface)
    (F : ACC0LikeCircuitFamily) : Prop :=
  F.depthBound <= S.depthBound ∧
    F.sizeExponent <= S.sizeExponent ∧
      F.modulusBound <= S.modulusBound

/-- The N-frame Lagrangian yields the algorithmically useful object only if it
extracts efficient SYM+ normal forms for every ACC0-like family in the concrete
surface. -/
def NFrameLagrangianYieldsSYMPlusNormalForms
    (_D : DescribedCanonicalSurface)
    (_I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface) : Prop :=
  ∀ F : ACC0LikeCircuitFamily,
    ACC0FamilyBoundedBySurface S F ->
      Nonempty (ACC0FamilyHasEfficientSYMPlusNormalForms F)

/-- The loose `NFrameLagrangianYieldsSYMPlusNormalForms` theorem is provable
without using the N-frame Lagrangian at all.  That is the diagnostic: the loose
surface is semantic bookkeeping, not the load-bearing ACC0 algorithmic theorem.
-/
theorem loose_nFrameLagrangianYieldsSYMPlusNormalForms
    (_D : DescribedCanonicalSurface)
    (_I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface) :
    NFrameLagrangianYieldsSYMPlusNormalForms _D _I S := by
  intro F _hbounded
  exact ⟨semanticACC0FamilyHasEfficientSYMPlusNormalForms F⟩

/-! ## Strict SYM+ normal forms -/

/-- A strict SYM+ normal form: a symmetric combiner of AND terms.  Unlike the
loose surface above, the evaluation is fixed by the AND supports and the
symmetric combiner. -/
structure StrictSYMPlusNormalForm (arity : Nat) where
  termCount : Nat
  andSupport : Fin termCount -> Finset (Fin arity)
  symmetricCombiner : Nat -> Bool

/-- Evaluate one AND term of a strict SYM+ normal form. -/
noncomputable def StrictSYMPlusNormalForm.andTermValue
    {arity : Nat}
    (N : StrictSYMPlusNormalForm arity)
    (i : Fin N.termCount)
    (x : Fin arity -> Bool) : Bool :=
  if ∀ v : Fin arity, v ∈ N.andSupport i -> x v = true then
    true
  else
    false

/-- Count how many AND terms evaluate to true. -/
noncomputable def StrictSYMPlusNormalForm.trueTermCount
    {arity : Nat}
    (N : StrictSYMPlusNormalForm arity)
    (x : Fin arity -> Bool) : Nat :=
  (Finset.univ.filter fun i : Fin N.termCount =>
    N.andTermValue i x = true).card

/-- Evaluate a strict SYM+ normal form. -/
noncomputable def StrictSYMPlusNormalForm.evaluate
    {arity : Nat}
    (N : StrictSYMPlusNormalForm arity)
    (x : Fin arity -> Bool) : Bool :=
  N.symmetricCombiner (N.trueTermCount x)

/-- A circuit has a strict SYM+ normal form if the symmetric-of-ANDs evaluation
agrees with the circuit semantics. -/
structure ACC0CircuitHasStrictSYMPlusNormalForm
    (C : ACC0LikeCircuit) where
  normalForm : StrictSYMPlusNormalForm C.inputArity
  agrees : ∀ x : Fin C.inputArity -> Bool,
    normalForm.evaluate x = C.semantics x

/-- A family has efficient strict SYM+ normal forms. -/
structure ACC0FamilyHasEfficientStrictSYMPlusNormalForms
    (F : ACC0LikeCircuitFamily) where
  normalForm :
    ∀ n : Nat, ACC0CircuitHasStrictSYMPlusNormalForm (F.circuit n)
  andGateExponent : Nat
  andGateCount_le :
    ∀ n : Nat,
      ((normalForm n).normalForm).termCount <= n ^ andGateExponent

/-- The real N-frame extraction target: strict SYM+ normal forms, not arbitrary
semantic normal forms. -/
def NFrameLagrangianYieldsStrictSYMPlusNormalForms
    (_D : DescribedCanonicalSurface)
    (_I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface) : Prop :=
  ∀ F : ACC0LikeCircuitFamily,
    ACC0FamilyBoundedBySurface S F ->
      Nonempty (ACC0FamilyHasEfficientStrictSYMPlusNormalForms F)

/-- The strict target without N-frame labels.  This is the pure
Yao-Beigel-Tarui-style normalization statement for the concrete surface. -/
def StrictSYMPlusNormalizationSurface
    (S : ConcreteACC0Surface) : Prop :=
  ∀ F : ACC0LikeCircuitFamily,
    ACC0FamilyBoundedBySurface S F ->
      Nonempty (ACC0FamilyHasEfficientStrictSYMPlusNormalForms F)

/-- The current strict N-frame-yields statement is definitionally just the
surface normalization theorem; it does not yet force the normal form to be
carried by the N-frame Lagrangian. -/
theorem nFrameLagrangianYieldsStrictSYMPlusNormalForms_iff_surfaceNormalization
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface) :
    NFrameLagrangianYieldsStrictSYMPlusNormalForms D I S ↔
      StrictSYMPlusNormalizationSurface S :=
  Iff.rfl

/-- A surface normalization theorem proves the current strict target for any
N-frame labels.  This is useful, but it is YBT normalization, not N-frame
extraction. -/
theorem nFrameLagrangianYieldsStrictSYMPlusNormalForms_of_surfaceNormalization
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (hYBT : StrictSYMPlusNormalizationSurface S) :
    NFrameLagrangianYieldsStrictSYMPlusNormalForms D I S :=
  hYBT

/-! ## Certified strict extraction from N-frame bulk -/

/-- A strict SYM+ normal form certified by a low-action N-frame bulk object. -/
structure NFrameCertifiedStrictSYMPlusNormalForm
    (_D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (F : ACC0LikeCircuitFamily)
    (n : Nat) where
  bulk : NFramePACBulk I.dim
  low_action : I.action bulk <= I.actionBound
  strictNormalForm : ACC0CircuitHasStrictSYMPlusNormalForm (F.circuit n)
  reconstruction_tracks_size :
    bulk.reconstructionCode = (F.circuit n).size
  description_tracks_termCount :
    bulk.descriptionLength = strictNormalForm.normalForm.termCount

/-- A family has efficient strict SYM+ normal forms certified by N-frame bulk. -/
structure ACC0FamilyHasNFrameCertifiedEfficientStrictSYMPlusNormalForms
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (F : ACC0LikeCircuitFamily) where
  certified :
    ∀ n : Nat, NFrameCertifiedStrictSYMPlusNormalForm D I F n
  andGateExponent : Nat
  andGateCount_le :
    ∀ n : Nat,
      ((certified n).strictNormalForm.normalForm).termCount <=
        n ^ andGateExponent

/-- Forget the N-frame certificates and keep only the strict SYM+ normal forms.
-/
def ACC0FamilyHasNFrameCertifiedEfficientStrictSYMPlusNormalForms.toStrict
    {D : DescribedCanonicalSurface}
    {I : NFrameLagrangianPACInvariant}
    {F : ACC0LikeCircuitFamily}
    (C : ACC0FamilyHasNFrameCertifiedEfficientStrictSYMPlusNormalForms D I F) :
    ACC0FamilyHasEfficientStrictSYMPlusNormalForms F where
  normalForm := fun n => (C.certified n).strictNormalForm
  andGateExponent := C.andGateExponent
  andGateCount_le := C.andGateCount_le

/-- The real N-frame extraction target: strict SYM+ normal forms must be
certified by low-action N-frame bulk objects. -/
def NFrameLagrangianExtractsStrictSYMPlusNormalForms
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface) : Prop :=
  ∀ F : ACC0LikeCircuitFamily,
    ACC0FamilyBoundedBySurface S F ->
      Nonempty
        (ACC0FamilyHasNFrameCertifiedEfficientStrictSYMPlusNormalForms D I F)

/-- Certified N-frame extraction implies the current strict-normal-form target.
-/
theorem nFrameLagrangianYieldsStrictSYMPlusNormalForms_of_certifiedExtraction
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (hextract : NFrameLagrangianExtractsStrictSYMPlusNormalForms D I S) :
    NFrameLagrangianYieldsStrictSYMPlusNormalForms D I S := by
  intro F hbounded
  rcases hextract F hbounded with ⟨certified⟩
  exact ⟨certified.toStrict⟩

/-! ## Bulk encoding theorem for certified extraction -/

/-- A low-action N-frame bulk encoder for strict SYM+ normal forms.

This is the actual N-frame certification theorem separated from the pure
YBT-style normalization theorem: given a strict normal form, the N-frame
Lagrangian must provide a low-action bulk object whose bookkeeping tracks the
circuit size and normal-form term count. -/
structure NFrameStrictSYMPlusBulkEncoder
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant) where
  encode :
    ∀ (F : ACC0LikeCircuitFamily) (n : Nat)
      (_nf : ACC0CircuitHasStrictSYMPlusNormalForm (F.circuit n)),
        NFrameCertifiedStrictSYMPlusNormalForm D I F n
  encode_strictNormalForm :
    ∀ (F : ACC0LikeCircuitFamily) (n : Nat)
      (nf : ACC0CircuitHasStrictSYMPlusNormalForm (F.circuit n)),
        (encode F n nf).strictNormalForm = nf

/-! ## Low-action bulk coding capacity -/

/-- The exact low-action N-frame capacity needed by the strict SYM+ encoder:
for every code/description pair, produce a low-action bulk object carrying that
pair. -/
structure NFrameLowActionBulkCodingCapacity
    (I : NFrameLagrangianPACInvariant) where
  bulk : Nat -> Nat -> NFramePACBulk I.dim
  low_action :
    ∀ code desc : Nat, I.action (bulk code desc) <= I.actionBound
  reconstructionCode_eq :
    ∀ code desc : Nat, (bulk code desc).reconstructionCode = code
  descriptionLength_eq :
    ∀ code desc : Nat, (bulk code desc).descriptionLength = desc

/-- A pointwise low-action encoding of one code/description pair.  This is the
targeted version of `NFrameLowActionBulkCodingCapacity`: it carries actual data,
not just a proposition, so it can be used to build certified normal forms. -/
structure LowActionBulkEncoding
    (I : NFrameLagrangianPACInvariant)
    (code desc : Nat) where
  bulk : NFramePACBulk I.dim
  low_action : I.action bulk <= I.actionBound
  reconstructionCode_eq :
    bulk.reconstructionCode = code
  descriptionLength_eq :
    bulk.descriptionLength = desc

/-- Universal low-action capacity gives a pointwise low-action encoding. -/
def lowActionBulkEncoding_of_capacity
    (I : NFrameLagrangianPACInvariant)
    (capacity : NFrameLowActionBulkCodingCapacity I)
    (code desc : Nat) :
    LowActionBulkEncoding I code desc where
  bulk := capacity.bulk code desc
  low_action := capacity.low_action code desc
  reconstructionCode_eq := capacity.reconstructionCode_eq code desc
  descriptionLength_eq := capacity.descriptionLength_eq code desc

/-- Pointwise low-action encodings for every pair assemble into universal
low-action coding capacity. -/
def lowActionBulkCodingCapacity_of_pointwiseEncoding
    (I : NFrameLagrangianPACInvariant)
    (encode : ∀ code desc : Nat, LowActionBulkEncoding I code desc) :
    NFrameLowActionBulkCodingCapacity I where
  bulk := fun code desc => (encode code desc).bulk
  low_action := fun code desc => (encode code desc).low_action
  reconstructionCode_eq := fun code desc =>
    (encode code desc).reconstructionCode_eq
  descriptionLength_eq := fun code desc =>
    (encode code desc).descriptionLength_eq

/-- Because the current log-det action depends only on the matrix field,
arbitrary bookkeeping codes can be attached to the identity matrix without
increasing action.

This proves the targeted coding theorem, but it is a diagnostic victory rather
than a lower-bound breakthrough: the bookkeeping is not constrained by the
N-frame Lagrangian. -/
def lowActionBulkCodingCapacity_of_bookkeepingFreeLogDetAction
    (I : NFrameLagrangianPACInvariant) :
    NFrameLowActionBulkCodingCapacity I where
  bulk := fun code desc =>
    NFramePACBulk.identityMatrixWithBookkeeping I.dim code desc
  low_action := by
    intro code desc
    simpa [NFrameLagrangianPACInvariant.action, nFramePACLogDetAction,
      NFramePACBulk.identity, NFramePACBulk.identityMatrixWithBookkeeping]
      using I.identity_low_action
  reconstructionCode_eq := by
    intro code desc
    rfl
  descriptionLength_eq := by
    intro code desc
    rfl

/-- Low-action bulk coding capacity constructs the strict SYM+ bulk encoder. -/
def nFrameStrictSYMPlusBulkEncoder_of_lowActionBulkCodingCapacity
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (capacity : NFrameLowActionBulkCodingCapacity I) :
    NFrameStrictSYMPlusBulkEncoder D I where
  encode := by
    intro F n nf
    exact {
      bulk := capacity.bulk (F.circuit n).size nf.normalForm.termCount
      low_action :=
        capacity.low_action (F.circuit n).size nf.normalForm.termCount
      strictNormalForm := nf
      reconstruction_tracks_size :=
        capacity.reconstructionCode_eq
          (F.circuit n).size nf.normalForm.termCount
      description_tracks_termCount :=
        capacity.descriptionLength_eq
          (F.circuit n).size nf.normalForm.termCount
    }
  encode_strictNormalForm := by
    intro F n nf
    rfl

/-- If the only low-action bulk object is the identity/reference bulk, the
N-frame invariant cannot have universal low-action coding capacity. -/
def IdentityOnlyLowActionBulk
    (I : NFrameLagrangianPACInvariant) : Prop :=
  ∀ bulk : NFramePACBulk I.dim,
    I.action bulk <= I.actionBound ->
      bulk = NFramePACBulk.identity I.dim

/-- Identity-only low action rules out the coding capacity, because the capacity
must encode code `1`, while identity carries code `0`. -/
theorem not_lowActionBulkCodingCapacity_of_identityOnly
    (I : NFrameLagrangianPACInvariant)
    (honly : IdentityOnlyLowActionBulk I) :
    ¬ Nonempty (NFrameLowActionBulkCodingCapacity I) := by
  intro hcapacity
  rcases hcapacity with ⟨capacity⟩
  let b := capacity.bulk 1 0
  have hb : b = NFramePACBulk.identity I.dim :=
    honly b (capacity.low_action 1 0)
  have hcode0 : b.reconstructionCode = 0 := by
    simpa [b, NFramePACBulk.identity] using
      congrArg NFramePACBulk.reconstructionCode hb
  have h10 : (1 : Nat) = 0 := by
    rw [← capacity.reconstructionCode_eq 1 0]
    exact hcode0
  exact Nat.succ_ne_zero 0 h10

/-- Identity-only low action rules out a pointwise encoding of any nonzero
code/description pair. -/
theorem not_lowActionBulkEncoding_of_identityOnly_nonzero
    (I : NFrameLagrangianPACInvariant)
    (code desc : Nat)
    (honly : IdentityOnlyLowActionBulk I)
    (hnonzero : code ≠ 0 ∨ desc ≠ 0) :
    ¬ Nonempty (LowActionBulkEncoding I code desc) := by
  intro hencoding
  rcases hencoding with ⟨encoding⟩
  have hbulk : encoding.bulk = NFramePACBulk.identity I.dim :=
    honly encoding.bulk encoding.low_action
  have hcode0_bulk : encoding.bulk.reconstructionCode = 0 := by
    simpa [NFramePACBulk.identity] using
      congrArg NFramePACBulk.reconstructionCode hbulk
  have hdesc0_bulk : encoding.bulk.descriptionLength = 0 := by
    simpa [NFramePACBulk.identity] using
      congrArg NFramePACBulk.descriptionLength hbulk
  have hcode0 : code = 0 := by
    rw [← encoding.reconstructionCode_eq]
    exact hcode0_bulk
  have hdesc0 : desc = 0 := by
    rw [← encoding.descriptionLength_eq]
    exact hdesc0_bulk
  rcases hnonzero with hcode | hdesc
  · exact hcode hcode0
  · exact hdesc hdesc0

/-- Identity-only low action also rules out a strict bulk encoder whenever a
requested certificate has nonzero circuit-size code or nonzero term-count
description. -/
theorem not_nFrameStrictSYMPlusBulkEncoder_of_identityOnly_nonzeroCertificate
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (F : ACC0LikeCircuitFamily)
    (n : Nat)
    (nf : ACC0CircuitHasStrictSYMPlusNormalForm (F.circuit n))
    (honly : IdentityOnlyLowActionBulk I)
    (hnonzero :
      (F.circuit n).size ≠ 0 ∨ nf.normalForm.termCount ≠ 0) :
    ¬ Nonempty (NFrameStrictSYMPlusBulkEncoder D I) := by
  intro hencoder
  rcases hencoder with ⟨encoder⟩
  let cert := encoder.encode F n nf
  have hbulk : cert.bulk = NFramePACBulk.identity I.dim :=
    honly cert.bulk cert.low_action
  have hcode0 : cert.bulk.reconstructionCode = 0 := by
    simpa [cert, NFramePACBulk.identity] using
      congrArg NFramePACBulk.reconstructionCode hbulk
  have hdesc0 : cert.bulk.descriptionLength = 0 := by
    simpa [cert, NFramePACBulk.identity] using
      congrArg NFramePACBulk.descriptionLength hbulk
  have hnf : cert.strictNormalForm = nf :=
    encoder.encode_strictNormalForm F n nf
  rcases hnonzero with hsize | hterms
  · have hsize0 : (F.circuit n).size = 0 := by
      rw [← cert.reconstruction_tracks_size]
      exact hcode0
    exact hsize hsize0
  · have hterm0 : nf.normalForm.termCount = 0 := by
      rw [← hnf]
      rw [← cert.description_tracks_termCount]
      exact hdesc0
    exact hterms hterm0

/-- Targeted low-action coding for the strict SYM+ certificates that the
surface normalization theorem actually produces.

This is weaker and more faithful than universal capacity: the N-frame layer only
has to encode the circuit-size/term-count pairs used by the strict normal forms
on the concrete surface. -/
structure NFrameTargetedStrictSYMPlusBulkCoding
    (_D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface) where
  encode :
    ∀ (F : ACC0LikeCircuitFamily),
      ACC0FamilyBoundedBySurface S F ->
        ∀ strictFamily : ACC0FamilyHasEfficientStrictSYMPlusNormalForms F,
          ∀ n : Nat,
            LowActionBulkEncoding I
              (F.circuit n).size
              ((strictFamily.normalForm n).normalForm).termCount

/-- Universal capacity implies the targeted strict-SYM+ coding theorem. -/
def nFrameTargetedStrictSYMPlusBulkCoding_of_lowActionBulkCodingCapacity
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (capacity : NFrameLowActionBulkCodingCapacity I) :
    NFrameTargetedStrictSYMPlusBulkCoding D I S where
  encode := by
    intro F _hbounded strictFamily n
    exact lowActionBulkEncoding_of_capacity I capacity
      (F.circuit n).size
      ((strictFamily.normalForm n).normalForm).termCount

/-- The current bookkeeping-free log-det action proves the targeted strict-SYM+
bulk-coding theorem directly.

This is useful as a guard: if targeted coding was meant to be load-bearing, the
bulk/action model must be strengthened so the action sees the encoded
reconstruction data. -/
def nFrameTargetedStrictSYMPlusBulkCoding_of_bookkeepingFreeLogDetAction
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface) :
    NFrameTargetedStrictSYMPlusBulkCoding D I S :=
  nFrameTargetedStrictSYMPlusBulkCoding_of_lowActionBulkCodingCapacity
    D I S
    (lowActionBulkCodingCapacity_of_bookkeepingFreeLogDetAction I)

/-- Identity-only low action rules out targeted coding as soon as one requested
strict-SYM+ certificate needs a nonzero code or description. -/
theorem not_nFrameTargetedStrictSYMPlusBulkCoding_of_identityOnly_nonzero
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (F : ACC0LikeCircuitFamily)
    (hbounded : ACC0FamilyBoundedBySurface S F)
    (strictFamily : ACC0FamilyHasEfficientStrictSYMPlusNormalForms F)
    (n : Nat)
    (honly : IdentityOnlyLowActionBulk I)
    (hnonzero :
      (F.circuit n).size ≠ 0 ∨
        ((strictFamily.normalForm n).normalForm).termCount ≠ 0) :
    ¬ Nonempty (NFrameTargetedStrictSYMPlusBulkCoding D I S) := by
  intro htargeted
  rcases htargeted with ⟨targeted⟩
  exact not_lowActionBulkEncoding_of_identityOnly_nonzero
    I
    (F.circuit n).size
    ((strictFamily.normalForm n).normalForm).termCount
    honly
    hnonzero
    ⟨targeted.encode F hbounded strictFamily n⟩

/-- Package a strict normal form with a bulk supplied by an N-frame encoder. -/
def nFrameCertifiedStrictSYMPlusNormalForm_of_bulkEncoder
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (encoder : NFrameStrictSYMPlusBulkEncoder D I)
    (F : ACC0LikeCircuitFamily)
    (n : Nat)
    (nf : ACC0CircuitHasStrictSYMPlusNormalForm (F.circuit n)) :
    NFrameCertifiedStrictSYMPlusNormalForm D I F n :=
  encoder.encode F n nf

/-- YBT strict normalization plus an N-frame bulk encoder gives certified
strict SYM+ extraction. -/
theorem nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_bulkEncoder
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (hYBT : StrictSYMPlusNormalizationSurface S)
    (encoder : NFrameStrictSYMPlusBulkEncoder D I) :
    NFrameLagrangianExtractsStrictSYMPlusNormalForms D I S := by
  intro F hbounded
  rcases hYBT F hbounded with ⟨strictFamily⟩
  refine ⟨{
    certified := ?_
    andGateExponent := strictFamily.andGateExponent
    andGateCount_le := ?_
  }⟩
  · intro n
    exact nFrameCertifiedStrictSYMPlusNormalForm_of_bulkEncoder
      D I encoder F n (strictFamily.normalForm n)
  · intro n
    dsimp [nFrameCertifiedStrictSYMPlusNormalForm_of_bulkEncoder]
    rw [encoder.encode_strictNormalForm F n (strictFamily.normalForm n)]
    exact strictFamily.andGateCount_le n

/-- YBT strict normalization plus targeted low-action coding gives certified
strict SYM+ extraction.  This is the faithful positive target after removing
the overstrong demand that the N-frame encode every possible natural-number
pair. -/
theorem nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_targetedCoding
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (hYBT : StrictSYMPlusNormalizationSurface S)
    (targeted : NFrameTargetedStrictSYMPlusBulkCoding D I S) :
    NFrameLagrangianExtractsStrictSYMPlusNormalForms D I S := by
  intro F hbounded
  rcases hYBT F hbounded with ⟨strictFamily⟩
  refine ⟨{
    certified := ?_
    andGateExponent := strictFamily.andGateExponent
    andGateCount_le := ?_
  }⟩
  · intro n
    let encoding := targeted.encode F hbounded strictFamily n
    exact {
      bulk := encoding.bulk
      low_action := encoding.low_action
      strictNormalForm := strictFamily.normalForm n
      reconstruction_tracks_size := encoding.reconstructionCode_eq
      description_tracks_termCount := encoding.descriptionLength_eq
    }
  · intro n
    exact strictFamily.andGateCount_le n

/-- With the current bookkeeping-free log-det action, surface normalization
alone gives certified strict SYM+ extraction: the certificate bookkeeping can be
placed on an identity-matrix bulk object.

This is a diagnostic theorem.  It shows that certified extraction is too weak
unless the action couples to the reconstruction data. -/
theorem nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_bookkeepingFree
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (hYBT : StrictSYMPlusNormalizationSurface S) :
    NFrameLagrangianExtractsStrictSYMPlusNormalForms D I S :=
  nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_targetedCoding
    D I S hYBT
    (nFrameTargetedStrictSYMPlusBulkCoding_of_bookkeepingFreeLogDetAction D I S)

/-- Algorithmic Williams/Yao-Beigel-Tarui step for strict normal forms. -/
structure StrictSYMPlusNormalFormsYieldFastACC0SAT
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S) : Prop where
  fastSAT_of_strictSYMPlusNormalForms :
    (∀ F : ACC0LikeCircuitFamily,
      ACC0FamilyBoundedBySurface S F ->
        Nonempty (ACC0FamilyHasEfficientStrictSYMPlusNormalForms F)) ->
          P.FastACC0CircuitSAT

/-- Strict SYM+ extraction is the non-vacuous way for N-frame to supply the
fast-ACC0-SAT component. -/
theorem nFrameSuppliesConcreteACC0FastCircuitSAT_of_strictSYMPlusNormalForms
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hnf : NFrameLagrangianYieldsStrictSYMPlusNormalForms D I S)
    (halg : StrictSYMPlusNormalFormsYieldFastACC0SAT S P) :
    NFrameSuppliesConcreteACC0FastCircuitSAT D I S P := by
  simpa [NFrameSuppliesConcreteACC0FastCircuitSAT,
    NFrameSuppliesFastCircuitSAT,
    concreteACC0WilliamsTarget,
    ACC0WilliamsTarget.toGodelWilliamsStep]
    using halg.fastSAT_of_strictSYMPlusNormalForms hnf

/-- The strict positive restricted route.  This is the version that remains
mathematically meaningful after the loose semantic-normal-form guard theorem. -/
theorem concreteACC0_nexp_not_subset_of_nFrameStrictSYMPlusNormalForms
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hnf : NFrameLagrangianYieldsStrictSYMPlusNormalForms D I S)
    (halg : StrictSYMPlusNormalFormsYieldFastACC0SAT S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      (concreteACC0WilliamsTarget S P).toCircuitClass :=
  concreteACC0_nexp_not_subset_of_nFrame_fastSAT_meta D I S P
    (nFrameSuppliesConcreteACC0FastCircuitSAT_of_strictSYMPlusNormalForms
      D I S P hnf halg)
    hmeta

/-- The certified N-frame extraction route: low-action N-frame bulk certificates
for strict SYM+ normal forms feed the strict Williams/ACC0 route. -/
theorem concreteACC0_nexp_not_subset_of_nFrameCertifiedStrictSYMPlusNormalForms
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hextract : NFrameLagrangianExtractsStrictSYMPlusNormalForms D I S)
    (halg : StrictSYMPlusNormalFormsYieldFastACC0SAT S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      (concreteACC0WilliamsTarget S P).toCircuitClass :=
  concreteACC0_nexp_not_subset_of_nFrameStrictSYMPlusNormalForms
    D I S P
    (nFrameLagrangianYieldsStrictSYMPlusNormalForms_of_certifiedExtraction
      D I S hextract)
    halg
    hmeta

/-- Full restricted Williams closure from the two honest ingredients:
surface YBT normalization and N-frame low-action bulk encoding. -/
theorem concreteACC0_nexp_not_subset_of_surfaceNormalization_bulkEncoder
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hYBT : StrictSYMPlusNormalizationSurface S)
    (encoder : NFrameStrictSYMPlusBulkEncoder D I)
    (halg : StrictSYMPlusNormalFormsYieldFastACC0SAT S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      (concreteACC0WilliamsTarget S P).toCircuitClass :=
  concreteACC0_nexp_not_subset_of_nFrameCertifiedStrictSYMPlusNormalForms
    D I S P
    (nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_bulkEncoder
      D I S hYBT encoder)
    halg
    hmeta

/-- Full restricted Williams closure from the weaker targeted coding theorem:
surface YBT normalization plus low-action N-frame encodings only for the
requested strict-SYM+ certificate pairs. -/
theorem concreteACC0_nexp_not_subset_of_surfaceNormalization_targetedCoding
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hYBT : StrictSYMPlusNormalizationSurface S)
    (targeted : NFrameTargetedStrictSYMPlusBulkCoding D I S)
    (halg : StrictSYMPlusNormalFormsYieldFastACC0SAT S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      (concreteACC0WilliamsTarget S P).toCircuitClass :=
  concreteACC0_nexp_not_subset_of_nFrameCertifiedStrictSYMPlusNormalForms
    D I S P
    (nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_targetedCoding
      D I S hYBT targeted)
    halg
    hmeta

/-- Restricted Williams closure using the current bookkeeping-free log-det
action.  The N-frame part here is not load-bearing: the bulk certificate is
obtained by attaching bookkeeping to the identity matrix. -/
theorem concreteACC0_nexp_not_subset_of_surfaceNormalization_bookkeepingFree
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hYBT : StrictSYMPlusNormalizationSurface S)
    (halg : StrictSYMPlusNormalFormsYieldFastACC0SAT S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      (concreteACC0WilliamsTarget S P).toCircuitClass :=
  concreteACC0_nexp_not_subset_of_surfaceNormalization_targetedCoding
    D I S P hYBT
    (nFrameTargetedStrictSYMPlusBulkCoding_of_bookkeepingFreeLogDetAction
      D I S)
    halg
    hmeta

/-! ## Faithful holographic encoder layer -/

/-- A faithful holographic encoder is the strengthened version of the bulk
space: boundary data is decoded from the bulk object, and low-action bulk can
decode only bounded-complexity boundaries.

This is the formal replacement for free bookkeeping.  The action need not expose
a numeric formula here; what matters for the route is the pricing consequence:
below the action bound, decoded boundary complexity is bounded by
`lowActionComplexityBudget`. -/
structure FaithfulHolographicEncoder
    (I : NFrameLagrangianPACInvariant) where
  Boundary : Type
  decode : NFramePACBulk I.dim -> Boundary
  boundaryComplexity : Boundary -> Nat
  lowActionComplexityBudget : Nat
  complexity_le_budget_of_lowAction :
    ∀ bulk : NFramePACBulk I.dim,
      I.action bulk <= I.actionBound ->
        boundaryComplexity (decode bulk) <= lowActionComplexityBudget

/-- A concrete low-action faithful encoding of one decoded boundary. -/
structure FaithfulLowActionBoundaryEncoding
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (boundary : H.Boundary) where
  bulk : NFramePACBulk I.dim
  low_action : I.action bulk <= I.actionBound
  decodes_to : H.decode bulk = boundary

/-- High-complexity boundaries cannot be represented by low-action faithful
bulk.  This is the formal version of "P-level observers cannot faithfully carry
NP-level boundary data." -/
theorem noLowActionEncoding_of_highBoundaryComplexity
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (boundary : H.Boundary)
    (hhigh :
      H.lowActionComplexityBudget < H.boundaryComplexity boundary) :
    ¬ Nonempty (FaithfulLowActionBoundaryEncoding I H boundary) := by
  intro hencoding
  rcases hencoding with ⟨encoding⟩
  have hle_decode :
      H.boundaryComplexity (H.decode encoding.bulk) <=
        H.lowActionComplexityBudget :=
    H.complexity_le_budget_of_lowAction encoding.bulk encoding.low_action
  have hle_boundary :
      H.boundaryComplexity boundary <= H.lowActionComplexityBudget := by
    simpa [encoding.decodes_to] using hle_decode
  exact (Nat.not_lt_of_ge hle_boundary) hhigh

/-- Equivalent pointwise form: if a bulk decodes a high-complexity boundary,
then it cannot be low action.  High-level observers may use high-action bulk;
the theorem only rules out low-action/P-level encoding. -/
theorem highBoundaryComplexity_forces_not_lowAction
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (bulk : NFramePACBulk I.dim)
    (boundary : H.Boundary)
    (hdecode : H.decode bulk = boundary)
    (hhigh :
      H.lowActionComplexityBudget < H.boundaryComplexity boundary) :
    ¬ I.action bulk <= I.actionBound := by
  intro hlow
  exact noLowActionEncoding_of_highBoundaryComplexity I H boundary hhigh
    ⟨{
      bulk := bulk
      low_action := hlow
      decodes_to := hdecode
    }⟩

/-- SAT semantics attached to a decoded holographic boundary.

The next real theorem must make this semantics nontrivial: the boundary must be
the actual Cook-Levin/SAT boundary decoded from the bulk geometry, not external
metadata. -/
structure SATHolographicBoundarySemantics
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF)
    (boundary : H.Boundary) where
  witness : RawAssignment
  machine_outputs :
    D.surface.toMachineModel.searchRun M.code phi = some witness
  witness_satisfies : Satisfies phi witness
  boundary_is_decoded_sat_boundary : Prop
  boundary_semantics_proof : boundary_is_decoded_sat_boundary

/-- A faithful low-action SAT boundary: the machine output is SAT-correct, and
the relevant SAT boundary is decoded from low-action bulk. -/
structure FaithfulLowActionSATBoundary
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF) where
  boundary : H.Boundary
  encoding : FaithfulLowActionBoundaryEncoding I H boundary
  semantics : SATHolographicBoundarySemantics D I H M phi boundary

/-- The missing SAT-side theorem: every faithfully decoded SAT boundary has
complexity above the low-action budget.

This is the real load-bearing lower bound.  It must be proved from SAT /
Cook-Levin structure, not assumed from the nonexistence of polynomial-time SAT
deciders. -/
def FaithfulSATHolographicBoundaryLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I) : Prop :=
  ∀ (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF)
    (boundary : H.Boundary),
      SATHolographicBoundarySemantics D I H M phi boundary ->
        H.lowActionComplexityBudget < H.boundaryComplexity boundary

/-- Guard theorem: any faithfully decoded SAT boundary whose complexity is
within the low-action budget refutes the SAT lower-bound socket.

So `FaithfulSATHolographicBoundaryLowerBound` cannot be proved from the
holographic interface alone; it needs a real SAT/Cook-Levin argument that rules
out such low-complexity decoded SAT boundaries. -/
theorem not_faithfulSATHolographicBoundaryLowerBound_of_lowComplexitySATBoundary
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF)
    (boundary : H.Boundary)
    (semantics : SATHolographicBoundarySemantics D I H M phi boundary)
    (hle :
      H.boundaryComplexity boundary <= H.lowActionComplexityBudget) :
    ¬ FaithfulSATHolographicBoundaryLowerBound D I H := by
  intro hlower
  exact (Nat.not_lt_of_ge hle) (hlower M phi boundary semantics)

/-- The degenerate faithful encoder: every bulk decodes to the single boundary
of complexity zero.  It satisfies the low-action pricing condition, but it
cannot support a SAT lower bound once any SAT semantics is attached to its sole
boundary.

This is a diagnostic object: it proves the lower bound must use a nontrivial
decoder/complexity model, not just the abstract word "faithful." -/
def trivialFaithfulHolographicEncoder
    (I : NFrameLagrangianPACInvariant) :
    FaithfulHolographicEncoder I where
  Boundary := Unit
  decode := fun _ => ()
  boundaryComplexity := fun _ => 0
  lowActionComplexityBudget := 0
  complexity_le_budget_of_lowAction := by
    intro _bulk _hlow
    exact Nat.le_refl 0

/-- The trivial faithful encoder refutes the SAT lower-bound socket whenever
its unique boundary is given SAT semantics. -/
theorem not_trivialFaithfulSATHolographicBoundaryLowerBound_of_semantics
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF)
    (semantics :
      SATHolographicBoundarySemantics D I
        (trivialFaithfulHolographicEncoder I) M phi ()) :
    ¬ FaithfulSATHolographicBoundaryLowerBound D I
        (trivialFaithfulHolographicEncoder I) :=
  not_faithfulSATHolographicBoundaryLowerBound_of_lowComplexitySATBoundary
    D I (trivialFaithfulHolographicEncoder I) M phi () semantics
    (Nat.le_refl 0)

/-- Consequently there is no theorem proving the SAT boundary lower bound for
every faithful encoder once even one low-complexity SAT-semantic boundary is
available.  A successful route must first specify a nontrivial encoder and then
prove its SAT boundary lower bound. -/
theorem not_universalFaithfulSATHolographicBoundaryLowerBound_of_trivialSemantics
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF)
    (semantics :
      SATHolographicBoundarySemantics D I
        (trivialFaithfulHolographicEncoder I) M phi ()) :
    ¬ (∀ H : FaithfulHolographicEncoder I,
        FaithfulSATHolographicBoundaryLowerBound D I H) := by
  intro huniversal
  exact not_trivialFaithfulSATHolographicBoundaryLowerBound_of_semantics
    D I M phi semantics
    (huniversal (trivialFaithfulHolographicEncoder I))

/-! ## Cook-Levin boundary projection and fixed-budget guard -/

/-- The satisfiable empty CNF on `n` variables.  It is used only as a
size-growth witness: SAT has satisfiable formulas of arbitrarily large
syntactic size. -/
def emptySatisfiableCNF (n : Nat) : CNF where
  vars := n
  clauses := []

theorem emptySatisfiableCNF_size
    (n : Nat) :
    (emptySatisfiableCNF n).size = n := by
  simp [emptySatisfiableCNF, CNF.size]

theorem emptySatisfiableCNF_satisfiable
    (n : Nat) :
    Satisfiable (emptySatisfiableCNF n) := by
  refine ⟨List.replicate n false, ?_⟩
  simp [Satisfies, emptySatisfiableCNF, CNF.eval]

/-- SAT has satisfiable CNFs above any fixed syntactic-size budget. -/
theorem exists_satisfiableCNF_size_gt
    (budget : Nat) :
    ∃ phi : CNF, Satisfiable phi ∧ budget < phi.size := by
  refine ⟨emptySatisfiableCNF (budget + 1), ?_, ?_⟩
  · exact emptySatisfiableCNF_satisfiable (budget + 1)
  · rw [emptySatisfiableCNF_size]
    exact Nat.lt_succ_self budget

/-- A Cook-Levin-style interpretation of decoded holographic boundaries.

This is the first concrete nontrivial shape: a decoded boundary must expose the
formula it is about, the produced witness, and the machine code.  The key
pricing assumption is intentionally modest: boundary complexity is at least the
syntactic size of the decoded formula. -/
structure CookLevinBoundaryProjection
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I) where
  decodedFormula : H.Boundary -> CNF
  decodedWitness : H.Boundary -> RawAssignment
  decodedMachineCode : H.Boundary -> Nat
  formula_size_le_complexity :
    ∀ boundary : H.Boundary,
      (decodedFormula boundary).size <= H.boundaryComplexity boundary

/-- A low-action SAT boundary whose decoded Cook-Levin formula is the actual
formula being solved. -/
structure CookLevinFaithfulLowActionSATBoundary
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (P : CookLevinBoundaryProjection I H)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF) where
  boundary : H.Boundary
  encoding : FaithfulLowActionBoundaryEncoding I H boundary
  semantics : SATHolographicBoundarySemantics D I H M phi boundary
  decoded_formula_eq : P.decodedFormula boundary = phi
  decoded_witness_eq : P.decodedWitness boundary = semantics.witness
  decoded_machineCode_eq : P.decodedMachineCode boundary = M.code

/-- If decoded boundary complexity prices even the formula size, then a
low-action boundary cannot faithfully decode a formula larger than the
low-action budget.

This is the fixed-budget obstruction: it is a real theorem, but it also shows
the current faithful interface is too coarse for P-vs-NP.  A realistic observer
calibration needs a length-indexed polynomial budget, not one global constant. -/
theorem noCookLevinLowActionBoundary_of_formula_size_gt_budget
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (P : CookLevinBoundaryProjection I H)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF)
    (hlarge : H.lowActionComplexityBudget < phi.size) :
    ¬ Nonempty (CookLevinFaithfulLowActionSATBoundary D I H P M phi) := by
  intro hboundary
  rcases hboundary with ⟨B⟩
  have hcomplexity_le_budget :
      H.boundaryComplexity B.boundary <= H.lowActionComplexityBudget := by
    have hdecoded :=
      H.complexity_le_budget_of_lowAction B.encoding.bulk
        B.encoding.low_action
    simpa [B.encoding.decodes_to] using hdecoded
  have hformula_le_complexity :
      phi.size <= H.boundaryComplexity B.boundary := by
    simpa [B.decoded_formula_eq] using
      P.formula_size_le_complexity B.boundary
  exact (Nat.not_lt_of_ge
    (Nat.le_trans hformula_le_complexity hcomplexity_le_budget)) hlarge

/-- Strong P-side Cook-Levin transport for the fixed-budget faithful interface:
every satisfiable formula gets a faithful low-action decoded boundary.

This is intentionally named as a strong transport because, with formula-size
pricing, it is already impossible over arbitrarily large formulas. -/
structure FixedBudgetPLevelCookLevinBoundaryTransport
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (P : CookLevinBoundaryProjection I H) : Prop where
  transport :
    ∀ M : SearchMachine D.surface.toMachineModel,
      SearchCorrect D.surface.toMachineModel M ->
        ∀ phi : CNF,
          Satisfiable phi ->
            Nonempty
              (CookLevinFaithfulLowActionSATBoundary D I H P M phi)

/-- The fixed-budget faithful Cook-Levin transport is impossible for any
complete SAT search machine, because satisfiable formulas have unbounded
syntactic size. -/
theorem forall_not_searchCorrect_of_fixedBudgetCookLevinTransport
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (P : CookLevinBoundaryProjection I H)
    (htransport : FixedBudgetPLevelCookLevinBoundaryTransport D I H P) :
    ∀ M : SearchMachine D.surface.toMachineModel,
      ¬ SearchCorrect D.surface.toMachineModel M := by
  intro M hcorrect
  rcases exists_satisfiableCNF_size_gt H.lowActionComplexityBudget with
    ⟨phi, hsat, hlarge⟩
  exact noCookLevinLowActionBoundary_of_formula_size_gt_budget
    D I H P M phi hlarge
    (htransport.transport M hcorrect phi hsat)

/-- Conditional closure from the overstrong fixed-budget Cook-Levin transport.
This is a guard theorem, not the final route: it explains why the next faithful
encoder must be length-indexed/polynomially calibrated. -/
theorem noCanonicalSATDecisionInP_of_fixedBudgetCookLevinTransport
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (P : CookLevinBoundaryProjection I H)
    (htransport : FixedBudgetPLevelCookLevinBoundaryTransport D I H P) :
    ¬ CanonicalSATDecisionInP D.surface :=
  canonicalNoDecider_of_deepSATSearch D.surface
    ((canonicalDeepSATSearch_iff_forall_not_searchCorrect D.surface).mpr
      (forall_not_searchCorrect_of_fixedBudgetCookLevinTransport
        D I H P htransport))

/-! ## Length-indexed faithful holography -/

/-- Length-indexed faithful holographic encoder.

This is the corrected version of the faithful interface after the fixed-budget
guard above: low-action decoding is allowed a budget depending on the decoded
boundary length, and that budget must be polynomial. -/
structure LengthIndexedFaithfulHolographicEncoder
    (I : NFrameLagrangianPACInvariant) where
  Boundary : Type
  decode : NFramePACBulk I.dim -> Boundary
  boundaryLength : Boundary -> Nat
  boundaryComplexity : Boundary -> Nat
  lowActionBudget : Nat -> Nat
  lowActionBudget_poly : IsPolynomialBudget lowActionBudget
  complexity_le_budget_of_lowAction :
    ∀ bulk : NFramePACBulk I.dim,
      I.action bulk <= I.actionBound ->
        boundaryComplexity (decode bulk) <=
          lowActionBudget (boundaryLength (decode bulk))

/-- A low-action encoding of one boundary in the length-indexed model. -/
structure LengthIndexedLowActionBoundaryEncoding
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (boundary : H.Boundary) where
  bulk : NFramePACBulk I.dim
  low_action : I.action bulk <= I.actionBound
  decodes_to : H.decode bulk = boundary

/-- Low-action length-indexed bulk cannot decode a boundary whose complexity
exceeds the budget at its own length. -/
theorem noLengthIndexedLowActionEncoding_of_complexity_gt_budget
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (boundary : H.Boundary)
    (hgt :
      H.lowActionBudget (H.boundaryLength boundary) <
        H.boundaryComplexity boundary) :
    ¬ Nonempty (LengthIndexedLowActionBoundaryEncoding I H boundary) := by
  intro hencoding
  rcases hencoding with ⟨encoding⟩
  have hle_decode :
      H.boundaryComplexity (H.decode encoding.bulk) <=
        H.lowActionBudget (H.boundaryLength (H.decode encoding.bulk)) :=
    H.complexity_le_budget_of_lowAction encoding.bulk encoding.low_action
  have hle_boundary :
      H.boundaryComplexity boundary <=
        H.lowActionBudget (H.boundaryLength boundary) := by
    simpa [encoding.decodes_to] using hle_decode
  exact (Nat.not_lt_of_ge hle_boundary) hgt

/-- SAT semantics attached to a decoded boundary in the length-indexed model. -/
structure LengthIndexedSATHolographicBoundarySemantics
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF)
    (boundary : H.Boundary) where
  witness : RawAssignment
  machine_outputs :
    D.surface.toMachineModel.searchRun M.code phi = some witness
  witness_satisfies : Satisfies phi witness
  boundary_is_decoded_sat_boundary : Prop
  boundary_semantics_proof : boundary_is_decoded_sat_boundary

/-- A length-indexed SAT boundary family: one semantic boundary at each length.
The `length_eq` field is what lets polynomial P-side budgets and
superpolynomial SAT-side lower bounds meet on the same `n`. -/
structure LengthIndexedSATBoundaryFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel) where
  boundaryAt : Nat -> H.Boundary
  phiAt : Nat -> CNF
  semanticsAt :
    ∀ n : Nat,
      LengthIndexedSATHolographicBoundarySemantics
        D I H M (phiAt n) (boundaryAt n)
  length_eq :
    ∀ n : Nat, H.boundaryLength (boundaryAt n) = n

/-- A P-level low-action SAT boundary family: the semantic boundaries are
actually carried by low-action bulk at every length. -/
structure LengthIndexedLowActionSATBoundaryFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel) where
  boundaryAt : Nat -> H.Boundary
  phiAt : Nat -> CNF
  encodingAt :
    ∀ n : Nat,
      LengthIndexedLowActionBoundaryEncoding I H (boundaryAt n)
  semanticsAt :
    ∀ n : Nat,
      LengthIndexedSATHolographicBoundarySemantics
        D I H M (phiAt n) (boundaryAt n)
  length_eq :
    ∀ n : Nat, H.boundaryLength (boundaryAt n) = n

/-- Forget low-action encodings and keep only the SAT-semantic boundary family.
-/
def LengthIndexedLowActionSATBoundaryFamily.toSATBoundaryFamily
    {D : DescribedCanonicalSurface}
    {I : NFrameLagrangianPACInvariant}
    {H : LengthIndexedFaithfulHolographicEncoder I}
    {M : SearchMachine D.surface.toMachineModel}
    (F : LengthIndexedLowActionSATBoundaryFamily D I H M) :
    LengthIndexedSATBoundaryFamily D I H M where
  boundaryAt := F.boundaryAt
  phiAt := F.phiAt
  semanticsAt := F.semanticsAt
  length_eq := F.length_eq

/-- The SAT-side lower bound in the corrected length-indexed model.

Every semantic SAT boundary family has complexity that eventually beats every
polynomial.  This is the real mathematical lower-bound target; it is not proved
by the interface. -/
def LengthIndexedSATHolographicBoundaryLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) : Prop :=
  ∀ (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedSATBoundaryFamily D I H M)
    (k c : Nat),
      ∃ n : Nat,
        c * (n + 1) ^ k < H.boundaryComplexity (F.boundaryAt n)

/-- A low-complexity semantic boundary family refutes the length-indexed SAT
lower-bound socket. -/
theorem not_lengthIndexedSATHolographicBoundaryLowerBound_of_polyBoundedFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedSATBoundaryFamily D I H M)
    (k c : Nat)
    (hpoly :
      ∀ n : Nat,
        H.boundaryComplexity (F.boundaryAt n) <= c * (n + 1) ^ k) :
    ¬ LengthIndexedSATHolographicBoundaryLowerBound D I H := by
  intro hlower
  rcases hlower M F k c with ⟨n, hgt⟩
  exact (Nat.not_lt_of_ge (hpoly n)) hgt

/-- Degenerate length-indexed encoder: boundary length is real, but complexity
is identically zero.  It satisfies the abstract P-side budget condition and
therefore demonstrates again that the SAT lower bound needs a nontrivial
Cook-Levin decoder/complexity theorem. -/
def trivialLengthIndexedFaithfulHolographicEncoder
    (I : NFrameLagrangianPACInvariant) :
    LengthIndexedFaithfulHolographicEncoder I where
  Boundary := Nat
  decode := fun _ => 0
  boundaryLength := fun n => n
  boundaryComplexity := fun _ => 0
  lowActionBudget := fun _ => 0
  lowActionBudget_poly := by
    refine ⟨0, 0, ?_⟩
    intro n
    exact Nat.le_refl 0
  complexity_le_budget_of_lowAction := by
    intro _bulk _hlow
    exact Nat.le_refl 0

/-- If a zero-complexity semantic family is available, the length-indexed SAT
lower bound is false. -/
theorem not_lengthIndexedSATHolographicBoundaryLowerBound_of_zeroComplexityFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedSATBoundaryFamily D I H M)
    (hzero :
      ∀ n : Nat, H.boundaryComplexity (F.boundaryAt n) = 0) :
    ¬ LengthIndexedSATHolographicBoundaryLowerBound D I H := by
  intro hlower
  rcases hlower M F 0 0 with ⟨n, hgt⟩
  have hgt0 : 0 < 0 := by
    simp at hgt
    rw [hzero n] at hgt
    exact hgt
  exact Nat.lt_irrefl 0 hgt0

/-- P-side transport in the length-indexed model: every complete P-level SAT
search observer produces a low-action SAT boundary family. -/
structure LengthIndexedPLevelSATObserverTransport
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) : Prop where
  transport :
    ∀ M : SearchMachine D.surface.toMachineModel,
      SearchCorrect D.surface.toMachineModel M ->
        Nonempty (LengthIndexedLowActionSATBoundaryFamily D I H M)

/-- Length-indexed SAT lower bound forbids a P-side low-action boundary family.
-/
theorem noLengthIndexedLowActionSATBoundaryFamily_of_lowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hlower : LengthIndexedSATHolographicBoundaryLowerBound D I H)
    (M : SearchMachine D.surface.toMachineModel) :
    ¬ Nonempty (LengthIndexedLowActionSATBoundaryFamily D I H M) := by
  intro hfamily
  rcases hfamily with ⟨F⟩
  rcases H.lowActionBudget_poly with ⟨k, c, hbudget_poly⟩
  rcases hlower M F.toSATBoundaryFamily k c with ⟨n, hgt⟩
  have hcomplexity_le_budget :
      H.boundaryComplexity (F.boundaryAt n) <= H.lowActionBudget n := by
    have hdecoded :=
      H.complexity_le_budget_of_lowAction
        (F.encodingAt n).bulk
        (F.encodingAt n).low_action
    simpa [(F.encodingAt n).decodes_to, F.length_eq n] using hdecoded
  have hcomplexity_le_poly :
      H.boundaryComplexity (F.boundaryAt n) <= c * (n + 1) ^ k :=
    Nat.le_trans hcomplexity_le_budget (hbudget_poly n)
  exact (Nat.not_lt_of_ge hcomplexity_le_poly) hgt

/-- Corrected length-indexed closure: P-side low-action transport plus a
superpolynomial SAT-boundary lower bound rules out complete canonical SAT
search. -/
theorem forall_not_searchCorrect_of_lengthIndexedFaithfulHolographicSATLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (htransport : LengthIndexedPLevelSATObserverTransport D I H)
    (hlower : LengthIndexedSATHolographicBoundaryLowerBound D I H) :
    ∀ M : SearchMachine D.surface.toMachineModel,
      ¬ SearchCorrect D.surface.toMachineModel M := by
  intro M hcorrect
  exact noLengthIndexedLowActionSATBoundaryFamily_of_lowerBound
    D I H hlower M
    (htransport.transport M hcorrect)

/-- Canonical deep SAT search follows from the corrected length-indexed
holographic route. -/
theorem canonicalDeepSATSearch_of_lengthIndexedFaithfulHolographicSATLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (htransport : LengthIndexedPLevelSATObserverTransport D I H)
    (hlower : LengthIndexedSATHolographicBoundaryLowerBound D I H) :
    CanonicalDeepSATSearch D.surface :=
  (canonicalDeepSATSearch_iff_forall_not_searchCorrect D.surface).mpr
    (forall_not_searchCorrect_of_lengthIndexedFaithfulHolographicSATLowerBound
      D I H htransport hlower)

/-- Conditional P-vs-NP-facing closure for the corrected length-indexed
holographic route. -/
theorem noCanonicalSATDecisionInP_of_lengthIndexedFaithfulHolographicSATLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (htransport : LengthIndexedPLevelSATObserverTransport D I H)
    (hlower : LengthIndexedSATHolographicBoundaryLowerBound D I H) :
    ¬ CanonicalSATDecisionInP D.surface :=
  canonicalNoDecider_of_deepSATSearch D.surface
    (canonicalDeepSATSearch_of_lengthIndexedFaithfulHolographicSATLowerBound
      D I H htransport hlower)

/-! ## Concrete formula-size Cook-Levin length-indexed encoder -/

/-- A first concrete Cook-Levin length-indexed boundary.

It records the decoded formula and a witness field.  Its complexity below is
only formula size, so this is deliberately a weak Cook-Levin projection rather
than the missing high-complexity SAT invariant. -/
structure CookLevinFormulaSizeBoundary where
  formula : CNF
  witness : RawAssignment

/-- The concrete formula-size Cook-Levin encoder.

Low-action decoding is polynomial because the decoded complexity is just the
decoded formula size.  The decoder obtains a satisfiable empty formula of size
`descriptionLength`; this makes the P-side transport constructible from the
current bulk object, but it also makes the SAT-side lower bound false for this
encoder. -/
def cookLevinFormulaSizeLengthIndexedEncoder
    (I : NFrameLagrangianPACInvariant) :
    LengthIndexedFaithfulHolographicEncoder I where
  Boundary := CookLevinFormulaSizeBoundary
  decode := fun bulk => {
    formula := emptySatisfiableCNF bulk.descriptionLength
    witness := List.replicate bulk.descriptionLength false
  }
  boundaryLength := fun boundary => boundary.formula.size
  boundaryComplexity := fun boundary => boundary.formula.size
  lowActionBudget := fun n => n
  lowActionBudget_poly := by
    refine ⟨1, 1, ?_⟩
    intro n
    simp
  complexity_le_budget_of_lowAction := by
    intro bulk _hlow
    simp [emptySatisfiableCNF_size]

/-- For the formula-size encoder, boundary complexity is exactly boundary
length. -/
theorem cookLevinFormulaSize_complexity_eq_length
    (I : NFrameLagrangianPACInvariant)
    (boundary : (cookLevinFormulaSizeLengthIndexedEncoder I).Boundary) :
    (cookLevinFormulaSizeLengthIndexedEncoder I).boundaryComplexity boundary =
      (cookLevinFormulaSizeLengthIndexedEncoder I).boundaryLength boundary :=
  rfl

/-- Build the low-action family carried by identity-matrix bulk with
length-coded bookkeeping.  This proves the P-side transport for the concrete
formula-size encoder, but only because the current action does not price the
length bookkeeping. -/
noncomputable def cookLevinFormulaSizeLowActionFamily_of_searchCorrect
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    LengthIndexedLowActionSATBoundaryFamily D I
      (cookLevinFormulaSizeLengthIndexedEncoder I) M where
  boundaryAt := fun n =>
    (cookLevinFormulaSizeLengthIndexedEncoder I).decode
      (NFramePACBulk.identityMatrixWithBookkeeping I.dim M.code n)
  phiAt := fun n => emptySatisfiableCNF n
  encodingAt := by
    intro n
    exact {
      bulk := NFramePACBulk.identityMatrixWithBookkeeping I.dim M.code n
      low_action := by
        simpa [NFrameLagrangianPACInvariant.action, nFramePACLogDetAction,
          NFramePACBulk.identity, NFramePACBulk.identityMatrixWithBookkeeping]
          using I.identity_low_action
      decodes_to := rfl
    }
  semanticsAt := by
    intro n
    let phi := emptySatisfiableCNF n
    have hsat : Satisfiable phi := emptySatisfiableCNF_satisfiable n
    let witness := Classical.choose (hcorrect phi hsat)
    have hwitness := Classical.choose_spec (hcorrect phi hsat)
    exact {
      witness := witness
      machine_outputs := hwitness.1
      witness_satisfies := hwitness.2
      boundary_is_decoded_sat_boundary := True
      boundary_semantics_proof := trivial
    }
  length_eq := by
    intro n
    simp [cookLevinFormulaSizeLengthIndexedEncoder,
      NFramePACBulk.identityMatrixWithBookkeeping, emptySatisfiableCNF_size]

/-- The concrete formula-size encoder satisfies the P-side transport socket. -/
noncomputable def cookLevinFormulaSize_pLevelTransport
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant) :
    LengthIndexedPLevelSATObserverTransport D I
      (cookLevinFormulaSizeLengthIndexedEncoder I) where
  transport := by
    intro M hcorrect
    exact ⟨cookLevinFormulaSizeLowActionFamily_of_searchCorrect
      D I M hcorrect⟩

/-- Any SAT boundary family for the formula-size encoder is polynomially
bounded by its length.  Thus this concrete encoder cannot support the required
superpolynomial SAT-side lower bound. -/
theorem not_lengthIndexedSATHolographicBoundaryLowerBound_cookLevinFormulaSize
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedSATBoundaryFamily D I
      (cookLevinFormulaSizeLengthIndexedEncoder I) M) :
    ¬ LengthIndexedSATHolographicBoundaryLowerBound D I
      (cookLevinFormulaSizeLengthIndexedEncoder I) := by
  exact
    not_lengthIndexedSATHolographicBoundaryLowerBound_of_polyBoundedFamily
      D I (cookLevinFormulaSizeLengthIndexedEncoder I) M F 1 1
      (by
        intro n
        rw [cookLevinFormulaSize_complexity_eq_length I (F.boundaryAt n)]
        rw [F.length_eq n]
        simp)

/-- In particular, if a complete SAT search machine exists, the formula-size
Cook-Levin encoder's own P-side family refutes its SAT lower-bound socket. -/
theorem not_lengthIndexedSATHolographicBoundaryLowerBound_cookLevinFormulaSize_of_searchCorrect
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    ¬ LengthIndexedSATHolographicBoundaryLowerBound D I
      (cookLevinFormulaSizeLengthIndexedEncoder I) :=
  not_lengthIndexedSATHolographicBoundaryLowerBound_cookLevinFormulaSize
    D I M
    (cookLevinFormulaSizeLowActionFamily_of_searchCorrect
      D I M hcorrect).toSATBoundaryFamily

/-! ## Semantic-orbit Cook-Levin boundary guard -/

/-- A deliberately stronger Cook-Levin boundary complexity scale.

Unlike formula size, `semanticOrbitComplexity n = (n+1)^(n+1)` beats every
fixed polynomial in `n`.  It models pricing the whole semantic/certificate
orbit rather than only the printed CNF. -/
def cookLevinSemanticOrbitComplexity (n : Nat) : Nat :=
  (n + 1) ^ (n + 1)

/-- The semantic-orbit scale is superpolynomial in the length parameter. -/
theorem cookLevinSemanticOrbitComplexity_beats_polynomial
    (k c : Nat) :
    ∃ n : Nat,
      c * (n + 1) ^ k < cookLevinSemanticOrbitComplexity n := by
  let n := k + c + 1
  refine ⟨n, ?_⟩
  have hc_le : c <= n + 1 := by
    dsimp [n]
    omega
  have hk_succ_lt : k + 1 < n + 1 := by
    dsimp [n]
    omega
  have hb_gt_one : 1 < n + 1 := by
    dsimp [n]
    omega
  have hmul :
      c * (n + 1) ^ k <= (n + 1) * (n + 1) ^ k :=
    Nat.mul_le_mul_right ((n + 1) ^ k) hc_le
  have hsucc :
      (n + 1) * (n + 1) ^ k = (n + 1) ^ (k + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hpow :
      (n + 1) ^ (k + 1) < (n + 1) ^ (n + 1) :=
    Nat.pow_lt_pow_right hb_gt_one hk_succ_lt
  exact lt_of_le_of_lt (hmul.trans_eq hsucc) hpow

/-- Semantic-orbit pricing for an arbitrary length-indexed encoder.

This is the exact strengthened SAT-side condition that formula size failed:
every SAT-semantic boundary family must price at least the full
`(n+1)^(n+1)` orbit at length `n`. -/
def LengthIndexedCookLevinSemanticOrbitPricing
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) : Prop :=
  ∀ (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedSATBoundaryFamily D I H M)
    (n : Nat),
      cookLevinSemanticOrbitComplexity n <=
        H.boundaryComplexity (F.boundaryAt n)

/-- Semantic-orbit pricing implies the SAT-side superpolynomial lower-bound
socket. -/
theorem lengthIndexedSATHolographicBoundaryLowerBound_of_semanticOrbitPricing
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hpricing : LengthIndexedCookLevinSemanticOrbitPricing D I H) :
    LengthIndexedSATHolographicBoundaryLowerBound D I H := by
  intro M F k c
  rcases cookLevinSemanticOrbitComplexity_beats_polynomial k c with
    ⟨n, hgt⟩
  exact ⟨n, lt_of_lt_of_le hgt (hpricing M F n)⟩

/-- If semantic-orbit pricing holds, no low-action P-side family can exist.

This is the core guard: pricing enough semantic orbit to prove the SAT lower
bound immediately conflicts with polynomial low-action decoding. -/
theorem noLengthIndexedLowActionSATBoundaryFamily_of_semanticOrbitPricing
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hpricing : LengthIndexedCookLevinSemanticOrbitPricing D I H)
    (M : SearchMachine D.surface.toMachineModel) :
    ¬ Nonempty (LengthIndexedLowActionSATBoundaryFamily D I H M) :=
  noLengthIndexedLowActionSATBoundaryFamily_of_lowerBound D I H
    (lengthIndexedSATHolographicBoundaryLowerBound_of_semanticOrbitPricing
      D I H hpricing) M

/-- Consequently, if a complete SAT search machine exists, semantic-orbit
pricing refutes the P-side observer transport. -/
theorem not_lengthIndexedPLevelSATObserverTransport_of_semanticOrbitPricing
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hpricing : LengthIndexedCookLevinSemanticOrbitPricing D I H)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    ¬ LengthIndexedPLevelSATObserverTransport D I H := by
  intro htransport
  exact noLengthIndexedLowActionSATBoundaryFamily_of_semanticOrbitPricing
    D I H hpricing M
    (htransport.transport M hcorrect)

/-- A concrete semantic-orbit boundary. -/
structure CookLevinSemanticOrbitBoundary where
  formula : CNF
  witness : RawAssignment

/-- The concrete semantic-orbit encoder.

It has a genuine superpolynomial SAT-side complexity scale, but its low-action
decoder only emits the zero-length reference boundary.  This makes the SAT side
provable while exposing why the P-side transport cannot be obtained from this
measure. -/
def cookLevinSemanticOrbitLengthIndexedEncoder
    (I : NFrameLagrangianPACInvariant) :
    LengthIndexedFaithfulHolographicEncoder I where
  Boundary := CookLevinSemanticOrbitBoundary
  decode := fun _ => {
    formula := emptySatisfiableCNF 0
    witness := []
  }
  boundaryLength := fun boundary => boundary.formula.size
  boundaryComplexity := fun boundary =>
    cookLevinSemanticOrbitComplexity boundary.formula.size
  lowActionBudget := fun _ => 1
  lowActionBudget_poly := by
    refine ⟨0, 1, ?_⟩
    intro n
    simp
  complexity_le_budget_of_lowAction := by
    intro _bulk _hlow
    simp [cookLevinSemanticOrbitComplexity, emptySatisfiableCNF_size]

/-- For the semantic-orbit encoder, complexity is exactly the self-powered
length scale. -/
theorem cookLevinSemanticOrbit_complexity_eq_selfPow
    (I : NFrameLagrangianPACInvariant)
    (boundary : (cookLevinSemanticOrbitLengthIndexedEncoder I).Boundary) :
    (cookLevinSemanticOrbitLengthIndexedEncoder I).boundaryComplexity boundary =
      cookLevinSemanticOrbitComplexity
        ((cookLevinSemanticOrbitLengthIndexedEncoder I).boundaryLength
          boundary) :=
  rfl

/-- The concrete semantic-orbit encoder satisfies semantic-orbit pricing. -/
theorem cookLevinSemanticOrbit_pricing
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant) :
    LengthIndexedCookLevinSemanticOrbitPricing D I
      (cookLevinSemanticOrbitLengthIndexedEncoder I) := by
  intro M F n
  rw [cookLevinSemanticOrbit_complexity_eq_selfPow I (F.boundaryAt n)]
  rw [F.length_eq n]

/-- Hence the concrete semantic-orbit encoder proves the SAT-side lower-bound
socket. -/
theorem lengthIndexedSATHolographicBoundaryLowerBound_cookLevinSemanticOrbit
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant) :
    LengthIndexedSATHolographicBoundaryLowerBound D I
      (cookLevinSemanticOrbitLengthIndexedEncoder I) :=
  lengthIndexedSATHolographicBoundaryLowerBound_of_semanticOrbitPricing
    D I (cookLevinSemanticOrbitLengthIndexedEncoder I)
    (cookLevinSemanticOrbit_pricing D I)

/-- But the same semantic-orbit encoder admits no low-action SAT boundary
family at all: already at length one, complexity exceeds the constant
low-action budget. -/
theorem noLengthIndexedLowActionSATBoundaryFamily_cookLevinSemanticOrbit
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel) :
    ¬ Nonempty (LengthIndexedLowActionSATBoundaryFamily D I
      (cookLevinSemanticOrbitLengthIndexedEncoder I) M) := by
  exact noLengthIndexedLowActionSATBoundaryFamily_of_semanticOrbitPricing
    D I (cookLevinSemanticOrbitLengthIndexedEncoder I)
    (cookLevinSemanticOrbit_pricing D I) M

/-- Therefore this stronger semantic-orbit measure cannot supply the P-side
transport in the presence of any complete SAT search machine. -/
theorem not_cookLevinSemanticOrbit_pLevelTransport_of_searchCorrect
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    ¬ LengthIndexedPLevelSATObserverTransport D I
      (cookLevinSemanticOrbitLengthIndexedEncoder I) :=
  not_lengthIndexedPLevelSATObserverTransport_of_semanticOrbitPricing
    D I (cookLevinSemanticOrbitLengthIndexedEncoder I)
    (cookLevinSemanticOrbit_pricing D I) M hcorrect

/-- Conditional closure if one could nevertheless prove the missing P-side
transport for the semantic-orbit encoder.  This names the remaining theorem
without asserting it. -/
theorem noCanonicalSATDecisionInP_of_cookLevinSemanticOrbit_transport
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (htransport : LengthIndexedPLevelSATObserverTransport D I
      (cookLevinSemanticOrbitLengthIndexedEncoder I)) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_lengthIndexedFaithfulHolographicSATLowerBound
    D I (cookLevinSemanticOrbitLengthIndexedEncoder I) htransport
    (lengthIndexedSATHolographicBoundaryLowerBound_cookLevinSemanticOrbit
      D I)

/-! ## Length-only middle-invariant no-go -/

/-- A length-indexed encoder is length-only when its complexity factors through
one scalar growth function of the boundary length.

This covers formula-size, semantic-orbit, and every attempted middle scale such
as `n^log n` if the invariant only reads boundary length. -/
def BoundaryComplexityFactorsThroughLength
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat) : Prop :=
  ∀ boundary : H.Boundary,
    H.boundaryComplexity boundary = scale (H.boundaryLength boundary)

/-- A scale is polynomially bounded in the same sense used by the P-side
observer budget. -/
def ScalePolynomialBounded (scale : Nat -> Nat) : Prop :=
  ∃ k c : Nat, ∀ n : Nat, scale n <= c * (n + 1) ^ k

/-- A scale is superpolynomial if it eventually beats every fixed polynomial
at some length.  This matches `LengthIndexedSATHolographicBoundaryLowerBound`.
-/
def ScaleSuperpolynomial (scale : Nat -> Nat) : Prop :=
  ∀ k c : Nat, ∃ n : Nat, c * (n + 1) ^ k < scale n

/-- Polynomially bounded length-only complexity cannot prove the SAT-side
lower-bound socket once a SAT-semantic family exists. -/
theorem not_lengthIndexedSATHolographicBoundaryLowerBound_of_lengthOnlyPolyScale
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat)
    (hfactors : BoundaryComplexityFactorsThroughLength I H scale)
    (hpoly : ScalePolynomialBounded scale)
    (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedSATBoundaryFamily D I H M) :
    ¬ LengthIndexedSATHolographicBoundaryLowerBound D I H := by
  rcases hpoly with ⟨k, c, hpoly_bound⟩
  exact
    not_lengthIndexedSATHolographicBoundaryLowerBound_of_polyBoundedFamily
      D I H M F k c
      (by
        intro n
        rw [hfactors (F.boundaryAt n), F.length_eq n]
        exact hpoly_bound n)

/-- Superpolynomial length-only complexity is enough to prove the SAT-side
lower-bound socket. -/
theorem lengthIndexedSATHolographicBoundaryLowerBound_of_lengthOnlySuperpolyScale
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat)
    (hfactors : BoundaryComplexityFactorsThroughLength I H scale)
    (hsuper : ScaleSuperpolynomial scale) :
    LengthIndexedSATHolographicBoundaryLowerBound D I H := by
  intro M F k c
  rcases hsuper k c with ⟨n, hgt⟩
  refine ⟨n, ?_⟩
  rwa [hfactors (F.boundaryAt n), F.length_eq n]

/-- But once the length-only scale is superpolynomial, the same generic
lower-bound argument forbids every low-action SAT boundary family. -/
theorem noLengthIndexedLowActionSATBoundaryFamily_of_lengthOnlySuperpolyScale
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat)
    (hfactors : BoundaryComplexityFactorsThroughLength I H scale)
    (hsuper : ScaleSuperpolynomial scale)
    (M : SearchMachine D.surface.toMachineModel) :
    ¬ Nonempty (LengthIndexedLowActionSATBoundaryFamily D I H M) :=
  noLengthIndexedLowActionSATBoundaryFamily_of_lowerBound D I H
    (lengthIndexedSATHolographicBoundaryLowerBound_of_lengthOnlySuperpolyScale
      D I H scale hfactors hsuper) M

/-- Superpolynomial length-only complexity refutes the P-side transport in the
presence of any complete SAT search machine. -/
theorem not_lengthIndexedPLevelSATObserverTransport_of_lengthOnlySuperpolyScale
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat)
    (hfactors : BoundaryComplexityFactorsThroughLength I H scale)
    (hsuper : ScaleSuperpolynomial scale)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    ¬ LengthIndexedPLevelSATObserverTransport D I H := by
  intro htransport
  exact noLengthIndexedLowActionSATBoundaryFamily_of_lengthOnlySuperpolyScale
    D I H scale hfactors hsuper M
    (htransport.transport M hcorrect)

/-- A named middle-invariant package for the length-only experiment.

It is deliberately not asserted.  The two guard theorems below explain why
length-only middle attempts do not solve the problem: polynomial scales lose
the SAT lower bound, while superpolynomial scales lose the P-side transport
unless no SAT search machine exists. -/
structure LengthOnlyCookLevinMiddleInvariant
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat) : Prop where
  factorsThroughLength : BoundaryComplexityFactorsThroughLength I H scale
  pSide : LengthIndexedPLevelSATObserverTransport D I H
  satSide : LengthIndexedSATHolographicBoundaryLowerBound D I H

/-- No polynomially bounded length-only middle invariant can survive a
SAT-semantic boundary family. -/
theorem not_lengthOnlyCookLevinMiddleInvariant_of_polyScale
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat)
    (hpoly : ScalePolynomialBounded scale)
    (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedSATBoundaryFamily D I H M) :
    ¬ LengthOnlyCookLevinMiddleInvariant D I H scale := by
  intro hmiddle
  exact not_lengthIndexedSATHolographicBoundaryLowerBound_of_lengthOnlyPolyScale
    D I H scale hmiddle.factorsThroughLength hpoly M F hmiddle.satSide

/-- No superpolynomial length-only middle invariant can coexist with a complete
SAT search machine.  That is exactly the P-vs-NP-strength horn. -/
theorem not_lengthOnlyCookLevinMiddleInvariant_of_superpolyScale_searchCorrect
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (scale : Nat -> Nat)
    (hsuper : ScaleSuperpolynomial scale)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    ¬ LengthOnlyCookLevinMiddleInvariant D I H scale := by
  intro hmiddle
  exact not_lengthIndexedPLevelSATObserverTransport_of_lengthOnlySuperpolyScale
    D I H scale hmiddle.factorsThroughLength hsuper M hcorrect hmiddle.pSide

/-! ## Instance-sensitive middle-invariant pressure point -/

/-- Positive instance-sensitivity: two boundaries of the same length are priced
differently.

This is the minimal formal way to say the invariant is not merely a function of
length.  It is necessary for any surviving middle invariant, but it is not
sufficient by itself. -/
def BoundaryComplexityIsInstanceSensitive
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) : Prop :=
  ∃ b1 b2 : H.Boundary,
    H.boundaryLength b1 = H.boundaryLength b2 ∧
      H.boundaryComplexity b1 ≠ H.boundaryComplexity b2

/-- A SAT-semantic boundary family whose complexity is polynomially bounded.

This is the obstruction any universal SAT-side lower bound must rule out.  It
can arise from genuinely easy SAT instances, or from a P-side low-action
transport if a complete SAT search machine exists. -/
structure PolynomiallyBoundedSATBoundaryFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel) where
  family : LengthIndexedSATBoundaryFamily D I H M
  k : Nat
  c : Nat
  complexity_le_poly :
    ∀ n : Nat,
      H.boundaryComplexity (family.boundaryAt n) <= c * (n + 1) ^ k

/-- Any polynomially bounded SAT-semantic family refutes the SAT-side lower
bound, regardless of whether the invariant is length-only or instance-sensitive.
-/
theorem not_lengthIndexedSATHolographicBoundaryLowerBound_of_polySATFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (F : PolynomiallyBoundedSATBoundaryFamily D I H M) :
    ¬ LengthIndexedSATHolographicBoundaryLowerBound D I H :=
  not_lengthIndexedSATHolographicBoundaryLowerBound_of_polyBoundedFamily
    D I H M F.family F.k F.c F.complexity_le_poly

/-- A low-action SAT family is automatically polynomially bounded by the
encoder's P-side calibration. -/
theorem not_lengthIndexedSATHolographicBoundaryLowerBound_of_lowActionSATFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (F : LengthIndexedLowActionSATBoundaryFamily D I H M) :
    ¬ LengthIndexedSATHolographicBoundaryLowerBound D I H := by
  rcases H.lowActionBudget_poly with ⟨k, c, hbudget_poly⟩
  exact
    not_lengthIndexedSATHolographicBoundaryLowerBound_of_polyBoundedFamily
      D I H M F.toSATBoundaryFamily k c
      (by
        intro n
        have hcomplexity_le_budget :
            H.boundaryComplexity (F.boundaryAt n) <= H.lowActionBudget n := by
          have hdecoded :=
            H.complexity_le_budget_of_lowAction
              (F.encodingAt n).bulk
              (F.encodingAt n).low_action
          simpa [(F.encodingAt n).decodes_to, F.length_eq n] using hdecoded
        exact Nat.le_trans hcomplexity_le_budget (hbudget_poly n))

/-- Instance-sensitive middle-invariant package.

The `sensitive` field rules out pure length-only pricing.  The guard theorems
below show that this still does not solve the problem unless the invariant also
rules out every polynomially bounded SAT-semantic family by genuine SAT
structure. -/
structure InstanceSensitiveCookLevinMiddleInvariant
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) : Prop where
  sensitive : BoundaryComplexityIsInstanceSensitive I H
  pSide : LengthIndexedPLevelSATObserverTransport D I H
  satSide : LengthIndexedSATHolographicBoundaryLowerBound D I H

/-- Instance sensitivity alone is not enough: any polynomially bounded
SAT-semantic family refutes the package. -/
theorem not_instanceSensitiveCookLevinMiddleInvariant_of_polySATFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (F : PolynomiallyBoundedSATBoundaryFamily D I H M) :
    ¬ InstanceSensitiveCookLevinMiddleInvariant D I H := by
  intro hmiddle
  exact not_lengthIndexedSATHolographicBoundaryLowerBound_of_polySATFamily
    D I H M F hmiddle.satSide

/-- If a complete SAT search machine exists, P-side transport itself produces a
low-action SAT family, hence a polynomially bounded SAT-semantic family.  Thus
an instance-sensitive middle invariant would already imply the absence of such
a machine. -/
theorem not_instanceSensitiveCookLevinMiddleInvariant_of_searchCorrect
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    ¬ InstanceSensitiveCookLevinMiddleInvariant D I H := by
  intro hmiddle
  rcases hmiddle.pSide.transport M hcorrect with ⟨F⟩
  exact not_lengthIndexedSATHolographicBoundaryLowerBound_of_lowActionSATFamily
    D I H M F hmiddle.satSide

/-- Conditional closure from an instance-sensitive middle invariant.  This is
the honest positive socket: proving such an invariant is exactly strong enough
to rule out canonical polynomial-time SAT search. -/
theorem noCanonicalSATDecisionInP_of_instanceSensitiveCookLevinMiddleInvariant
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hmiddle : InstanceSensitiveCookLevinMiddleInvariant D I H) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_lengthIndexedFaithfulHolographicSATLowerBound
    D I H hmiddle.pSide hmiddle.satSide

/-! ## God-Move annihilator interface -/

/-- The God-Move annihilator complexity of a boundary.

At this abstraction level it is the encoder's boundary complexity, but the
interface below records the extra obligations that make this complexity a real
annihilator rather than formula size, length-only growth, or bookkeeping. -/
def GodMoveAnnihilatorComplexity
    {I : NFrameLagrangianPACInvariant}
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (boundary : H.Boundary) : Nat :=
  H.boundaryComplexity boundary

/-- Instance sensitivity rules out every pure length-only factorization. -/
theorem not_boundaryComplexityFactorsThroughLength_of_instanceSensitive
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hsensitive : BoundaryComplexityIsInstanceSensitive I H)
    (scale : Nat -> Nat) :
    ¬ BoundaryComplexityFactorsThroughLength I H scale := by
  intro hfactors
  rcases hsensitive with ⟨b1, b2, hlen, hneq⟩
  apply hneq
  calc
    H.boundaryComplexity b1 = scale (H.boundaryLength b1) :=
      hfactors b1
    _ = scale (H.boundaryLength b2) := by
      rw [hlen]
    _ = H.boundaryComplexity b2 := (hfactors b2).symm

/-- The non-bookkeeping annihilator lower-bound socket: no SAT-semantic
boundary family may remain polynomially bounded.

This is intentionally stated without mentioning "no SAT search machine"; it is
the instance-level lower-bound content the God-Move annihilator would have to
prove from Cook-Levin/N-frame structure. -/
def GodMoveAnnihilatorNoPolynomialSATFamilies
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) : Prop :=
  ∀ M : SearchMachine D.surface.toMachineModel,
    ¬ Nonempty (PolynomiallyBoundedSATBoundaryFamily D I H M)

/-- Ruling out polynomially bounded SAT-semantic families is exactly enough to
obtain the SAT-side holographic lower bound. -/
theorem lengthIndexedSATHolographicBoundaryLowerBound_of_noPolynomialSATFamilies
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hnoPoly : GodMoveAnnihilatorNoPolynomialSATFamilies D I H) :
    LengthIndexedSATHolographicBoundaryLowerBound D I H := by
  intro M F k c
  by_contra hnone
  have hle :
      ∀ n : Nat,
        H.boundaryComplexity (F.boundaryAt n) <= c * (n + 1) ^ k := by
    intro n
    exact Nat.le_of_not_gt (by
      intro hgt
      exact hnone ⟨n, hgt⟩)
  exact hnoPoly M ⟨{
    family := F
    k := k
    c := c
    complexity_le_poly := hle
  }⟩

/-- Conversely, the SAT-side holographic lower bound rules out polynomially
bounded SAT-semantic families. -/
theorem noPolynomialSATFamilies_of_lengthIndexedSATHolographicBoundaryLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hlower : LengthIndexedSATHolographicBoundaryLowerBound D I H) :
    GodMoveAnnihilatorNoPolynomialSATFamilies D I H := by
  intro M hpoly
  rcases hpoly with ⟨F⟩
  exact
    (not_lengthIndexedSATHolographicBoundaryLowerBound_of_polySATFamily
      D I H M F) hlower

/-- The annihilator lower-bound socket is equivalent to the SAT-side
superpolynomial boundary lower bound. -/
theorem lengthIndexedSATHolographicBoundaryLowerBound_iff_noPolynomialSATFamilies
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) :
    LengthIndexedSATHolographicBoundaryLowerBound D I H ↔
      GodMoveAnnihilatorNoPolynomialSATFamilies D I H :=
  ⟨noPolynomialSATFamilies_of_lengthIndexedSATHolographicBoundaryLowerBound
      D I H,
    lengthIndexedSATHolographicBoundaryLowerBound_of_noPolynomialSATFamilies
      D I H⟩

/-- The narrowed God-Move annihilator target.

`sensitive` says the complexity distinguishes same-length instances.
`pSide` is the intended low-action/P observer calibration.
`annihilatesPolynomialSATFamilies` is the hard SAT/Cook-Levin/N-frame theorem:
no SAT-semantic boundary family can stay polynomially bounded.

This is the first interface that is not length-only by construction and does
not allow a merely decorative complexity measure.  It is still a socket, not a
proof of P vs NP. -/
structure GodMoveAnnihilatorInvariant
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I) : Prop where
  sensitive : BoundaryComplexityIsInstanceSensitive I H
  pSide : LengthIndexedPLevelSATObserverTransport D I H
  annihilatesPolynomialSATFamilies :
    GodMoveAnnihilatorNoPolynomialSATFamilies D I H

/-- A God-Move annihilator cannot be length-only. -/
theorem godMoveAnnihilator_not_lengthOnly
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hgod : GodMoveAnnihilatorInvariant D I H)
    (scale : Nat -> Nat) :
    ¬ BoundaryComplexityFactorsThroughLength I H scale :=
  not_boundaryComplexityFactorsThroughLength_of_instanceSensitive
    I H hgod.sensitive scale

/-- A God-Move annihilator supplies the SAT-side lower bound. -/
theorem lengthIndexedSATHolographicBoundaryLowerBound_of_godMoveAnnihilator
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hgod : GodMoveAnnihilatorInvariant D I H) :
    LengthIndexedSATHolographicBoundaryLowerBound D I H :=
  lengthIndexedSATHolographicBoundaryLowerBound_of_noPolynomialSATFamilies
    D I H hgod.annihilatesPolynomialSATFamilies

/-- A God-Move annihilator is an instance-sensitive Cook-Levin middle
invariant. -/
theorem instanceSensitiveMiddleInvariant_of_godMoveAnnihilator
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hgod : GodMoveAnnihilatorInvariant D I H) :
    InstanceSensitiveCookLevinMiddleInvariant D I H where
  sensitive := hgod.sensitive
  pSide := hgod.pSide
  satSide :=
    lengthIndexedSATHolographicBoundaryLowerBound_of_godMoveAnnihilator
      D I H hgod

/-- A polynomially bounded SAT-semantic family refutes the God-Move
annihilator invariant. -/
theorem not_godMoveAnnihilatorInvariant_of_polySATFamily
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (F : PolynomiallyBoundedSATBoundaryFamily D I H M) :
    ¬ GodMoveAnnihilatorInvariant D I H := by
  intro hgod
  exact hgod.annihilatesPolynomialSATFamilies M ⟨F⟩

/-- If a complete SAT search machine exists, P-side transport refutes the
God-Move annihilator invariant.  This is the P-vs-NP-strength guard. -/
theorem not_godMoveAnnihilatorInvariant_of_searchCorrect
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (M : SearchMachine D.surface.toMachineModel)
    (hcorrect : SearchCorrect D.surface.toMachineModel M) :
    ¬ GodMoveAnnihilatorInvariant D I H := by
  intro hgod
  exact not_instanceSensitiveCookLevinMiddleInvariant_of_searchCorrect
    D I H M hcorrect
    (instanceSensitiveMiddleInvariant_of_godMoveAnnihilator D I H hgod)

/-- A God-Move annihilator rules out every complete canonical SAT search
machine. -/
theorem forall_not_searchCorrect_of_godMoveAnnihilator
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hgod : GodMoveAnnihilatorInvariant D I H) :
    ∀ M : SearchMachine D.surface.toMachineModel,
      ¬ SearchCorrect D.surface.toMachineModel M := by
  intro M hcorrect
  exact not_godMoveAnnihilatorInvariant_of_searchCorrect
    D I H M hcorrect hgod

/-- Conditional closure from the God-Move annihilator interface. -/
theorem noCanonicalSATDecisionInP_of_godMoveAnnihilator
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : LengthIndexedFaithfulHolographicEncoder I)
    (hgod : GodMoveAnnihilatorInvariant D I H) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_lengthIndexedFaithfulHolographicSATLowerBound
    D I H hgod.pSide
    (lengthIndexedSATHolographicBoundaryLowerBound_of_godMoveAnnihilator
      D I H hgod)

/-- The P-side observer calibration for the faithful holographic layer:
a complete SAT search machine would produce a faithful low-action decoded SAT
boundary on some instance. -/
structure PLevelSATObserverFaithfulBoundaryTransport
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I) : Prop where
  transport :
    ∀ M : SearchMachine D.surface.toMachineModel,
      SearchCorrect D.surface.toMachineModel M ->
        ∃ phi : CNF,
          Nonempty (FaithfulLowActionSATBoundary D I H M phi)

/-- Faithful SAT lower bound forbids low-action faithful SAT boundaries. -/
theorem noFaithfulLowActionSATBoundary_of_faithfulSATLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (hlower : FaithfulSATHolographicBoundaryLowerBound D I H)
    (M : SearchMachine D.surface.toMachineModel)
    (phi : CNF) :
    ¬ Nonempty (FaithfulLowActionSATBoundary D I H M phi) := by
  intro hboundary
  rcases hboundary with ⟨B⟩
  exact noLowActionEncoding_of_highBoundaryComplexity
    I H B.boundary
    (hlower M phi B.boundary B.semantics)
    ⟨B.encoding⟩

/-- If P-level SAT observers always produce faithful low-action SAT boundaries,
and faithful SAT boundaries are above the low-action complexity budget, then no
complete canonical SAT search machine exists. -/
theorem forall_not_searchCorrect_of_faithfulHolographicSATLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (htransport : PLevelSATObserverFaithfulBoundaryTransport D I H)
    (hlower : FaithfulSATHolographicBoundaryLowerBound D I H) :
    ∀ M : SearchMachine D.surface.toMachineModel,
      ¬ SearchCorrect D.surface.toMachineModel M := by
  intro M hcorrect
  rcases htransport.transport M hcorrect with ⟨phi, hboundary⟩
  exact noFaithfulLowActionSATBoundary_of_faithfulSATLowerBound
    D I H hlower M phi hboundary

/-- Faithful holographic SAT lower bound gives canonical deep SAT search, once
the P-side transport/calibration is supplied. -/
theorem canonicalDeepSATSearch_of_faithfulHolographicSATLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (htransport : PLevelSATObserverFaithfulBoundaryTransport D I H)
    (hlower : FaithfulSATHolographicBoundaryLowerBound D I H) :
    CanonicalDeepSATSearch D.surface :=
  (canonicalDeepSATSearch_iff_forall_not_searchCorrect D.surface).mpr
    (forall_not_searchCorrect_of_faithfulHolographicSATLowerBound
      D I H htransport hlower)

/-- Conditional P-vs-NP-facing closure for the faithful holographic route.  The
unproved content is exactly the faithful transport plus the SAT boundary lower
bound above. -/
theorem noCanonicalSATDecisionInP_of_faithfulHolographicSATLowerBound
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (H : FaithfulHolographicEncoder I)
    (htransport : PLevelSATObserverFaithfulBoundaryTransport D I H)
    (hlower : FaithfulSATHolographicBoundaryLowerBound D I H) :
    ¬ CanonicalSATDecisionInP D.surface :=
  canonicalNoDecider_of_deepSATSearch D.surface
    (canonicalDeepSATSearch_of_faithfulHolographicSATLowerBound
      D I H htransport hlower)

/-- The algorithmic step from efficient SYM+ normal forms to fast ACC0
circuit-SAT.  This is the Williams/Yao-Beigel-Tarui-style ingredient; it is
kept separate from the N-frame extraction theorem. -/
structure SYMPlusNormalFormsYieldFastACC0SAT
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S) : Prop where
  fastSAT_of_symPlusNormalForms :
    (∀ F : ACC0LikeCircuitFamily,
      ACC0FamilyBoundedBySurface S F ->
        Nonempty (ACC0FamilyHasEfficientSYMPlusNormalForms F)) ->
          P.FastACC0CircuitSAT

/-- If the N-frame Lagrangian extracts efficient SYM+ normal forms, and those
normal forms feed the known ACC0-SAT algorithmic method, then N-frame supplies
the fast-ACC0-SAT component. -/
theorem nFrameSuppliesConcreteACC0FastCircuitSAT_of_symPlusNormalForms
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hnf : NFrameLagrangianYieldsSYMPlusNormalForms D I S)
    (halg : SYMPlusNormalFormsYieldFastACC0SAT S P) :
    NFrameSuppliesConcreteACC0FastCircuitSAT D I S P := by
  simpa [NFrameSuppliesConcreteACC0FastCircuitSAT,
    NFrameSuppliesFastCircuitSAT,
    concreteACC0WilliamsTarget,
    ACC0WilliamsTarget.toGodelWilliamsStep]
    using halg.fastSAT_of_symPlusNormalForms hnf

/-- The positive restricted route: N-frame-derived SYM+ normal forms plus
meta-simulation yield the Williams-scale ACC0 lower bound. -/
theorem concreteACC0_nexp_not_subset_of_nFrameSYMPlusNormalForms
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (P : ConcreteACC0WilliamsPackage S)
    (hnf : NFrameLagrangianYieldsSYMPlusNormalForms D I S)
    (halg : SYMPlusNormalFormsYieldFastACC0SAT S P)
    (hmeta : NFrameSuppliesConcreteACC0MetaSimulation D I S P) :
    PallLean.Paper93.DeepMath.PathB.NEXPNotSubsetCircuitClass
      (concreteACC0WilliamsTarget S P).toCircuitClass :=
  concreteACC0_nexp_not_subset_of_nFrame_fastSAT_meta D I S P
    (nFrameSuppliesConcreteACC0FastCircuitSAT_of_symPlusNormalForms
      D I S P hnf halg)
    hmeta

/-- Rank-detector version of the SYM+ extraction route.  This is intentionally
narrow: it says the SYM+ normal forms are being obtained through the same
SPDP/log-det easiness detector refuted by the symmetric probes. -/
def NFrameSYMPlusNormalFormsViaSPDPDetector
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (probe : SYMPlusEasyMaximalSPDPProbe) : Prop :=
  NFrameLagrangianYieldsSYMPlusNormalForms D I S ∧
    SPDPProbeReadsSYMPlusEasyAsNonmaximal probe

/-- A SYM+-easy maximal-rank probe rules out the rank-detector version of the
SYM+ normal-form extraction route.  It does not rule out a genuinely algorithmic
N-frame extraction theorem. -/
theorem not_nFrameSYMPlusNormalFormsViaSPDPDetector
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (S : ConcreteACC0Surface)
    (probe : SYMPlusEasyMaximalSPDPProbe) :
    ¬ NFrameSYMPlusNormalFormsViaSPDPDetector D I S probe := by
  intro h
  exact not_spdpProbeReadsSYMPlusEasyAsNonmaximal probe h.2

/-- The Gödel/Williams transport closes the canonical SAT decider only by using
a hierarchy contradiction.  This is the intended non-natural shape: no
truth-table largeness/rank property is invoked. -/
theorem noCanonicalSATDecisionInP_of_nFrameGodelWilliamsProgram
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (h : NFrameGodelWilliamsProgram D I T W) :
    ¬ CanonicalSATDecisionInP D.surface := by
  intro hdec
  exact false_of_williamsGodelNonNaturalStep T W
    h.nframe_supplies_fastCircuitSAT
    (h.decider_to_smallRepresentation hdec)
    h.nframe_supplies_metaSimulation

/-- The same Gödel/Williams transport feeds the existing hard
metacomplexity socket. -/
theorem hardMetacomplexitySocket_of_nFrameGodelWilliamsProgram
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (h : NFrameGodelWilliamsProgram D I T W) :
    HardMetacomplexitySocket D :=
  hardMetacomplexitySocket_of_noCanonicalSATDecisionInP D
    (noCanonicalSATDecisionInP_of_nFrameGodelWilliamsProgram D I T W h)

/-- Conditional route closure from a Williams/Gödel tower transport. -/
theorem ktRoute_finalClosure_of_nFrameGodelWilliamsProgram
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (h : NFrameGodelWilliamsProgram D I T W) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardMetacomplexitySocket_of_nFrameGodelWilliamsProgram D I T W h)

/-- The tower program still uses a genuine non-vacuous N-frame Lagrangian:
there is always a low-action identity/reference bulk object. -/
theorem exists_lowActionBulk_of_nFrameGodelWilliamsProgram
    (D : DescribedCanonicalSurface)
    (I : NFrameLagrangianPACInvariant)
    (T : ResourceBoundedGodelWilliamsTower)
    (W : WilliamsGodelNonNaturalStep T)
    (_h : NFrameGodelWilliamsProgram D I T W) :
    ∃ bulk : NFramePACBulk I.dim, I.action bulk <= I.actionBound :=
  exists_lowActionBulk_of_nFrameLagrangianPACInvariant I

/-! The remaining positive theorem is still the construction of
`NFrameGodelWilliamsProgram`: prove that the N-frame/Gödel tower supplies
`fastCircuitSAT` and `metaSimulation`, and that any canonical SAT decider yields
the `smallRepresentation` needed by Williams' hierarchy contradiction.

At the restricted ACC0 test surface, the new concrete subtarget is
`NFrameTargetedStrictSYMPlusBulkCoding`: low-action N-frame bulk must encode the
specific size/term-count pairs of the strict SYM+ certificates supplied by the
surface normalization theorem.

The current file proves that subtarget for the present model, but only because
the log-det action ignores the bookkeeping fields.  A load-bearing version must
replace this with an action/encoding coupling theorem where reconstruction data
is constrained by the actual N-frame bulk geometry.

The faithful holographic layer names that replacement:
`FaithfulSATHolographicBoundaryLowerBound`, plus the P-side
`PLevelSATObserverFaithfulBoundaryTransport`.  Together they give canonical
SAT separation in this formal model, but the SAT lower bound is the missing
mathematical theorem.

The Cook-Levin projection below also shows that a single fixed low-action budget
is too coarse: once boundary complexity prices formula size, arbitrarily large
satisfiable CNFs defeat any global budget.  A faithful positive version must be
length-indexed, with a polynomial P-side budget and a superpolynomial SAT-side
boundary lower bound.

The concrete formula-size Cook-Levin encoder discharges the P-side transport
but has only linear boundary complexity, so its SAT lower-bound socket is
refuted.  The remaining positive target is therefore a stronger Cook-Levin
complexity measure than formula size.

The semantic-orbit encoder above tests the opposite extreme.  Its
`(n+1)^(n+1)` complexity scale proves the SAT-side lower-bound socket, but then
no low-action SAT boundary family can exist.  Thus formula-size pricing is too
weak for SAT, while semantic-orbit pricing is too strong for the P-side
transport.  A successful invariant would have to occupy the currently missing
middle: strong enough to force SAT superpolynomial complexity, but still
decoded from genuine low-action polynomial observers.

The length-only no-go makes that sharper.  If boundary complexity factors only
through a scalar function of boundary length, then polynomial scales cannot
prove the SAT lower bound, and superpolynomial scales refute P-side transport
in the presence of any complete SAT search machine.  Therefore a surviving
middle invariant cannot merely be a better growth function of `n`; it must be
instance-sensitive and tied to non-length Cook-Levin/N-frame structure.

The instance-sensitive pressure theorem then removes a second possible escape:
instance sensitivity alone is not enough.  Any polynomially bounded
SAT-semantic family refutes the universal SAT lower-bound socket, and any
P-side transport plus a complete SAT search machine supplies such a family.
So the next positive target must prove, from actual SAT/Cook-Levin/N-frame
structure, that no polynomially bounded SAT-semantic family exists without
assuming the absence of SAT search machines.

The God-Move annihilator interface names exactly that target.  It packages an
instance-sensitive boundary complexity, P-side observer transport, and the hard
annihilator theorem that no polynomially bounded SAT-semantic family exists.
The file proves this interface is not length-only, is equivalent on the
SAT-side to the superpolynomial boundary lower bound, and conditionally closes
the canonical SAT-decider socket.  It also proves that any polynomially bounded
SAT family, or any complete SAT search machine together with P-side transport,
refutes the annihilator. -/

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
#print axioms false_of_williamsGodelNonNaturalStep
#print axioms williamsGodelCollapseIsNonBlackBox
#print axioms nFrameGodelWilliamsProgram_of_components
#print axioms noCanonicalSATDecisionInP_of_nFrameGodelWilliamsComponents
#print axioms not_all_nFrameGodelWilliamsComponents_of_canonicalSATDecisionInP
#print axioms ktRoute_finalClosure_of_nFrameGodelWilliamsComponents
#print axioms acc0_nexp_not_subset_of_fastSAT_and_metaSimulation
#print axioms acc0_nexp_not_subset_of_nFrameACC0WilliamsRestrictedProgram
#print axioms not_nFrameACC0WilliamsRestrictedProgram_of_nexp_subset_acc0
#print axioms nFrameACC0WilliamsRestrictedProgram_of_concreteACC0Ingredients
#print axioms concreteACC0_nexp_not_subset_of_nFrame_fastSAT_meta
#print axioms not_both_nFrameConcreteACC0Ingredients_of_nexp_subset
#print axioms not_spdpProbeReadsSYMPlusEasyAsNonmaximal
#print axioms not_nFrameConcreteACC0FastSATViaSPDPDetector
#print axioms loose_nFrameLagrangianYieldsSYMPlusNormalForms
#print axioms nFrameLagrangianYieldsStrictSYMPlusNormalForms_iff_surfaceNormalization
#print axioms nFrameLagrangianYieldsStrictSYMPlusNormalForms_of_surfaceNormalization
#print axioms ACC0FamilyHasNFrameCertifiedEfficientStrictSYMPlusNormalForms.toStrict
#print axioms nFrameLagrangianYieldsStrictSYMPlusNormalForms_of_certifiedExtraction
#print axioms lowActionBulkEncoding_of_capacity
#print axioms lowActionBulkCodingCapacity_of_pointwiseEncoding
#print axioms lowActionBulkCodingCapacity_of_bookkeepingFreeLogDetAction
#print axioms nFrameStrictSYMPlusBulkEncoder_of_lowActionBulkCodingCapacity
#print axioms not_lowActionBulkCodingCapacity_of_identityOnly
#print axioms not_lowActionBulkEncoding_of_identityOnly_nonzero
#print axioms not_nFrameStrictSYMPlusBulkEncoder_of_identityOnly_nonzeroCertificate
#print axioms nFrameTargetedStrictSYMPlusBulkCoding_of_lowActionBulkCodingCapacity
#print axioms nFrameTargetedStrictSYMPlusBulkCoding_of_bookkeepingFreeLogDetAction
#print axioms not_nFrameTargetedStrictSYMPlusBulkCoding_of_identityOnly_nonzero
#print axioms nFrameCertifiedStrictSYMPlusNormalForm_of_bulkEncoder
#print axioms nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_bulkEncoder
#print axioms nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_targetedCoding
#print axioms nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_bookkeepingFree
#print axioms nFrameSuppliesConcreteACC0FastCircuitSAT_of_strictSYMPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_nFrameStrictSYMPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_nFrameCertifiedStrictSYMPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_surfaceNormalization_bulkEncoder
#print axioms concreteACC0_nexp_not_subset_of_surfaceNormalization_targetedCoding
#print axioms concreteACC0_nexp_not_subset_of_surfaceNormalization_bookkeepingFree
#print axioms noLowActionEncoding_of_highBoundaryComplexity
#print axioms highBoundaryComplexity_forces_not_lowAction
#print axioms not_faithfulSATHolographicBoundaryLowerBound_of_lowComplexitySATBoundary
#print axioms not_trivialFaithfulSATHolographicBoundaryLowerBound_of_semantics
#print axioms not_universalFaithfulSATHolographicBoundaryLowerBound_of_trivialSemantics
#print axioms emptySatisfiableCNF_size
#print axioms emptySatisfiableCNF_satisfiable
#print axioms exists_satisfiableCNF_size_gt
#print axioms noCookLevinLowActionBoundary_of_formula_size_gt_budget
#print axioms forall_not_searchCorrect_of_fixedBudgetCookLevinTransport
#print axioms noCanonicalSATDecisionInP_of_fixedBudgetCookLevinTransport
#print axioms noLengthIndexedLowActionEncoding_of_complexity_gt_budget
#print axioms LengthIndexedLowActionSATBoundaryFamily.toSATBoundaryFamily
#print axioms not_lengthIndexedSATHolographicBoundaryLowerBound_of_polyBoundedFamily
#print axioms not_lengthIndexedSATHolographicBoundaryLowerBound_of_zeroComplexityFamily
#print axioms noLengthIndexedLowActionSATBoundaryFamily_of_lowerBound
#print axioms forall_not_searchCorrect_of_lengthIndexedFaithfulHolographicSATLowerBound
#print axioms canonicalDeepSATSearch_of_lengthIndexedFaithfulHolographicSATLowerBound
#print axioms noCanonicalSATDecisionInP_of_lengthIndexedFaithfulHolographicSATLowerBound
#print axioms cookLevinFormulaSize_complexity_eq_length
#print axioms cookLevinFormulaSizeLowActionFamily_of_searchCorrect
#print axioms cookLevinFormulaSize_pLevelTransport
#print axioms not_lengthIndexedSATHolographicBoundaryLowerBound_cookLevinFormulaSize
#print axioms not_lengthIndexedSATHolographicBoundaryLowerBound_cookLevinFormulaSize_of_searchCorrect
#print axioms cookLevinSemanticOrbitComplexity_beats_polynomial
#print axioms lengthIndexedSATHolographicBoundaryLowerBound_of_semanticOrbitPricing
#print axioms noLengthIndexedLowActionSATBoundaryFamily_of_semanticOrbitPricing
#print axioms not_lengthIndexedPLevelSATObserverTransport_of_semanticOrbitPricing
#print axioms cookLevinSemanticOrbit_pricing
#print axioms lengthIndexedSATHolographicBoundaryLowerBound_cookLevinSemanticOrbit
#print axioms noLengthIndexedLowActionSATBoundaryFamily_cookLevinSemanticOrbit
#print axioms not_cookLevinSemanticOrbit_pLevelTransport_of_searchCorrect
#print axioms noCanonicalSATDecisionInP_of_cookLevinSemanticOrbit_transport
#print axioms not_lengthIndexedSATHolographicBoundaryLowerBound_of_lengthOnlyPolyScale
#print axioms lengthIndexedSATHolographicBoundaryLowerBound_of_lengthOnlySuperpolyScale
#print axioms noLengthIndexedLowActionSATBoundaryFamily_of_lengthOnlySuperpolyScale
#print axioms not_lengthIndexedPLevelSATObserverTransport_of_lengthOnlySuperpolyScale
#print axioms not_lengthOnlyCookLevinMiddleInvariant_of_polyScale
#print axioms not_lengthOnlyCookLevinMiddleInvariant_of_superpolyScale_searchCorrect
#print axioms not_lengthIndexedSATHolographicBoundaryLowerBound_of_polySATFamily
#print axioms not_lengthIndexedSATHolographicBoundaryLowerBound_of_lowActionSATFamily
#print axioms not_instanceSensitiveCookLevinMiddleInvariant_of_polySATFamily
#print axioms not_instanceSensitiveCookLevinMiddleInvariant_of_searchCorrect
#print axioms noCanonicalSATDecisionInP_of_instanceSensitiveCookLevinMiddleInvariant
#print axioms not_boundaryComplexityFactorsThroughLength_of_instanceSensitive
#print axioms lengthIndexedSATHolographicBoundaryLowerBound_of_noPolynomialSATFamilies
#print axioms noPolynomialSATFamilies_of_lengthIndexedSATHolographicBoundaryLowerBound
#print axioms lengthIndexedSATHolographicBoundaryLowerBound_iff_noPolynomialSATFamilies
#print axioms godMoveAnnihilator_not_lengthOnly
#print axioms lengthIndexedSATHolographicBoundaryLowerBound_of_godMoveAnnihilator
#print axioms instanceSensitiveMiddleInvariant_of_godMoveAnnihilator
#print axioms not_godMoveAnnihilatorInvariant_of_polySATFamily
#print axioms not_godMoveAnnihilatorInvariant_of_searchCorrect
#print axioms forall_not_searchCorrect_of_godMoveAnnihilator
#print axioms noCanonicalSATDecisionInP_of_godMoveAnnihilator
#print axioms noFaithfulLowActionSATBoundary_of_faithfulSATLowerBound
#print axioms forall_not_searchCorrect_of_faithfulHolographicSATLowerBound
#print axioms canonicalDeepSATSearch_of_faithfulHolographicSATLowerBound
#print axioms noCanonicalSATDecisionInP_of_faithfulHolographicSATLowerBound
#print axioms nFrameSuppliesConcreteACC0FastCircuitSAT_of_symPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_nFrameSYMPlusNormalForms
#print axioms not_nFrameSYMPlusNormalFormsViaSPDPDetector
#print axioms noCanonicalSATDecisionInP_of_nFrameGodelWilliamsProgram
#print axioms hardMetacomplexitySocket_of_nFrameGodelWilliamsProgram
#print axioms ktRoute_finalClosure_of_nFrameGodelWilliamsProgram
#print axioms exists_lowActionBulk_of_nFrameGodelWilliamsProgram

end SATDepthMachine
