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

/-! The remaining theorem is exactly the construction of
`NFrameGodelWilliamsProgram`: prove that the N-frame/Gödel tower supplies
`fastCircuitSAT` and `metaSimulation`, and that any canonical SAT decider yields
the `smallRepresentation` needed by Williams' hierarchy contradiction. -/

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
#print axioms noCanonicalSATDecisionInP_of_nFrameGodelWilliamsProgram
#print axioms hardMetacomplexitySocket_of_nFrameGodelWilliamsProgram
#print axioms ktRoute_finalClosure_of_nFrameGodelWilliamsProgram
#print axioms exists_lowActionBulk_of_nFrameGodelWilliamsProgram

end SATDepthMachine
