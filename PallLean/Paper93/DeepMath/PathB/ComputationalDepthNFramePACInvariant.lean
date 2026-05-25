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
surface normalization theorem. -/

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
#print axioms nFrameStrictSYMPlusBulkEncoder_of_lowActionBulkCodingCapacity
#print axioms not_lowActionBulkCodingCapacity_of_identityOnly
#print axioms not_lowActionBulkEncoding_of_identityOnly_nonzero
#print axioms not_nFrameStrictSYMPlusBulkEncoder_of_identityOnly_nonzeroCertificate
#print axioms nFrameTargetedStrictSYMPlusBulkCoding_of_lowActionBulkCodingCapacity
#print axioms not_nFrameTargetedStrictSYMPlusBulkCoding_of_identityOnly_nonzero
#print axioms nFrameCertifiedStrictSYMPlusNormalForm_of_bulkEncoder
#print axioms nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_bulkEncoder
#print axioms nFrameLagrangianExtractsStrictSYMPlusNormalForms_of_surfaceNormalization_and_targetedCoding
#print axioms nFrameSuppliesConcreteACC0FastCircuitSAT_of_strictSYMPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_nFrameStrictSYMPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_nFrameCertifiedStrictSYMPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_surfaceNormalization_bulkEncoder
#print axioms concreteACC0_nexp_not_subset_of_surfaceNormalization_targetedCoding
#print axioms nFrameSuppliesConcreteACC0FastCircuitSAT_of_symPlusNormalForms
#print axioms concreteACC0_nexp_not_subset_of_nFrameSYMPlusNormalForms
#print axioms not_nFrameSYMPlusNormalFormsViaSPDPDetector
#print axioms noCanonicalSATDecisionInP_of_nFrameGodelWilliamsProgram
#print axioms hardMetacomplexitySocket_of_nFrameGodelWilliamsProgram
#print axioms ktRoute_finalClosure_of_nFrameGodelWilliamsProgram
#print axioms exists_lowActionBulk_of_nFrameGodelWilliamsProgram

end SATDepthMachine
