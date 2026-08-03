import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameExpanderAgreementGap

/-!
# Solver-independent expander agreement is vacuous on the full continuation cube

The independent SAT continuation-query family realizes every Boolean label.  This
creates a sharp obstruction for a fixed Ramanujan/N-frame validity predicate:
if it is sound for every legitimate continuation batch, surjectivity forces it to
accept every one of the `2^m` labels.

Thus a solver-independent notion of a "valid N-frame continuation" cannot produce
polynomial list recovery.  A useful agreement test must be correlated with the
solver-induced amplituhedron cell (or first encode the semantic labels into a
genuinely redundant code).  The final section formalizes that cell-dependent
agreement is exactly what constructs a list decoder.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSolverIndependentAgreementNoGo

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint

/-! ## Every semantic continuation label is realizable -/

/-- A fixed predicate on semantic continuation labels. -/
abbrev ContinuationValidity (m : Nat) := Assignment m -> Prop

/-- The fixed predicate accepts every label produced by the independent SAT
continuation-query family. -/
def SoundOnContinuationFamily {m : Nat}
    (valid : ContinuationValidity m) : Prop :=
  forall batch : (independentSATQueryFamily m).Instance,
    valid ((independentSATQueryFamily m).label batch)

/-- Surjectivity of the continuation family makes any sound fixed predicate
universal. -/
theorem valid_of_soundOnContinuationFamily
    {m : Nat} {valid : ContinuationValidity m}
    (hsound : SoundOnContinuationFamily valid) :
    forall a : Assignment m, valid a := by
  intro a
  obtain ⟨batch, hbatch⟩ :=
    (independentSATQueryFamily m).label_surjective a
  rw [← hbatch]
  exact hsound batch

/-- The finite set accepted by a fixed validity predicate. -/
noncomputable def validLabels {m : Nat}
    (valid : ContinuationValidity m) : Finset (Assignment m) := by
  classical
  exact (Finset.univ : Finset (Assignment m)).filter valid

/-- A sound fixed predicate accepts the entire continuation cube. -/
theorem validLabels_eq_univ_of_sound
    {m : Nat} {valid : ContinuationValidity m}
    (hsound : SoundOnContinuationFamily valid) :
    validLabels valid = Finset.univ := by
  classical
  unfold validLabels
  apply Finset.filter_eq_self.mpr
  intro a _
  exact valid_of_soundOnContinuationFamily hsound a

/-- Consequently its candidate set has exact exponential size. -/
theorem validLabels_card_of_sound
    {m : Nat} {valid : ContinuationValidity m}
    (hsound : SoundOnContinuationFamily valid) :
    (validLabels valid).card = 2 ^ m := by
  rw [validLabels_eq_univ_of_sound hsound]
  simp

/-- No solver-independent sound validity predicate can have a candidate bound
strictly below the full cube size. -/
theorem no_small_solverIndependent_validity_list
    {m r : Nat} {valid : ContinuationValidity m}
    (hsound : SoundOnContinuationFamily valid)
    (hsmall : r < 2 ^ m) :
    ¬ (validLabels valid).card <= r := by
  rw [validLabels_card_of_sound hsound]
  omega

/-! ## A fixed predicate cannot become useful merely by attaching cell names -/

/-- A solver-independent agreement list repeats the same validity set at every
amplituhedron cell. -/
noncomputable def solverIndependentCandidates
    {m : Nat} {Cell : Type}
    (valid : ContinuationValidity m) (_c : Cell) :
    Finset (Assignment m) :=
  validLabels valid

/-- With at least one cell, no sound fixed predicate yields a subexponential
uniform cell-list bound. -/
theorem no_solverIndependent_cellAgreement
    {m r : Nat} {Cell : Type} [Nonempty Cell]
    {valid : ContinuationValidity m}
    (hsound : SoundOnContinuationFamily valid)
    (hsmall : r < 2 ^ m) :
    ¬ (forall c : Cell,
      (solverIndependentCandidates valid c).card <= r) := by
  intro hbound
  let c : Cell := Classical.choice (inferInstance : Nonempty Cell)
  have hc := hbound c
  change (validLabels valid).card <= r at hc
  exact no_small_solverIndependent_validity_list hsound hsmall hc

/-! ## Cell-correlated agreement is the genuine missing object -/

/-- A cell-dependent agreement predicate contains the true label paired with its
actual solver-induced cell. -/
def CellAgreementSound
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (accept : Cell -> Assignment m -> Prop) : Prop :=
  forall a : Assignment m, accept (cellOf a) a

/-- The cell-correlated candidate set. -/
noncomputable def cellAgreementCandidates
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    (accept : Cell -> Assignment m -> Prop) (c : Cell) :
    Finset (Assignment m) := by
  classical
  exact (Finset.univ : Finset (Assignment m)).filter (accept c)

/-- A polynomial cell-correlated agreement bound is precisely enough to build a
list decoder. -/
noncomputable def listRecoveryOfCellAgreement
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (accept : Cell -> Assignment m -> Prop)
    (hsound : CellAgreementSound cellOf accept)
    (hbound : forall c : Cell,
      (cellAgreementCandidates accept c).card <= r) :
    CellListRecovery cellOf r where
  candidates := cellAgreementCandidates accept
  covers a := by
    classical
    unfold cellAgreementCandidates
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hsound a⟩
  listSize := hbound

/-- Endpoint: fixed sound validity gives the full exponential list, whereas the
cell-correlated bounded predicate immediately supplies higher-order list
recovery. -/
theorem solverIndependent_vs_cellCorrelated_endpoint
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    {valid : ContinuationValidity m}
    (hsound : SoundOnContinuationFamily valid)
    (hsmall : r < 2 ^ m) :
    (¬ forall c : Cell,
        (solverIndependentCandidates valid c).card <= r) ∧
      (forall (accept : Cell -> Assignment m -> Prop),
        CellAgreementSound cellOf accept ->
        (forall c, (cellAgreementCandidates accept c).card <= r) ->
        Nonempty (CellListRecovery cellOf r)) := by
  constructor
  · let a0 : Assignment m := fun _ => false
    letI : Nonempty Cell := ⟨cellOf a0⟩
    exact no_solverIndependent_cellAgreement hsound hsmall
  · intro accept haccept hbound
    exact ⟨listRecoveryOfCellAgreement cellOf accept haccept hbound⟩

end PallLean.Paper93.DeepMath.PathB.NFrameSolverIndependentAgreementNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverIndependentAgreementNoGo.valid_of_soundOnContinuationFamily
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverIndependentAgreementNoGo.validLabels_card_of_sound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverIndependentAgreementNoGo.no_solverIndependent_cellAgreement
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverIndependentAgreementNoGo.solverIndependent_vs_cellCorrelated_endpoint
