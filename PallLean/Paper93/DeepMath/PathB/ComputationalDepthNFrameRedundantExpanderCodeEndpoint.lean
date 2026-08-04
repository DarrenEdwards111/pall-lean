import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSolverIndependentAgreementNoGo

/-!
# Redundant Ramanujan encoding: codebook size versus cell-correlated list decoding

A natural response to the full-rate continuation-cube obstruction is to encode
each `m`-bit semantic label into a longer `N`-bit expander codeword.  Redundancy
creates local checks, but by itself it does not reduce semantic ambiguity: every
injective code still has exactly `2^m` valid codewords.

The useful object is a cell-correlated received-word/proximity predicate.  It must
contain the encoded true label paired with its solver-induced amplituhedron cell
and contain only polynomially many semantic messages.  This file proves that such a
bounded predicate constructs the prior cell list decoder, while a fixed validity
test for the whole codebook remains exponentially large.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint

/-! ## Injective redundant continuation codes -/

/-- An abstract redundant Boolean encoding.  A concrete Ramanujan/Tanner code is
an instance with additional local-check and distance structure. -/
structure RedundantContinuationCode (m N : Nat) where
  encode : Assignment m -> Assignment N
  injective : Function.Injective encode

namespace RedundantContinuationCode

/-- The finite set of valid encoded continuation labels. -/
noncomputable def codewords {m N : Nat}
    (C : RedundantContinuationCode m N) : Finset (Assignment N) := by
  classical
  exact (Finset.univ : Finset (Assignment m)).image C.encode

/-- Redundancy preserves all semantic messages: every injective codebook has
exactly `2^m` words. -/
theorem codewords_card {m N : Nat}
    (C : RedundantContinuationCode m N) :
    C.codewords.card = 2 ^ m := by
  classical
  rw [codewords, Finset.card_image_of_injective _ C.injective]
  simp

/-- The ambient encoded carrier has `2^N` words; only injectivity, not redundancy,
controls the valid codebook cardinality. -/
theorem ambient_card (N : Nat) :
    Fintype.card (Assignment N) = 2 ^ N := by
  simp

end RedundantContinuationCode

/-! ## Solver-independent code validity remains exponential -/

/-- A fixed codeword predicate accepts every legitimate encoded continuation. -/
def SoundCodeValidity {m N : Nat}
    (C : RedundantContinuationCode m N)
    (valid : Assignment N -> Prop) : Prop :=
  forall a : Assignment m, valid (C.encode a)

/-- Semantic messages accepted through a fixed encoded-word validity test. -/
noncomputable def validEncodedMessages
    {m N : Nat} (C : RedundantContinuationCode m N)
    (valid : Assignment N -> Prop) : Finset (Assignment m) := by
  classical
  exact (Finset.univ : Finset (Assignment m)).filter
    (fun a => valid (C.encode a))

/-- Sound fixed code validity accepts every semantic message. -/
theorem validEncodedMessages_eq_univ
    {m N : Nat} (C : RedundantContinuationCode m N)
    {valid : Assignment N -> Prop}
    (hsound : SoundCodeValidity C valid) :
    validEncodedMessages C valid = Finset.univ := by
  classical
  unfold validEncodedMessages
  apply Finset.filter_eq_self.mpr
  intro a _
  exact hsound a

/-- Therefore redundancy alone leaves the full `2^m` semantic candidate set. -/
theorem validEncodedMessages_card
    {m N : Nat} (C : RedundantContinuationCode m N)
    {valid : Assignment N -> Prop}
    (hsound : SoundCodeValidity C valid) :
    (validEncodedMessages C valid).card = 2 ^ m := by
  rw [validEncodedMessages_eq_univ C hsound]
  simp

/-- No fixed sound code-validity predicate yields a list below the semantic cube
size. -/
theorem no_small_list_from_codeValidity
    {m N r : Nat} (C : RedundantContinuationCode m N)
    {valid : Assignment N -> Prop}
    (hsound : SoundCodeValidity C valid)
    (hsmall : r < 2 ^ m) :
    ¬ (validEncodedMessages C valid).card <= r := by
  rw [validEncodedMessages_card C hsound]
  omega

/-! ## Cell-correlated code proximity is the genuine decoding object -/

/-- The encoded true label satisfies the received-word/proximity predicate of its
actual solver-induced cell. -/
def CodeCellSound
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (close : Cell -> Assignment N -> Prop) : Prop :=
  forall a : Assignment m, close (cellOf a) (C.encode a)

/-- Semantic messages whose codewords are close/compatible with one cell. -/
noncomputable def codeCellCandidates
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (close : Cell -> Assignment N -> Prop) (c : Cell) :
    Finset (Assignment m) := by
  classical
  exact (Finset.univ : Finset (Assignment m)).filter
    (fun a => close c (C.encode a))

/-- A sound polynomial list-decoding bound around every cell constructs list
recovery for the original semantic continuations. -/
noncomputable def listRecoveryOfCodeCellAgreement
    {m N r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (close : Cell -> Assignment N -> Prop)
    (hsound : CodeCellSound C cellOf close)
    (hbound : forall c : Cell,
      (codeCellCandidates C close c).card <= r) :
    CellListRecovery cellOf r where
  candidates := codeCellCandidates C close
  covers a := by
    classical
    unfold codeCellCandidates
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hsound a⟩
  listSize := hbound

/-- Exact endpoint: a fixed sound codebook predicate is exponential, whereas a
cell-correlated bounded-distance predicate immediately supplies list recovery. -/
theorem redundantCode_requires_cellCorrelation
    {m N r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    {valid : Assignment N -> Prop}
    (hvalid : SoundCodeValidity C valid)
    (hsmall : r < 2 ^ m) :
    (¬ (validEncodedMessages C valid).card <= r) ∧
      (forall (close : Cell -> Assignment N -> Prop),
        CodeCellSound C cellOf close ->
        (forall c, (codeCellCandidates C close c).card <= r) ->
        Nonempty (CellListRecovery cellOf r)) := by
  constructor
  · exact no_small_list_from_codeValidity C hvalid hsmall
  · intro close hsound hbound
    exact ⟨listRecoveryOfCodeCellAgreement C cellOf close hsound hbound⟩

end PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint.RedundantContinuationCode.codewords_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint.validEncodedMessages_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint.no_small_list_from_codeValidity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint.redundantCode_requires_cellCorrelation
