import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRedundantExpanderCodeEndpoint

/-!
# Received-word list-decoding bridge

The redundant-code endpoint left one precise mechanism: each solver-induced
amplituhedron cell must determine a received word close to the encoded true
continuation label.  A standard expander-code list-decoding theorem can then bound
the number of semantic codewords in that Hamming ball.

This file separates and composes those obligations:

1. `HammingListDecodable` is a code-only combinatorial theorem.
2. `CellReceivedWordProjection` is the solver/cell semantic correspondence.
3. Together they construct the polynomial cell list decoder.

Radius zero is calibrated unconditionally: injectivity gives unique decoding,
but a zero-radius cell projection already forces the cell map to be injective.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint

/-! ## Hamming balls around encoded continuations -/

/-- Boolean Hamming distance. -/
def hammingDistance {N : Nat} (x y : Assignment N) : Nat :=
  ((Finset.univ : Finset (Fin N)).filter (fun i => x i ≠ y i)).card

/-- Semantic messages whose codewords lie in a radius-`R` ball. -/
noncomputable def messageBall
    {m N : Nat} (C : RedundantContinuationCode m N)
    (received : Assignment N) (R : Nat) : Finset (Assignment m) := by
  classical
  exact (Finset.univ : Finset (Assignment m)).filter
    (fun a => hammingDistance received (C.encode a) <= R)

/-- A code-only list-decoding guarantee, uniform over every received word. -/
def HammingListDecodable
    {m N : Nat} (C : RedundantContinuationCode m N)
    (R L : Nat) : Prop :=
  forall received : Assignment N, (messageBall C received R).card <= L

/-- Distance zero is equality. -/
theorem hammingDistance_eq_zero_iff
    {N : Nat} {x y : Assignment N} :
    hammingDistance x y = 0 <-> x = y := by
  classical
  constructor
  · intro hzero
    apply funext
    intro i
    by_contra hne
    have hmem : i ∈
        (Finset.univ : Finset (Fin N)).filter (fun j => x j ≠ y j) := by
      simp [hne]
    have hempty :
        (Finset.univ : Finset (Fin N)).filter (fun j => x j ≠ y j) = ∅ :=
      Finset.card_eq_zero.mp hzero
    rw [hempty] at hmem
    exact Finset.notMem_empty i hmem
  · rintro rfl
    simp [hammingDistance]

/-- Every injective continuation code is uniquely decodable at radius zero. -/
theorem radiusZero_uniqueDecodable
    {m N : Nat} (C : RedundantContinuationCode m N) :
    HammingListDecodable C 0 1 := by
  intro received
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha0 : hammingDistance received (C.encode a) = 0 := by
    have := (Finset.mem_filter.mp ha).2
    omega
  have hb0 : hammingDistance received (C.encode b) = 0 := by
    have := (Finset.mem_filter.mp hb).2
    omega
  have hea : received = C.encode a := hammingDistance_eq_zero_iff.mp ha0
  have heb : received = C.encode b := hammingDistance_eq_zero_iff.mp hb0
  exact C.injective (hea.symm.trans heb)

/-! ## Solver cells as received words -/

/-- Each cell supplies a received word within radius `R` of the encoded true
continuation label. -/
structure CellReceivedWordProjection
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) (R : Nat) where
  received : Cell -> Assignment N
  trueCodewordNear : forall a : Assignment m,
    hammingDistance (received (cellOf a)) (C.encode a) <= R

/-- A code list-decoder plus a sound cell received-word map constructs semantic
cell list recovery. -/
noncomputable def listRecoveryOfReceivedWords
    {m N R L : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (hdecode : HammingListDecodable C R L)
    (P : CellReceivedWordProjection C cellOf R) :
    CellListRecovery cellOf L where
  candidates c := messageBall C (P.received c) R
  covers a := by
    classical
    unfold messageBall
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ a, P.trueCodewordNear a⟩
  listSize c := hdecode (P.received c)

/-- At radius zero, cell correspondence is already injective: two labels mapped
to one cell have the same received word and therefore the same codeword. -/
theorem cellOf_injective_of_radiusZero
    {m N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell)
    (P : CellReceivedWordProjection C cellOf 0) :
    Function.Injective cellOf := by
  intro a b hab
  apply C.injective
  have ha0 : hammingDistance (P.received (cellOf a)) (C.encode a) = 0 := by
    have := P.trueCodewordNear a
    omega
  have hb0 : hammingDistance (P.received (cellOf b)) (C.encode b) = 0 := by
    have := P.trueCodewordNear b
    omega
  have hea : P.received (cellOf a) = C.encode a :=
    hammingDistance_eq_zero_iff.mp ha0
  have heb : P.received (cellOf b) = C.encode b :=
    hammingDistance_eq_zero_iff.mp hb0
  rw [hab] at hea
  exact hea.symm.trans heb

/-! ## Solver-indexed composition endpoint -/

/-- The code theorem and the semantic cell-proximity theorem are separate fields.
Only the latter is allowed to depend on SAT correctness. -/
structure SolverReceivedWordListDecodingFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  N : Nat
  k : Nat
  d : Nat
  R : Nat
  code : RedundantContinuationCode m N
  Cell : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  cellOf : Assignment m -> Cell
  polyCells : @Fintype.card Cell cellFintype <= m ^ k
  codeListDecodable : HammingListDecodable code R (m ^ d)
  projection_of_decides : DecidesSAT U D ->
    @CellReceivedWordProjection m N Cell cellDecidableEq code cellOf R
  expGap : m ^ (k + d) < 2 ^ m

namespace SolverReceivedWordListDecodingFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- A genuine code theorem plus correctness-derived received-word projection
refutes the alleged solver. -/
theorem not_decidesSAT (B : SolverReceivedWordListDecodingFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype B.Cell := B.cellFintype
  letI : DecidableEq B.Cell := B.cellDecidableEq
  let L := listRecoveryOfReceivedWords B.code B.cellOf
    B.codeListDecodable (B.projection_of_decides hD)
  exact no_polynomial_cells_and_listRecovery B.cellOf B.polyCells L B.expGap

end SolverReceivedWordListDecodingFor

/-- Received-word/list-decoding bridges for every certified machine rule out
polynomial SAT decision. -/
theorem no_SATDecisionInP_of_receivedWordListDecoding
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverReceivedWordListDecodingFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨B⟩ := H D
  exact B.not_decidesSAT hD

end PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge.hammingDistance_eq_zero_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge.radiusZero_uniqueDecodable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge.cellOf_injective_of_radiusZero
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge.no_SATDecisionInP_of_receivedWordListDecoding
