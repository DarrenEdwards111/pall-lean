import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSolverOrientedConservationNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPDynamicHolonomyQueryTranscriptBridge

/-!
# N-frame continuation transcripts: exact conservation and the compression endpoint

The previous audit showed that one SAT decision bit does not preserve a complete
search/orientation label.  The natural repair is SAT self-reduction: expose each
label coordinate by a concrete continuation query and collect all answers.

This file tests that repair using the repository's solver-independent
`independentSATQueryFamily`.  Correctness genuinely transports every coordinate:

```text
correct SAT decider + m continuation queries
  -> exact m-bit answer transcript
  -> exact conservation of the weighted N-frame orientation charge.
```

That part works.  The obstruction moves to compression.  The complete transcript
carrier has exactly `2^m` states, even though it contains only `m` Boolean query
answers.  Any amplituhedron cell map that conserves the injective weighted charge
must still have at least `2^m` cells.  Hence self-reduction supplies decision
relevance, but it does not supply a polynomial positive-cell quotient.

Finally, the universal assertion that every correct SAT decider admits such a
polynomial conserving quotient is proved equivalent to `¬ SATDecisionInP U`; the
reverse implication is vacuous.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameContinuationTranscriptEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyDecisionRelevance
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint

/-! ## Exact decision-relevant continuation transcript -/

/-- The complete continuation transcript is the vector of all coordinate-query
answers returned by the alleged solver. -/
noncomputable def continuationAnswers
    {m : Nat} {U : MachineModel} (D : DecisionMachine U)
    (batch : (independentSATQueryFamily m).Instance) :
    HolonomySignature m :=
  (independentSATQueryFamily m).answers D batch

/-- SAT correctness really does identify the complete continuation transcript
with the semantic orientation label. -/
theorem continuationAnswers_eq_label
    {m : Nat} {U : MachineModel} (D : DecisionMachine U)
    (hD : DecidesSAT U D)
    (batch : (independentSATQueryFamily m).Instance) :
    continuationAnswers D batch = (independentSATQueryFamily m).label batch :=
  (independentSATQueryFamily m).answers_eq_label D hD batch

/-- Therefore the full, uncompressed continuation transcript exactly conserves
the gauge-fixed weighted N-frame orientation charge. -/
theorem exact_continuationTranscript_conserves_orientedAction
    {m : Nat} {U : MachineModel} (D : DecisionMachine U)
    (hD : DecidesSAT U D) :
    forall batch : (independentSATQueryFamily m).Instance,
      weightedOrientationAction ((independentSATQueryFamily m).label batch) =
        weightedOrientationAction (continuationAnswers D batch) := by
  intro batch
  rw [continuationAnswers_eq_label D hD batch]

/-- The exact transcript carrier has `2^m` possible states.  Linear query count
does not mean polynomially many complete answer patterns. -/
theorem continuationTranscript_card (m : Nat) :
    Fintype.card (HolonomySignature m) = 2 ^ m := by
  simp [HolonomySignature, Fintype.card_bool, Fintype.card_fin]

/-! ## Any charge-conserving quotient remains exponential -/

/-- A proposed amplituhedron compression of the solver's complete continuation
answer vector. -/
structure ContinuationCellCompression
    (m : Nat) {U : MachineModel} (D : DecisionMachine U) where
  Cell : Type
  cellFintype : Fintype Cell
  compress : HolonomySignature m -> Cell
  cellAction : Cell -> Real
  conserves : forall batch : (independentSATQueryFamily m).Instance,
    weightedOrientationAction ((independentSATQueryFamily m).label batch) =
      cellAction (compress (continuationAnswers D batch))

namespace ContinuationCellCompression

variable {m : Nat} {U : MachineModel} {D : DecisionMachine U}

/-- If the solver is SAT-correct, conservation makes the compression injective
on every possible continuation signature. -/
theorem compress_injective
    (C : ContinuationCellCompression m D) (hD : DecidesSAT U D) :
    Function.Injective C.compress := by
  intro left right hcell
  apply weightedOrientationAction_injective
  obtain ⟨leftBatch, hleft⟩ :=
    (independentSATQueryFamily m).label_surjective left
  obtain ⟨rightBatch, hright⟩ :=
    (independentSATQueryFamily m).label_surjective right
  have hleftAnswers : continuationAnswers D leftBatch = left := by
    rw [continuationAnswers_eq_label D hD leftBatch, hleft]
  have hrightAnswers : continuationAnswers D rightBatch = right := by
    rw [continuationAnswers_eq_label D hD rightBatch, hright]
  calc
    weightedOrientationAction left =
        weightedOrientationAction
          ((independentSATQueryFamily m).label leftBatch) := by rw [hleft]
    _ = C.cellAction (C.compress (continuationAnswers D leftBatch)) :=
      C.conserves leftBatch
    _ = C.cellAction (C.compress left) := by rw [hleftAnswers]
    _ = C.cellAction (C.compress right) := by rw [hcell]
    _ = C.cellAction (C.compress (continuationAnswers D rightBatch)) := by
      rw [hrightAnswers]
    _ = weightedOrientationAction
          ((independentSATQueryFamily m).label rightBatch) :=
      (C.conserves rightBatch).symm
    _ = weightedOrientationAction right := by rw [hright]

/-- Consequently every exact charge-conserving continuation quotient has at
least `2^m` cells. -/
theorem two_pow_le_cell_card
    (C : ContinuationCellCompression m D) (hD : DecidesSAT U D) :
    2 ^ m <= @Fintype.card C.Cell C.cellFintype := by
  letI : Fintype C.Cell := C.cellFintype
  have hcard := Fintype.card_le_of_injective C.compress
    (C.compress_injective hD)
  simpa [HolonomySignature, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] using hcard

end ContinuationCellCompression

/-! ## Exact polynomial-compression calibration -/

/-- The proposed polynomial positive-cell endpoint for one correct solver. -/
structure PolynomialContinuationConservationFor
    (U : MachineModel) (D : DecisionMachine U) (hD : DecidesSAT U D) where
  m : Nat
  k : Nat
  compression : ContinuationCellCompression m D
  polyCells : @Fintype.card compression.Cell compression.cellFintype <= m ^ k
  expGap : m ^ k < 2 ^ m

namespace PolynomialContinuationConservationFor

variable {U : MachineModel} {D : DecisionMachine U} {hD : DecidesSAT U D}

/-- Self-reduction correctness plus exact oriented conservation contradicts a
polynomial cell bound below the exponential gap. -/
theorem impossible
    (P : PolynomialContinuationConservationFor U D hD) : False := by
  have hlower := P.compression.two_pow_le_cell_card hD
  exact (Nat.not_lt_of_ge (le_trans hlower P.polyCells)) P.expGap

end PolynomialContinuationConservationFor

/-- Universal claim that every correct SAT decider admits a polynomial
charge-conserving continuation quotient. -/
def EverySATDeciderHasPolynomialContinuationConservation
    (U : MachineModel) : Prop :=
  forall (D : DecisionMachine U) (hD : DecidesSAT U D),
    Nonempty (PolynomialContinuationConservationFor U D hD)

/-- Exact endpoint: the universal compression theorem is the SAT lower bound,
not a consequence of ordinary decision-to-search self-reduction. -/
theorem everySATDeciderHasPolynomialContinuationConservation_iff
    (U : MachineModel) :
    EverySATDeciderHasPolynomialContinuationConservation U <->
      ¬ SATDecisionInP U := by
  constructor
  · intro H hSAT
    obtain ⟨D, hD⟩ := hSAT
    obtain ⟨P⟩ := H D hD
    exact P.impossible
  · intro hNo D hD
    exact False.elim (hNo ⟨D, hD⟩)

end PallLean.Paper93.DeepMath.PathB.NFrameContinuationTranscriptEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameContinuationTranscriptEndpoint.continuationAnswers_eq_label
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameContinuationTranscriptEndpoint.exact_continuationTranscript_conserves_orientedAction
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameContinuationTranscriptEndpoint.ContinuationCellCompression.two_pow_le_cell_card
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameContinuationTranscriptEndpoint.everySATDeciderHasPolynomialContinuationConservation_iff
