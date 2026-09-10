import GodMoveCircuitConnection
import GodMovePinnedFaceLayout
import GodMoveBooleanFace
import GodMoveMultilinearRestriction

/-!
# A concrete rank-monotone face extraction from the normalized machine source

The source is the Boolean-normalized output polynomial of the actual unrolled
machine on all words of the pinned input length. The gauge fixes the encoded
formula/header bits and retains each assignment bit at its unique position.
It depends only on the input template, not a satisfying assignment. It is a
concrete linear idempotent substitution, and its rank transport is derived at
the same partition and derivative/shift parameters.

Correct SAT-machine behavior identifies the extracted polynomial with the
renamed verifier characteristic. This target is not thereby identified with
the paper's hard coupled sheet. The gate bound below controls circuit syntax;
no polynomial SPDP bound for the normalized source is proved or assumed here.
In particular, Boolean normalization is not a rank-free construction step.
-/

namespace GodMoveMachineFaceExtraction

open MvPolynomial MultilinearSPDP SPDP PiStarConcrete
open GodMoveBooleanInterpolation GodMoveCircuitNormalization GodMoveBooleanFace
open GodMoveSymbolicPinnedInput GodMovePinnedFaceLayout GodMovePinnedSATQueries
open GodMoveCircuitConnection GodMoveFaithfulHandshake GodMoveMultilinearRestriction
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine ComposableStepCircuit ComposablePpolyDischarge
open NFrameBoundaryTransducer CookLevinReduction SeparationTarget

/-- The actual machine's normalized output polynomial, before template pinning. -/
noncomputable def machineSource (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    Poly (inputTemplate φ n).length :=
  circuitTarget (circuitFor M (inputTemplate φ n).length (T (inputTemplate φ n).length))

theorem machineSource_multilinear (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    IsMultilinear (machineSource M T φ n) :=
  normalize_isMultilinear _

/-- Formula-dependent constant restriction with no SAT witness parameter. -/
noncomputable def pinnedGauge (φ : Formula) (n : ℕ) :
    Poly (inputTemplate φ n).length →ₗ[ℚ] Poly (inputTemplate φ n).length := by
  classical
  exact piSubst (pinnedKeep φ n) (fun j => bit (pinnedFixed φ n j))

theorem pinnedGauge_idempotent (φ : Formula) (n : ℕ) :
    pinnedGauge φ n ∘ₗ pinnedGauge φ n = pinnedGauge φ n := by
  classical
  exact piSubst_idempotent _ _

/-- Restricting the encoded input bits executes precisely the specialized
machine circuit, for every ambient Boolean input and every machine. -/
theorem machine_face_output (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ)
    (a : Assignment (inputTemplate φ n).length) :
    output (circuitFor M (inputTemplate φ n).length (T (inputTemplate φ n).length))
        (fun j => if pinnedKeep φ n j then a j else pinnedFixed φ n j) =
      output (compactCircuit M T φ n) (fun i => a (variablePosition φ n i)) := by
  classical
  rw [compactCircuit, output_specialize _ (pinnedSubstitution_closed φ n)]
  rw [pinnedFace_eq]

/-- Exact polynomial extraction follows from actual circuit semantics and
multilinearity, without a SAT correctness or rank hypothesis. -/
theorem pinnedGauge_extracts_compactTarget
    (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    pinnedGauge φ n (machineSource M T φ n) =
      rename (variablePosition φ n) (circuitTarget (compactCircuit M T φ n)) := by
  classical
  apply multilinear_eq_of_boolean_eval
  · exact isMultilinear_piSubst _ _ _ (machineSource_multilinear M T φ n)
  · exact isMultilinear_rename _ (variablePosition_injective φ n) _
      (normalize_isMultilinear _)
  · intro a
    change MvPolynomial.eval (booleanPoint a)
        (piSubst (pinnedKeep φ n) (fun j => bit (pinnedFixed φ n j))
          (machineSource M T φ n)) = _
    rw [eval_piSubst_boolean, eval_rename_boolean, machineSource,
      circuitTarget_eq_interpolate, circuitTarget_eq_interpolate,
      eval_interpolate, eval_interpolate, machine_face_output]

/-- Faithful SAT correctness identifies this concrete projection's target. -/
theorem pinnedGauge_extracts_verifier
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (n : ℕ) (hvars : VariablesBelow n φ) :
    pinnedGauge φ n (machineSource M T φ n) =
      rename (variablePosition φ n) (verifierCharacteristic n φ) := by
  rw [pinnedGauge_extracts_compactTarget,
    compactTarget_eq_verifierCharacteristic M T hD φ hvars]

/-- No-loss strict rank extraction, in the source's original ambient space. -/
theorem verifier_rank_le_machineSource
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (n : ℕ) (hvars : VariablesBelow n φ)
    (B : BlockPartition (inputTemplate φ n).length) (k ell : ℕ) :
    mlBlockedSpdpRank B k ell
        (rename (variablePosition φ n) (verifierCharacteristic n φ)) ≤
      mlBlockedSpdpRank B k ell (machineSource M T φ n) := by
  classical
  rw [← pinnedGauge_extracts_verifier M T hD φ n hvars]
  exact mlBlockedSpdpRank_piSubst_le _ _ B k ell _
    (machineSource_multilinear M T φ n)

/-- The identical concrete extraction also preserves the inclusive window. -/
theorem verifier_inclusive_rank_le_machineSource
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (n : ℕ) (hvars : VariablesBelow n φ)
    (B : BlockPartition (inputTemplate φ n).length) (k ell : ℕ) :
    mlBlockedSpdpRankInc B k ell
        (rename (variablePosition φ n) (verifierCharacteristic n φ)) ≤
      mlBlockedSpdpRankInc B k ell (machineSource M T φ n) := by
  classical
  rw [← pinnedGauge_extracts_verifier M T hD φ n hvars]
  exact mlBlockedSpdpRankInc_piSubst_le _ _ B k ell _
    (machineSource_multilinear M T φ n)

/-- The underlying machine circuit has the already-derived quartic gate bound.
This is deliberately a syntax bound, not a bound on the normalized SPDP rank. -/
theorem machineSource_circuit_length_le
    (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    (circuitFor M (inputTemplate φ n).length (T (inputTemplate φ n).length)).length ≤
      GodMoveCircuitRuntimeCost.circuitConstant M *
        ((inputTemplate φ n).length + T (inputTemplate φ n).length + 1) ^ 4 :=
  GodMoveCircuitRuntimeCost.circuitFor_length_le_quartic M _ _

end GodMoveMachineFaceExtraction

#print axioms GodMoveMachineFaceExtraction.machineSource_multilinear
#print axioms GodMoveMachineFaceExtraction.pinnedGauge_idempotent
#print axioms GodMoveMachineFaceExtraction.machine_face_output
#print axioms GodMoveMachineFaceExtraction.pinnedGauge_extracts_compactTarget
#print axioms GodMoveMachineFaceExtraction.pinnedGauge_extracts_verifier
#print axioms GodMoveMachineFaceExtraction.verifier_rank_le_machineSource
#print axioms GodMoveMachineFaceExtraction.verifier_inclusive_rank_le_machineSource
#print axioms GodMoveMachineFaceExtraction.machineSource_circuit_length_le
