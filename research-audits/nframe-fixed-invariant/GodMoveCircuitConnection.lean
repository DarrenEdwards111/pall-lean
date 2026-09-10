import GodMoveFaithfulHandshake
import GodMoveSymbolicPinnedInput
import GodMoveCircuitArithmetization
import GodMoveCircuitNormalization
import GodMoveCircuitRuntimeCost
import GodMoveCircuitRankObstruction
import GodMoveCircuitStorage

/-!
# A compact machine-circuit source and its exact characteristic target

One circuit simulates the machine on the symbolic pinned-input template.
Its gate list and arithmetic DAG are constructed without enumerating the
assignments. The machine transition circuit is shared across that symbolic
input family. This is not an extraction from a single execution on the
original unpinned formula. Actual clocked-output equality is unconditional; SAT
correctness then identifies the Boolean-normalized polynomial with the verifier
characteristic, including all of its derivative/shift rows.

The explicit quartic clock bound controls circuit gates and arithmetic DAG
syntax, not the expanded normal form or its SPDP rank. An actual linear-size
circuit family disproves the generic polynomial gate-count-to-rank inference.
Thus this is a costed compact representation and exact denotational bridge,
not the missing efficient rank-bounded extraction or a SAT lower bound.
-/

namespace GodMoveCircuitConnection

open GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveFaithfulHandshake
open GodMoveSymbolicPinnedInput GodMoveCircuitNormalization GodMoveCircuitRuntimeCost
open MvPolynomial MultilinearSPDP SPDP
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine ComposableStepCircuit ComposablePpolyDischarge
open CookLevinReduction CookLevinEmitCodec NFrameBoundaryTransducer
open SATCircuitSeparationBridge SeparationTarget

/-- The circuit implements the actual clocked run, independently of any
language-correctness or halting premise. -/
theorem circuitFor_output (M : Machine) (L t : ℕ) (x : Fin L → Bool) :
    output (circuitFor M L t) x = decideOut M (wordOfFin x) t := by
  have hinit := runFrom_closed x (initGates M L (L + t + 1)) []
    (initGates_closed M L _)
  rw [List.nil_append] at hinit
  have hlen0 : ((initGates M L (L + t + 1)).map (closedEval x)).length
      = (L + t + 1) + (L + t + 1) + QM M := by
    rw [List.length_map, initGates_length]
  have hpos0 : ∀ pt : CPort M (L + t + 1),
      pidx M (L + t + 1) pt < ((initGates M L (L + t + 1)).map (closedEval x)).length ∧
      ((initGates M L (L + t + 1)).map (closedEval x)).getD
        (pidx M (L + t + 1) pt) false = snapV M (L + t + 1) (wordOfFin x) 0 pt := by
    intro pt
    exact ⟨by rw [hlen0]; exact pidx_lt M _ pt, initVals_at M _ x pt⟩
  obtain ⟨w, hrun, hlen, hval⟩ :=
    unrollC_spec M (L + t + 1) x t 0 (pidx M (L + t + 1))
      ((initGates M L (L + t + 1)).map (closedEval x)) (by omega) hpos0
  unfold output
  rw [circuitFor, runFrom_append, hinit,
    show ((L + t + 1) + (L + t + 1) + QM M) =
      ((initGates M L (L + t + 1)).map (closedEval x)).length from hlen0.symm, hrun]
  rw [show (initGates M L (L + t + 1) ++
        unrollC (n := L) M (L + t + 1) (pidx M (L + t + 1))
          ((initGates M L (L + t + 1)).map (closedEval x)).length t).length =
      (((initGates M L (L + t + 1)).map (closedEval x)) ++ w).length from by
    rw [List.length_append, List.length_append, initGates_length,
      unrollC_length, hlen0, hlen]]
  rw [hval, Nat.zero_add]
  rfl

/-- One machine circuit specialized to a symbolic, fixed-length pinned input. -/
noncomputable def compactCircuit (M : Machine) (T : ℕ → ℕ) (φ : Formula)
    (n : ℕ) : List (CGate n) :=
  specializeCircuit (pinnedSubstitution φ n)
    (circuitFor M (inputTemplate φ n).length (T (inputTemplate φ n).length))

theorem compactCircuit_length (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    (compactCircuit M T φ n).length =
      (circuitFor M (inputTemplate φ n).length (T (inputTemplate φ n).length)).length := by
  simp [compactCircuit]

/-- Every assignment gives the actual pinned run, with the original encoded
query length used by its clock. No SAT correctness is needed for simulation. -/
theorem compactCircuit_output {n : ℕ} (M : Machine) (T : ℕ → ℕ)
    (φ : Formula) (a : Assignment n) :
    output (compactCircuit M T φ n) a = queryOutput M T φ a := by
  rw [compactCircuit, output_specialize _ (pinnedSubstitution_closed φ n),
    circuitFor_output, pinnedSubstitution_wordOfFin]
  unfold queryOutput
  rw [encoded_pinned_length]

theorem compactCircuit_computes_verifier {n : ℕ} (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (φ : Formula) (hvars : VariablesBelow n φ) :
    computes (compactCircuit M T φ n)
      (fun a => evalFormula (extendAssignment a) φ) := by
  intro a
  rw [compactCircuit_output, queryOutput_eq_eval M T hD φ hvars]

/-- Retained shared arithmetic syntax, not an expanded polynomial. -/
noncomputable def compactSource (M : Machine) (T : ℕ → ℕ) (φ : Formula)
    (n : ℕ) : List (GodMoveCircuitArithmetization.AExpr n) :=
  GodMoveCircuitArithmetization.compile (compactCircuit M T φ n)

/-- The source polynomial's Boolean normal form. Its expansion cost is not
included in the circuit/DAG construction bound. -/
noncomputable def circuitTarget {n : ℕ} (c : List (CGate n)) : Poly n :=
  normalize (GodMoveCircuitArithmetization.rawPoly c)

theorem circuitTarget_eq_interpolate {n : ℕ} (c : List (CGate n)) :
    circuitTarget c = interpolate (output c) :=
  normalize_eq_interpolate _ _ (GodMoveCircuitArithmetization.eval_rawPoly c)

/-- Exact connection to the older truth-table source, derived from actual runs. -/
theorem compactTarget_eq_machineQueryPolynomial {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (φ : Formula) :
    circuitTarget (compactCircuit M T φ n) = machineQueryPolynomial M T φ := by
  rw [circuitTarget_eq_interpolate]
  exact interpolate_congr (compactCircuit_output M T φ)

/-- SAT correctness supplies the exact characteristic identity, without a
polynomial-identity or rank-transport hypothesis. -/
theorem compactTarget_eq_verifierCharacteristic {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) :
    circuitTarget (compactCircuit M T φ n) = verifierCharacteristic n φ := by
  rw [compactTarget_eq_machineQueryPolynomial,
    machineQueryPolynomial_eq_verifierCharacteristic M T hD φ hvars]

theorem compactTarget_row_eq {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) (S : List (Fin n)) (shift : Poly n) :
    mlProj (shift * iterDerivList S (circuitTarget (compactCircuit M T φ n))) =
      mlProj (shift * iterDerivList S (verifierCharacteristic n φ)) := by
  rw [compactTarget_eq_verifierCharacteristic M T hD φ hvars]

theorem compactTarget_strict_rank_eq {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) (B : BlockPartition n) (k ell : ℕ) :
    mlBlockedSpdpRank B k ell (circuitTarget (compactCircuit M T φ n)) =
      mlBlockedSpdpRank B k ell (verifierCharacteristic n φ) := by
  rw [compactTarget_eq_verifierCharacteristic M T hD φ hvars]

theorem compactTarget_inclusive_rank_eq {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) (B : BlockPartition n) (k ell : ℕ) :
    mlBlockedSpdpRankInc B k ell (circuitTarget (compactCircuit M T φ n)) =
      mlBlockedSpdpRankInc B k ell (verifierCharacteristic n φ) := by
  rw [compactTarget_eq_verifierCharacteristic M T hD φ hvars]

theorem compactCircuit_length_le (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    (compactCircuit M T φ n).length ≤ circuitConstant M *
      ((inputTemplate φ n).length + T (inputTemplate φ n).length + 1) ^ 4 := by
  rw [compactCircuit_length]
  exact circuitFor_length_le_quartic M _ _

/-- Explicit source syntax cost in the actual pinned-input length and clock. -/
theorem compactSource_cost_le (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    GodMoveCircuitArithmetization.representationCost (compactSource M T φ n) ≤
      25 * circuitConstant M *
        ((inputTemplate φ n).length + T (inputTemplate φ n).length + 1) ^ 4 := by
  exact (GodMoveCircuitArithmetization.compile_cost_le _).trans
    (by simpa only [mul_assoc] using
      Nat.mul_le_mul_left 25 (compactCircuit_length_le M T φ n))

theorem compactSource_arithmeticCost_le (M : Machine) (T : ℕ → ℕ) (φ : Formula) (n : ℕ) :
    GodMoveCircuitArithmetization.arithmeticCost (compactSource M T φ n) ≤
      12 * circuitConstant M *
        ((inputTemplate φ n).length + T (inputTemplate φ n).length + 1) ^ 4 := by
  exact (GodMoveCircuitArithmetization.compile_arithmeticCost_le _).trans
    (by simpa only [mul_assoc] using
      Nat.mul_le_mul_left 12 (compactCircuit_length_le M T φ n))

/-- An explicit bit representation of the source circuit. Its input arity `n`
is supplied separately to the verified decoder. Invalid reads are folded
into gate truth tables, giving bounded stored wire indices. -/
noncomputable def encodedCompactCircuit (M : Machine) (T : ℕ → ℕ)
    (φ : Formula) (n : ℕ) : List Bool :=
  GodMoveCircuitStorage.encodeCircuit
    (GodMoveCircuitStorage.sanitize (compactCircuit M T φ n))

theorem encodedCompactCircuit_roundtrip (M : Machine) (T : ℕ → ℕ)
    (φ : Formula) (n : ℕ) (rest : List Bool) :
    GodMoveCircuitStorage.decodeCircuit n (encodedCompactCircuit M T φ n ++ rest) =
      some (GodMoveCircuitStorage.sanitize (compactCircuit M T φ n), rest) :=
  GodMoveCircuitStorage.decodeCircuit_encodeCircuit _ _

theorem encodedCompactCircuit_length_le (M : Machine) (T : ℕ → ℕ)
    (φ : Formula) (n : ℕ) :
    (encodedCompactCircuit M T φ n).length ≤
      (9 + 2 * (n + (compactCircuit M T φ n).length)) *
        (compactCircuit M T φ n).length + 1 :=
  GodMoveCircuitStorage.encodeCircuit_sanitize_length_le _

/-- Decoding the stored source retains the actual machine query behavior. -/
theorem storedCompactCircuit_output {n : ℕ} (M : Machine) (T : ℕ → ℕ)
    (φ : Formula) (a : Assignment n) :
    output (GodMoveCircuitStorage.sanitize (compactCircuit M T φ n)) a =
      queryOutput M T φ a := by
  rw [GodMoveCircuitStorage.output_sanitize, compactCircuit_output]

/-- The explicitly stored source has the same exact characteristic target. -/
theorem storedCompactTarget_eq_verifierCharacteristic {n : ℕ}
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) :
    circuitTarget (GodMoveCircuitStorage.sanitize (compactCircuit M T φ n)) =
      verifierCharacteristic n φ := by
  rw [circuitTarget_eq_interpolate]
  have hout : output (GodMoveCircuitStorage.sanitize (compactCircuit M T φ n)) =
      output (compactCircuit M T φ n) :=
    funext (GodMoveCircuitStorage.output_sanitize _)
  rw [hout, ← circuitTarget_eq_interpolate,
    compactTarget_eq_verifierCharacteristic M T hD φ hvars]

/-- The denotational bridge cannot turn arbitrary circuit size bounds into a
bound on the same normalized characteristic rank. -/
theorem no_polynomial_circuitTarget_strict_bound :
    ¬ ∃ C d : ℕ, ∀ n (c : List (CGate n)),
      mlBlockedSpdpRank (GodMoveMonomialMinor.discreteBlocks n) (Nat.log 2 n) 0
        (circuitTarget c) ≤ C * (n + c.length + 1) ^ d := by
  simpa only [circuitTarget_eq_interpolate] using
    GodMoveCircuitRankObstruction.no_polynomial_circuit_strict_bound

theorem no_polynomial_circuitTarget_inclusive_bound :
    ¬ ∃ C d : ℕ, ∀ n (c : List (CGate n)),
      mlBlockedSpdpRankInc (GodMoveMonomialMinor.discreteBlocks n) (Nat.log 2 n) 0
        (circuitTarget c) ≤ C * (n + c.length + 1) ^ d := by
  simpa only [circuitTarget_eq_interpolate] using
    GodMoveCircuitRankObstruction.no_polynomial_circuit_inclusive_bound

end GodMoveCircuitConnection

#print axioms GodMoveCircuitConnection.circuitFor_output
#print axioms GodMoveCircuitConnection.compactCircuit_output
#print axioms GodMoveCircuitConnection.compactCircuit_computes_verifier
#print axioms GodMoveCircuitConnection.circuitTarget_eq_interpolate
#print axioms GodMoveCircuitConnection.compactTarget_eq_machineQueryPolynomial
#print axioms GodMoveCircuitConnection.compactTarget_eq_verifierCharacteristic
#print axioms GodMoveCircuitConnection.compactTarget_row_eq
#print axioms GodMoveCircuitConnection.compactTarget_strict_rank_eq
#print axioms GodMoveCircuitConnection.compactTarget_inclusive_rank_eq
#print axioms GodMoveCircuitConnection.compactCircuit_length_le
#print axioms GodMoveCircuitConnection.compactSource_cost_le
#print axioms GodMoveCircuitConnection.compactSource_arithmeticCost_le
#print axioms GodMoveCircuitConnection.encodedCompactCircuit_roundtrip
#print axioms GodMoveCircuitConnection.encodedCompactCircuit_length_le
#print axioms GodMoveCircuitConnection.storedCompactCircuit_output
#print axioms GodMoveCircuitConnection.storedCompactTarget_eq_verifierCharacteristic
#print axioms GodMoveCircuitConnection.no_polynomial_circuitTarget_strict_bound
#print axioms GodMoveCircuitConnection.no_polynomial_circuitTarget_inclusive_bound
