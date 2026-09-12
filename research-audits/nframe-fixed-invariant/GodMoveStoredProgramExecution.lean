import GodMoveStoredBooleanProgram
import GodMoveBinaryPackingCost

/-!
# Counted serialization, decoding and execution of stored Boolean programs

The actual input and wire lists and the actual instruction list determine all
lengths and address caps through counted traversals. Decoding reads the emitted
Boolean data, and only its returned instructions are executed. A proof relates
that result to the original uncapped evaluator, including invalid references.

The bound includes this preparation and the encoder, decoder and evaluator
traversal counters. It excludes construction of the supplied instruction list,
lowering arbitrary Lean closures and a uniform tape-machine implementation.
-/

namespace GodMoveStoredProgramExecution

open GodMoveBooleanExecutionCost GodMoveStoredBooleanProgram
open GodMoveBinaryPackingCost
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

@[ext] structure Prepared where
  bits : List Bool
  fuel : ℕ
  deriving Repr, DecidableEq

def prepare (inputs vals : List Bool) (code : List Gate) : Execution Prepared :=
  let il := lengthFrom 0 inputs
  let vl := lengthFrom 0 vals
  let vg := lengthFrom vl.value code
  let fuel := lengthFrom 1 code
  let bits := emitProgram il.value vg.value code
  ⟨⟨bits.value, fuel.value⟩, il.steps + vl.steps + vg.steps + fuel.steps + bits.steps + 1⟩

theorem prepare_bits (inputs vals : List Bool) (code : List Gate) :
    (prepare inputs vals code).value.bits =
      programBits (code.map (capGate inputs.length (vals.length + code.length))) := by
  simp only [prepare, lengthFrom_value, zero_add, emitProgram_value]

theorem prepare_fuel (inputs vals : List Bool) (code : List Gate) :
    (prepare inputs vals code).value.fuel = code.length + 1 := by
  simp only [prepare, lengthFrom_value]
  omega

theorem capped_bounded (inputs vals : List Bool) (code : List Gate) :
    ∀ g ∈ code.map (capGate inputs.length (vals.length + code.length)),
      BoundedGate (inputs.length + vals.length + code.length) g := by
  intro g hg
  obtain ⟨g', _, rfl⟩ := List.mem_map.mp hg
  exact capGate_bounded _ _ _ g' (by omega) (by omega)

theorem prepare_bits_length_le (inputs vals : List Bool) (code : List Gate) :
    (prepare inputs vals code).value.bits.length ≤
      code.length * (2 * (inputs.length + vals.length + code.length) + 9) + 1 := by
  rw [prepare_bits]
  simpa only [List.length_map] using programBits_length_le _ _ (capped_bounded inputs vals code)

theorem prepare_steps_le (inputs vals : List Bool) (code : List Gate) :
    (prepare inputs vals code).steps ≤
      8 * code.length * (inputs.length + vals.length + code.length + 4) +
        4 * (inputs.length + vals.length + code.length) + 7 := by
  have h := emitProgram_steps_le inputs.length (vals.length + code.length)
    (inputs.length + vals.length + code.length) code (by omega) (by omega)
  simp only [prepare, lengthFrom_value, lengthFrom_steps, zero_add]
  omega

def executeEncoded (inputs vals : List Bool) (p : Prepared) : Execution (Option (List Bool)) :=
  let r := readProgram p.fuel p.bits
  match r.value with
  | some (code, _) =>
    let e := execute inputs vals code
    ⟨some e.value, r.steps + e.steps + 1⟩
  | none => ⟨none, r.steps + 1⟩

/-- The program's own terminator delimits it. Subsequent workspace and trailing
blank padding are neither rejected nor executed. Malformed streams are outside
this valid-encoding contract. -/
theorem executeEncoded_programBits_append (inputs vals : List Bool) (code : List Gate)
    (fuel : ℕ) (suffix : List Bool) (hf : code.length < fuel) :
    executeEncoded inputs vals ⟨programBits code ++ suffix, fuel⟩ =
      ⟨some (execute inputs vals code).value,
        programReadSteps code + (execute inputs vals code).steps + 1⟩ := by
  simp only [executeEncoded, readProgram_programBits code fuel suffix hf]

theorem executeEncoded_programBits (inputs vals : List Bool) (code : List Gate)
    (fuel : ℕ) (hf : code.length < fuel) :
    executeEncoded inputs vals ⟨programBits code, fuel⟩ =
      ⟨some (execute inputs vals code).value,
        programReadSteps code + (execute inputs vals code).steps + 1⟩ := by
  have h := readProgram_programBits code fuel [] hf
  simp only [List.append_nil] at h
  simp only [executeEncoded, h]

theorem executeEncoded_prepare (inputs vals : List Bool) (code : List Gate) :
    executeEncoded inputs vals (prepare inputs vals code).value =
      let capped := code.map (capGate inputs.length (vals.length + code.length))
      ⟨some (execute inputs vals capped).value,
        programReadSteps capped + (execute inputs vals capped).steps + 1⟩ := by
  have hp : (prepare inputs vals code).value =
      ⟨programBits (code.map (capGate inputs.length (vals.length + code.length))),
        code.length + 1⟩ := by
    apply Prepared.ext
    · exact prepare_bits inputs vals code
    · exact prepare_fuel inputs vals code
  rw [hp]
  apply executeEncoded_programBits
  simp only [List.length_map]
  omega

def executePrepared (inputs vals : List Bool) (code : List Gate) : Execution (Option (List Bool)) :=
  let p := prepare inputs vals code
  let e := executeEncoded inputs vals p.value
  ⟨e.value, p.steps + e.steps + 1⟩

theorem executePrepared_value (inputs vals : List Bool) (code : List Gate) :
    (executePrepared inputs vals code).value = some (execute inputs vals code).value := by
  simp only [executePrepared, executeEncoded_prepare]
  rw [execute_cap_value inputs vals inputs.length (vals.length + code.length) code le_rfl le_rfl]

theorem executePrepared_steps_le (inputs vals : List Bool) (code : List Gate) :
    (executePrepared inputs vals code).steps ≤
      32 * (inputs.length + vals.length + code.length + 4) ^ 2 := by
  let B := inputs.length + vals.length + code.length
  have hp := prepare_steps_le inputs vals code
  have hr := programReadSteps_le B _ (capped_bounded inputs vals code)
  have he := execute_steps_le inputs vals
    (code.map (capGate inputs.length (vals.length + code.length)))
  simp only [List.length_map] at hr he
  have hg : code.length ≤ B := by dsimp [B]; omega
  have hfirst : 8 * code.length * (B + 4) ≤ 8 * B * (B + 4) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hg)
  have hsecond : 7 * code.length * (B + 1) ≤ 7 * B * (B + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hg)
  change (prepare inputs vals code).steps ≤ 8 * code.length * (B + 4) + 4 * B + 7 at hp
  change (execute inputs vals
    (code.map (capGate inputs.length (vals.length + code.length)))).steps ≤
      7 * code.length * (B + 1) at he
  change (executePrepared inputs vals code).steps ≤ 32 * (B + 4) ^ 2
  simp only [executePrepared, executeEncoded_prepare]
  nlinarith

theorem executePrepared_lower_value {n : ℕ} (inputs vals : List Bool) (code : List (CGate n)) :
    (executePrepared inputs vals (code.map lowerGate)).value =
      some (runFrom (fun i => inputs.getD i.val false) vals code) := by
  rw [executePrepared_value, execute_lower_value]

/-- The encoded program can be given to a fixed interpreter as ordinary data;
no instruction count or address is stored in that interpreter's finite control. -/
theorem prepare_lower_bits_length_le {n : ℕ} (inputs vals : List Bool) (code : List (CGate n)) :
    (prepare inputs vals (code.map lowerGate)).value.bits.length ≤
      code.length * (2 * (inputs.length + vals.length + code.length) + 9) + 1 := by
  simpa only [List.length_map] using prepare_bits_length_le inputs vals (code.map lowerGate)

/-- Finite data round trips through every opcode, including out-of-range input
and wire addresses capped without changing their default-false answers. -/
example : (executePrepared [true] [false]
    [.input 0, .unary true false 1, .binary false true true false 0 1, .input 99,
      .constant true, .unary true false 99]).value =
      some [false, true, false, true, false, true, true] := by decide

example : (executePrepared [] [] []).value = some [] := by decide

example : executeEncoded [] [] ⟨[false], 1⟩ =
    executeEncoded [] [] ⟨[false, false], 1⟩ := by decide

end GodMoveStoredProgramExecution

#print axioms GodMoveStoredProgramExecution.prepare_bits
#print axioms GodMoveStoredProgramExecution.prepare_bits_length_le
#print axioms GodMoveStoredProgramExecution.prepare_steps_le
#print axioms GodMoveStoredProgramExecution.executeEncoded_programBits_append
#print axioms GodMoveStoredProgramExecution.executeEncoded_prepare
#print axioms GodMoveStoredProgramExecution.executePrepared_value
#print axioms GodMoveStoredProgramExecution.executePrepared_steps_le
#print axioms GodMoveStoredProgramExecution.executePrepared_lower_value
#print axioms GodMoveStoredProgramExecution.prepare_lower_bits_length_le
