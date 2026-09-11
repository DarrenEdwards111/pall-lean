import GodMoveRationalWireEncoding
import GodMoveBooleanExecutionCost

/-!
# Materialized signed rational results from the binary evaluator

All three output fields, including the computed sign, are read from the actual
executed wire store. Canonical representation is a theorem about these returned
Boolean lists, not a rational value calculated alongside the binary program.
The counter has the explicit traversal-model scope of BooleanExecutionCost;
it excludes code generation and compilation into a physical machine.
-/

namespace GodMoveBinaryScalarExecution

open GodMoveBinaryAdder GodMoveSignedBinary GodMoveBinaryMultiply
open GodMoveRationalWireEncoding GodMoveBooleanExecutionCost
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

structure FractionBits where
  negative : Bool
  numerator : List Bool
  denominator : List Bool
  deriving Repr, DecidableEq

def FractionBits.value (r : FractionBits) : ℚ :=
  (signedMagnitude r.negative (bitsValue r.numerator) : ℚ) / bitsValue r.denominator

def FractionBits.Represents (r : FractionBits) (q : ℚ) : Prop :=
  signedMagnitude r.negative (bitsValue r.numerator) = q.num ∧
    bitsValue r.denominator = q.den

theorem FractionBits.Represents.value_eq {r : FractionBits} {q : ℚ}
    (h : r.Represents q) : r.value = q := by
  rw [FractionBits.value, h.1, h.2, Rat.num_div_den]

/-- Both words and the sign are materialized from this execution's result. -/
def executeFraction {n : ℕ} (inputs vals : List Bool) (code : List (CGate n))
    (r : FractionRefs) : Execution FractionBits :=
  let e := execute inputs vals (code.map lowerGate)
  let sign := readWire e.value r.sign
  let num := collectWord e.value r.numerator
  let den := collectWord e.value r.denominator
  ⟨⟨sign.value, num.value, den.value⟩, e.steps + sign.steps + num.steps + den.steps + 1⟩

theorem executeFraction_represents {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (r : FractionRefs) (q : ℚ)
    (h : GodMoveRationalWireEncoding.Represents
      (runFrom (fun i => inputs.getD i.val false) vals code) r q) :
    (executeFraction inputs vals code r).value.Represents q := by
  simpa only [executeFraction, FractionBits.Represents, collectWord_value,
    readWire_value, bitsValue_readWord, execute_lower_value, Represents,
    GodMoveRationalWireEncoding.signedValue] using h

theorem executeFraction_steps_le {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (r : FractionRefs) (G R : ℕ)
    (hg : code.length ≤ G) (hr : r.numerator.length + r.denominator.length + 1 ≤ R) :
    (executeFraction inputs vals code r).steps ≤
      7 * G * (inputs.length + vals.length + G + 1) + R * (vals.length + G + 2) + 1 := by
  have he := execute_lower_steps_le_of_gate_bound inputs vals code G hg
  have hs := readWire_steps_le (execute inputs vals (code.map lowerGate)).value r.sign
  have hn := collectWord_steps_le (execute inputs vals (code.map lowerGate)).value r.numerator
  have hd := collectWord_steps_le (execute inputs vals (code.map lowerGate)).value r.denominator
  simp only [execute_value_length, List.length_map] at hs hn hd
  have hword : r.numerator.length + r.denominator.length + 1 ≤ R := hr
  have hcollect := Nat.mul_le_mul hword
    (show vals.length + code.length + 2 ≤ vals.length + G + 2 by omega)
  dsimp only [executeFraction]
  nlinarith

theorem bitsValue_append_zero (xs : List Bool) (k : ℕ) :
    bitsValue (xs ++ List.replicate k false) = bitsValue xs := by
  induction xs with
  | nil => induction k with
    | zero => rfl
    | succ k ih =>
      have hk : bitsValue (List.replicate k false) = 0 := ih
      simp [List.replicate_succ, bitsValue, hk]
  | cons b bs ih => simp only [List.cons_append, bitsValue, ih]

/-- Padding is explicit Boolean data and preserves the magnitude. -/
def padBits (w : ℕ) (xs : List Bool) : List Bool :=
  xs ++ List.replicate (w - xs.length) false

theorem padBits_length (w : ℕ) (xs : List Bool) (h : xs.length ≤ w) :
    (padBits w xs).length = w := by simp [padBits]; omega

theorem padBits_value (w : ℕ) (xs : List Bool) : bitsValue (padBits w xs) = bitsValue xs :=
  bitsValue_append_zero xs _

def pack (w : ℕ) (r : FractionBits) : List Bool :=
  [r.negative] ++ padBits w r.numerator ++ padBits w r.denominator

def packedRefs (start w : ℕ) : FractionRefs :=
  ⟨start, List.range' (start + 1) w, List.range' (start + 1 + w) w⟩

theorem pack_length (w : ℕ) (r : FractionBits)
    (hn : r.numerator.length ≤ w) (hd : r.denominator.length ≤ w) :
    (pack w r).length = 2 * w + 1 := by
  simp only [pack, List.length_append, List.length_singleton, padBits_length w _ hn,
    padBits_length w _ hd]
  omega

theorem packedRefs_width (start w : ℕ) : Width (packedRefs start w) w := by
  constructor <;> simp [packedRefs]

theorem packedRefs_valid (start w : ℕ) : Valid (packedRefs start w) (start + (2 * w + 1)) := by
  refine ⟨by dsimp [packedRefs]; omega, ?_, ?_⟩
  · intro i hi
    have h := List.mem_range'.mp hi
    omega
  · intro i hi
    have h := List.mem_range'.mp hi
    omega

theorem wordValue_append_old (vals suffix : List Bool) (refs : List ℕ)
    (h : ∀ i ∈ refs, i < vals.length) :
    wordValue (vals ++ suffix) refs = wordValue vals refs := by
  induction refs with
  | nil => rfl
  | cons i is ih =>
    rw [wordValue, wordValue, List.getD_append _ _ _ _ (h i (by simp)), ih]
    exact fun j hj => h j (by simp [hj])

theorem wordValue_range_segment (pre bits post : List Bool) :
    wordValue ((pre ++ bits) ++ post) (List.range' pre.length bits.length) = bitsValue bits := by
  rw [wordValue_append_old]
  · exact GodMoveControlledWord.wordValue_range_append pre bits
  · intro i hi
    have h := List.mem_range'.mp hi
    simp only [List.length_append]
    omega

/-- Any prefix and suffix may surround the packed operand; references point
only into its own explicit segment. -/
theorem packedRefs_represents (pre post : List Bool) (r : FractionBits) (q : ℚ) (w : ℕ)
    (hn : r.numerator.length ≤ w) (hd : r.denominator.length ≤ w)
    (h : r.Represents q) :
    GodMoveRationalWireEncoding.Represents (pre ++ pack w r ++ post)
      (packedRefs pre.length w) q := by
  have hs : (pre ++ pack w r ++ post).getD pre.length false = r.negative := by
    simp only [pack, List.append_assoc,
      GodMoveBinaryAdder.read_append_start, List.cons_append, List.getD_cons_zero]
  have hnum : wordValue (pre ++ pack w r ++ post) (List.range' (pre.length + 1) w) =
      bitsValue r.numerator := by
    have he := wordValue_range_segment (pre ++ [r.negative]) (padBits w r.numerator)
      (padBits w r.denominator ++ post)
    simpa only [List.length_append, List.length_singleton, padBits_length w _ hn,
      padBits_value, pack, List.append_assoc] using he
  have hden : wordValue (pre ++ pack w r ++ post) (List.range' (pre.length + 1 + w) w) =
      bitsValue r.denominator := by
    have he := wordValue_range_segment (pre ++ [r.negative] ++ padBits w r.numerator)
      (padBits w r.denominator) post
    simpa only [List.length_append, List.length_singleton, padBits_length w _ hn,
      padBits_length w _ hd, padBits_value, pack, List.append_assoc, Nat.add_assoc] using he
  constructor
  · change signedMagnitude _ _ = _
    change signedMagnitude ((pre ++ pack w r ++ post).getD pre.length false)
      (wordValue (pre ++ pack w r ++ post) (List.range' (pre.length + 1) w)) = _
    rw [hs, hnum]
    exact h.1
  · exact hden.trans h.2

end GodMoveBinaryScalarExecution

#print axioms GodMoveBinaryScalarExecution.executeFraction_represents
#print axioms GodMoveBinaryScalarExecution.executeFraction_steps_le
#print axioms GodMoveBinaryScalarExecution.padBits_value
#print axioms GodMoveBinaryScalarExecution.pack_length
#print axioms GodMoveBinaryScalarExecution.packedRefs_valid
#print axioms GodMoveBinaryScalarExecution.packedRefs_represents
