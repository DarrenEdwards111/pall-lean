import GodMoveBinaryAdder
import GodMoveSignedBinary

/-!
# Controlled binary coefficient words from actual Boolean wires

For each supplied coefficient bit, emit one unary gate reading the existing
selector wire and taking its conjunction with that bit. The fresh output
references are contiguous and interpreted in little-endian order. The output
word therefore represents the coefficient when the selector is true, and
zero when it is false.

The coefficient bit string is explicit input. This component emits exactly
one gate per bit and performs no assignment enumeration or polynomial
expansion. It makes no claim about the size of coefficients supplied by an
upstream rational computation.
-/

namespace GodMoveControlledWord

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open GodMoveBinaryAdder
open GodMoveSignedBinary (bitsValue)

def controlledWord {n : ℕ} (start selector : ℕ) (bits : List Bool) :
    List (CGate n) × List ℕ :=
  (bits.map (fun bit => .un (fun b => b && bit) selector),
    List.range' start bits.length)

theorem controlledWord_gate_count {n : ℕ} (start selector : ℕ) (bits : List Bool) :
    (controlledWord (n := n) start selector bits).1.length = bits.length := by
  simp [controlledWord]

theorem controlledWord_word_length {n : ℕ} (start selector : ℕ) (bits : List Bool) :
    (controlledWord (n := n) start selector bits).2.length = bits.length := by
  simp [controlledWord]

theorem controlledWord_refs_bounds {n : ℕ} (start selector : ℕ) (bits : List Bool) :
    ∀ i ∈ (controlledWord (n := n) start selector bits).2,
      start ≤ i ∧ i < start + bits.length := by
  intro i hi
  obtain ⟨j, hj, he⟩ := List.mem_range'.mp hi
  simp only [Nat.one_mul] at he
  omega

theorem controlledWord_refs_lt {n : ℕ} (start selector : ℕ) (bits : List Bool) :
    ∀ i ∈ (controlledWord (n := n) start selector bits).2, i < start + bits.length :=
  fun i hi => (controlledWord_refs_bounds start selector bits i hi).2

/-- Every gate reads the same supplied selector, which precedes every emitted
position when `selector < start`. -/
theorem controlledWord_gate_refs {n : ℕ} (start selector : ℕ) (bits : List Bool)
    (hselector : selector < start) :
    ∀ g ∈ (controlledWord (n := n) start selector bits).1,
      ∃ bit ∈ bits, g = .un (fun b => b && bit) selector ∧ selector < start := by
  intro g hg
  obtain ⟨bit, hb, rfl⟩ := List.mem_map.mp hg
  exact ⟨bit, hb, rfl, hselector⟩

theorem bitsValue_mask (b : Bool) (bits : List Bool) :
    bitsValue (bits.map (fun bit => b && bit)) = if b then bitsValue bits else 0 := by
  induction bits with
  | nil => cases b <;> rfl
  | cons bit bits ih => cases b <;> simp_all [bitsValue]

/-- Reading contiguous fresh references recovers the appended bit string. -/
theorem wordValue_range_append (vals bits : List Bool) :
    wordValue (vals ++ bits) (List.range' vals.length bits.length) = bitsValue bits := by
  induction bits generalizing vals with
  | nil => simp [wordValue, bitsValue]
  | cons bit bits ih =>
      have ht := ih (vals ++ [bit])
      simp only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] at ht
      simp only [List.length_cons, List.range'_succ, wordValue, bitsValue]
      rw [ht, read_append_start]
      rfl

/-- The emitted circuit appends exactly the controlled coefficient bits. -/
theorem controlledWord_runFrom {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (start selector : ℕ) (bits : List Bool) (hselector : selector < vals.length) :
    runFrom a vals (controlledWord (n := n) start selector bits).1 =
      vals ++ bits.map (fun bit => vals.getD selector false && bit) := by
  unfold controlledWord
  induction bits generalizing vals with
  | nil => simp [runFrom]
  | cons bit bits ih =>
      simp only [List.map_cons, runFrom, evalGate]
      have hnext : selector < (vals ++ [vals.getD selector false && bit]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [ih _ hnext]
      rw [List.getD_append _ _ _ _ hselector]
      simp only [List.append_assoc, List.singleton_append]

/-- Exact numeric value for an arbitrary initial wire state and input. -/
theorem controlledWord_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (selector : ℕ) (bits : List Bool) (hselector : selector < vals.length) :
    wordValue (runFrom a vals (controlledWord (n := n) vals.length selector bits).1)
      (controlledWord (n := n) vals.length selector bits).2 =
      if vals.getD selector false then bitsValue bits else 0 := by
  rw [controlledWord_runFrom a vals vals.length selector bits hselector]
  change wordValue (vals ++ bits.map (fun bit => vals.getD selector false && bit))
    (List.range' vals.length bits.length) = _
  rw [← List.length_map (f := fun bit => vals.getD selector false && bit) (as := bits),
    wordValue_range_append, bitsValue_mask]

/-- The supplied binary width gives an exact ordinary natural coefficient. -/
theorem controlledWord_bitsOf_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (selector width value : ℕ) (hselector : selector < vals.length)
    (hvalue : value < 2 ^ width) :
    wordValue (runFrom a vals
      (controlledWord (n := n) vals.length selector (GodMoveSignedBinary.bitsOf width value)).1)
      (controlledWord (n := n) vals.length selector (GodMoveSignedBinary.bitsOf width value)).2 =
      if vals.getD selector false then value else 0 := by
  rw [controlledWord_spec a vals selector _ hselector,
    GodMoveSignedBinary.bitsOf_value width value hvalue]

end GodMoveControlledWord

#print axioms GodMoveControlledWord.controlledWord_gate_count
#print axioms GodMoveControlledWord.controlledWord_word_length
#print axioms GodMoveControlledWord.controlledWord_refs_bounds
#print axioms GodMoveControlledWord.controlledWord_gate_refs
#print axioms GodMoveControlledWord.controlledWord_runFrom
#print axioms GodMoveControlledWord.controlledWord_spec
#print axioms GodMoveControlledWord.controlledWord_bitsOf_spec
