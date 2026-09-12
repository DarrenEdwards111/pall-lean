import GodMoveBooleanExecutionCost

/-!
# A bounded Boolean encoding of executable circuit programs

Instructions store their truth tables and unary addresses as Boolean data.
Addresses beyond the final possible store are capped at a missing reference;
the evaluator's default-false convention makes this transformation exact,
including forward and invalid references. The cap bounds serialized size
without an additional well-formedness premise on the original program.

Encoding and decoding have explicit list/unary traversal counters. These
counters do not assert a compilation to the tape machine or count generation
of the original circuit and conversion of arbitrary Lean function closures.
-/

namespace GodMoveStoredBooleanProgram

open GodMoveBooleanExecutionCost

def capGate (I V : ℕ) : Gate → Gate
  | .constant b => .constant b
  | .input i => .input (min i I)
  | .unary f t i => .unary f t (min i V)
  | .binary ff ft tf tt i j => .binary ff ft tf tt (min i V) (min j V)

theorem getD_cap (xs : List Bool) (cap i : ℕ) (h : xs.length ≤ cap) :
    xs.getD (min i cap) false = xs.getD i false := by
  by_cases hi : i ≤ cap
  · rw [Nat.min_eq_left hi]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]

theorem executeGate_cap_value (inputs vals : List Bool) (I V : ℕ) (g : Gate)
    (hi : inputs.length ≤ I) (hv : vals.length ≤ V) :
    (executeGate inputs vals (capGate I V g)).value = (executeGate inputs vals g).value := by
  cases g <;> simp only [capGate, executeGate, readWire_value,
    getD_cap inputs I _ hi, getD_cap vals V _ hv]

theorem execute_cap_value (inputs vals : List Bool) (I V : ℕ) (code : List Gate)
    (hi : inputs.length ≤ I) (hv : vals.length + code.length ≤ V) :
    (execute inputs vals (code.map (capGate I V))).value = (execute inputs vals code).value := by
  induction code generalizing vals with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, execute, executeGate_cap_value inputs vals I V g hi (by
      simp only [List.length_cons] at hv; omega)]
    apply ih
    simp only [appendBit_value, List.length_append, List.length_singleton]
    simp only [List.length_cons] at hv
    omega

def BoundedGate (B : ℕ) : Gate → Prop
  | .constant _ => True
  | .input i => i ≤ B
  | .unary _ _ i => i ≤ B
  | .binary _ _ _ _ i j => i ≤ B ∧ j ≤ B

theorem capGate_bounded (I V B : ℕ) (g : Gate) (hi : I ≤ B) (hv : V ≤ B) :
    BoundedGate B (capGate I V g) := by
  cases g with
  | constant => trivial
  | input => exact (Nat.min_le_right _ _).trans hi
  | unary => exact (Nat.min_le_right _ _).trans hv
  | binary => exact ⟨(Nat.min_le_right _ _).trans hv, (Nat.min_le_right _ _).trans hv⟩

/-- Unary addresses have a false terminator. -/
def unary (i : ℕ) : List Bool := List.replicate i true ++ [false]

@[simp] theorem unary_length (i : ℕ) : (unary i).length = i + 1 := by simp [unary]

/-- Capped unary emission visits at most the cap many successor constructors;
it never constructs the potentially huge uncapped unary address. -/
def emitUnary : ℕ → ℕ → Execution (List Bool)
  | 0, _ => ⟨[false], 1⟩
  | _ + 1, 0 => ⟨[false], 1⟩
  | cap + 1, i + 1 =>
    let e := emitUnary cap i
    ⟨true :: e.value, e.steps + 1⟩

theorem emitUnary_spec (cap i : ℕ) :
    emitUnary cap i = ⟨unary (min i cap), min i cap + 1⟩ := by
  induction cap generalizing i with
  | zero => simp [emitUnary, unary]
  | succ cap ih =>
    cases i with
    | zero => simp [emitUnary, unary]
    | succ i => simp [emitUnary, ih, unary, List.replicate_succ, Nat.succ_min_succ]

def attach : List Bool → List Bool → Execution (List Bool)
  | [], ys => ⟨ys, 1⟩
  | x :: xs, ys =>
    let e := attach xs ys
    ⟨x :: e.value, e.steps + 1⟩

theorem attach_spec (xs ys : List Bool) : attach xs ys = ⟨xs ++ ys, xs.length + 1⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [attach, ih]

/-- Two opcode bits, followed by a fixed truth table and terminated addresses. -/
def gateBits : Gate → List Bool
  | .constant b => [false, false, b]
  | .input i => [false, true] ++ unary i
  | .unary f t i => [true, false, f, t] ++ unary i
  | .binary ff ft tf tt i j => [true, true, ff, ft, tf, tt] ++ unary i ++ unary j

theorem gateBits_length_le (B : ℕ) (g : Gate) (h : BoundedGate B g) :
    (gateBits g).length ≤ 2 * B + 8 := by
  cases g <;> simp only [BoundedGate] at h <;>
    simp only [gateBits, List.length_append, List.length_cons, List.length_nil, unary_length] <;> omega

def emitGate (I V : ℕ) : Gate → Execution (List Bool)
  | .constant b => ⟨[false, false, b], 4⟩
  | .input i =>
    let e := emitUnary I i
    ⟨false :: true :: e.value, e.steps + 3⟩
  | .unary f t i =>
    let e := emitUnary V i
    ⟨true :: false :: f :: t :: e.value, e.steps + 5⟩
  | .binary ff ft tf tt i j =>
    let x := emitUnary V i
    let y := emitUnary V j
    let a := attach x.value y.value
    ⟨true :: true :: ff :: ft :: tf :: tt :: a.value, x.steps + y.steps + a.steps + 7⟩

theorem emitGate_value (I V : ℕ) (g : Gate) :
    (emitGate I V g).value = gateBits (capGate I V g) := by
  cases g <;> simp [emitGate, emitUnary_spec, attach_spec, gateBits, capGate]

theorem emitGate_steps_le (I V B : ℕ) (g : Gate) (hi : I ≤ B) (hv : V ≤ B) :
    (emitGate I V g).steps ≤ 4 * (B + 4) := by
  cases g with
  | constant => simp only [emitGate]; omega
  | input i =>
    simp only [emitGate, emitUnary_spec]
    have h := Nat.min_le_right i I; omega
  | unary f t i =>
    simp only [emitGate, emitUnary_spec]
    have h := Nat.min_le_right i V; omega
  | binary ff ft tf tt i j =>
    simp only [emitGate, emitUnary_spec, attach_spec, unary_length]
    have h := Nat.min_le_right i V
    have h' := Nat.min_le_right j V
    omega

def programBits : List Gate → List Bool
  | [] => [false]
  | g :: gs => true :: (gateBits g ++ programBits gs)

def emitProgram (I V : ℕ) : List Gate → Execution (List Bool)
  | [] => ⟨[false], 2⟩
  | g :: gs =>
    let e := emitGate I V g
    let r := emitProgram I V gs
    let a := attach e.value r.value
    ⟨true :: a.value, e.steps + r.steps + a.steps + 2⟩

theorem emitProgram_value (I V : ℕ) (code : List Gate) :
    (emitProgram I V code).value = programBits (code.map (capGate I V)) := by
  induction code with
  | nil => rfl
  | cons g gs ih => simp only [emitProgram, attach_spec, emitGate_value, ih,
      List.map_cons, programBits]

theorem programBits_length_le (B : ℕ) (code : List Gate)
    (h : ∀ g ∈ code, BoundedGate B g) :
    (programBits code).length ≤ code.length * (2 * B + 9) + 1 := by
  induction code with
  | nil => simp [programBits]
  | cons g gs ih =>
    have hg := gateBits_length_le B g (h g (by simp))
    have ht := ih (fun g hg => h g (by simp [hg]))
    simp only [programBits, List.length_cons, List.length_append]
    nlinarith

theorem emitProgram_steps_le (I V B : ℕ) (code : List Gate) (hi : I ≤ B) (hv : V ≤ B) :
    (emitProgram I V code).steps ≤ 8 * code.length * (B + 4) + 2 := by
  induction code with
  | nil => simp [emitProgram]
  | cons g gs ih =>
    have hg := emitGate_steps_le I V B g hi hv
    have hl := gateBits_length_le B (capGate I V g) (capGate_bounded I V B g hi hv)
    rw [← emitGate_value] at hl
    simp only [emitProgram, attach_spec, List.length_cons]
    nlinarith

def readUnary : List Bool → Execution (Option (ℕ × List Bool))
  | [] => ⟨none, 1⟩
  | false :: bs => ⟨some (0, bs), 1⟩
  | true :: bs =>
    let e := readUnary bs
    ⟨e.value.map (fun p => (p.1 + 1, p.2)), e.steps + 2⟩

theorem readUnary_unary (i : ℕ) (suffix : List Bool) :
    readUnary (unary i ++ suffix) = ⟨some (i, suffix), 2 * i + 1⟩ := by
  induction i with
  | zero => simp [unary, readUnary]
  | succ i ih =>
    have he : unary (i + 1) = true :: unary i := by simp [unary, List.replicate_succ]
    rw [he, List.cons_append, readUnary, ih]
    simp only [Option.map_some]
    congr 1

/-- Eight dispatch units cover inspection of the fixed header and truth table.
Address traversal is charged by the actual unary reader. -/
def readGate : List Bool → Execution (Option (Gate × List Bool))
  | false :: false :: b :: rest => ⟨some (.constant b, rest), 8⟩
  | false :: true :: rest =>
    let e := readUnary rest
    ⟨e.value.map (fun p => (.input p.1, p.2)), e.steps + 8⟩
  | true :: false :: f :: t :: rest =>
    let e := readUnary rest
    ⟨e.value.map (fun p => (.unary f t p.1, p.2)), e.steps + 8⟩
  | true :: true :: ff :: ft :: tf :: tt :: rest =>
    let e := readUnary rest
    match e.value with
    | none => ⟨none, e.steps + 8⟩
    | some (i, rest') =>
      let e' := readUnary rest'
      ⟨e'.value.map (fun p => (.binary ff ft tf tt i p.1, p.2)), e.steps + e'.steps + 8⟩
  | _ => ⟨none, 8⟩

def gateReadSteps : Gate → ℕ
  | .constant _ => 8
  | .input i => 2 * i + 9
  | .unary _ _ i => 2 * i + 9
  | .binary _ _ _ _ i j => 2 * i + 2 * j + 10

theorem readGate_gateBits (g : Gate) (suffix : List Bool) :
    readGate (gateBits g ++ suffix) = ⟨some (g, suffix), gateReadSteps g⟩ := by
  cases g <;> simp only [gateBits, List.append_assoc, List.cons_append, List.nil_append,
    readGate, readUnary_unary, Option.map_some, gateReadSteps]
  congr 1
  omega

theorem gateReadSteps_le (B : ℕ) (g : Gate) (h : BoundedGate B g) :
    gateReadSteps g ≤ 4 * (B + 4) := by
  cases g <;> simp only [gateReadSteps, BoundedGate] at * <;> omega

def readProgram : ℕ → List Bool → Execution (Option (List Gate × List Bool))
  | 0, _ => ⟨none, 1⟩
  | _ + 1, [] => ⟨none, 1⟩
  | _ + 1, false :: rest => ⟨some ([], rest), 1⟩
  | fuel + 1, true :: rest =>
    let g := readGate rest
    match g.value with
    | none => ⟨none, g.steps + 2⟩
    | some (g', rest') =>
      let r := readProgram fuel rest'
      ⟨r.value.map (fun p => (g' :: p.1, p.2)), g.steps + r.steps + 2⟩

def programReadSteps : List Gate → ℕ
  | [] => 1
  | g :: gs => gateReadSteps g + programReadSteps gs + 2

theorem readProgram_programBits (code : List Gate) (fuel : ℕ) (suffix : List Bool)
    (hf : code.length < fuel) :
    readProgram fuel (programBits code ++ suffix) =
      ⟨some (code, suffix), programReadSteps code⟩ := by
  induction code generalizing fuel with
  | nil => cases fuel with
    | zero => simp at hf
    | succ fuel => rfl
  | cons g gs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have ht : gs.length < fuel := by simp only [List.length_cons] at hf; omega
      simp only [programBits, List.cons_append, List.append_assoc, readProgram,
        readGate_gateBits, ih fuel ht, Option.map_some, programReadSteps]

theorem programReadSteps_le (B : ℕ) (code : List Gate)
    (h : ∀ g ∈ code, BoundedGate B g) :
    programReadSteps code ≤ 8 * code.length * (B + 4) + 1 := by
  induction code with
  | nil => simp [programReadSteps]
  | cons g gs ih =>
    have hg := gateReadSteps_le B g (h g (by simp))
    have ht := ih (fun g hg => h g (by simp [hg]))
    simp only [programReadSteps, List.length_cons]
    nlinarith

end GodMoveStoredBooleanProgram

#print axioms GodMoveStoredBooleanProgram.execute_cap_value
#print axioms GodMoveStoredBooleanProgram.emitUnary_spec
#print axioms GodMoveStoredBooleanProgram.emitGate_value
#print axioms GodMoveStoredBooleanProgram.emitProgram_value
#print axioms GodMoveStoredBooleanProgram.programBits_length_le
#print axioms GodMoveStoredBooleanProgram.emitProgram_steps_le
#print axioms GodMoveStoredBooleanProgram.readGate_gateBits
#print axioms GodMoveStoredBooleanProgram.readProgram_programBits
#print axioms GodMoveStoredBooleanProgram.programReadSteps_le
