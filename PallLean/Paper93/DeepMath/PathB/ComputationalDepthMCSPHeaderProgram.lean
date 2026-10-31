import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFiniteControlCompiler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteMCSP

/-!
# Compiled MCSP verifier, phase 1: the unary-header parser

An encoded MCSP input begins

`1^n 0 1^s 0 table`

where `n` is the circuit arity and `s` is the size threshold.  This file gives
the first actual program written in `FiniteControlCompiler` assembly:

* phase `0` scans the unary arity;
* phase `1` scans the unary threshold;
* phase `2` halts, with the head on the first truth-table bit.

The source run is proved exactly on canonical headers and then transported
through the compiler.  The program is also total on arbitrary finite inputs:
the Boolean tape's `false` padding supplies both missing terminators, so it
halts within `|x| + 2` steps.

The parser intentionally does not claim to retain `n` and `s`; later phases
will copy the unary fields into doubled work blocks before consuming them.
This brick establishes the executable control flow and its clock.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPHeaderProgram

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.FiniteControlCompiler
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSP
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeNatBits)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- A no-write action moving right. -/
def right (q : Fin 3) : Action (Fin 3) :=
  ⟨q, none, 1⟩

/-- The two-field unary header scanner. -/
def headerProgram : Program where
  Label := Fin 3
  fin := inferInstance
  dec := inferInstance
  start := 0
  code
    | 0 => .act (right 1) (right 0)
    | 1 => .act (right 2) (right 1)
    | _ => .halt false

/-- Its compiled faithful machine. -/
def headerMachine : Machine :=
  compile headerProgram

@[simp] theorem header_code_zero :
    headerProgram.code (0 : Fin 3) = .act (right 1) (right 0) := rfl

@[simp] theorem header_code_one :
    headerProgram.code (1 : Fin 3) = .act (right 2) (right 1) := rfl

@[simp] theorem header_code_two :
    headerProgram.code (2 : Fin 3) = .halt false := rfl

/-- One source step over a live unary bit. -/
theorem step_phase0_true {p : ℕ} {t : List Bool}
    (h : t.getD p false = true) :
    asmStep headerProgram ⟨(0 : Fin 3), p, t⟩ =
      ⟨(0 : Fin 3), p + 1, t⟩ := by
  unfold asmStep
  rw [header_code_zero]
  rw [h]
  rfl

/-- The first unary terminator switches to the threshold scan. -/
theorem step_phase0_false {p : ℕ} {t : List Bool}
    (h : t.getD p false = false) :
    asmStep headerProgram ⟨(0 : Fin 3), p, t⟩ =
      ⟨(1 : Fin 3), p + 1, t⟩ := by
  unfold asmStep
  rw [header_code_zero]
  rw [h]
  rfl

/-- One source step over a live threshold bit. -/
theorem step_phase1_true {p : ℕ} {t : List Bool}
    (h : t.getD p false = true) :
    asmStep headerProgram ⟨(1 : Fin 3), p, t⟩ =
      ⟨(1 : Fin 3), p + 1, t⟩ := by
  unfold asmStep
  rw [header_code_one]
  rw [h]
  rfl

/-- The second unary terminator enters the halt label at the table start. -/
theorem step_phase1_false {p : ℕ} {t : List Bool}
    (h : t.getD p false = false) :
    asmStep headerProgram ⟨(1 : Fin 3), p, t⟩ =
      ⟨(2 : Fin 3), p + 1, t⟩ := by
  unfold asmStep
  rw [header_code_one]
  rw [h]
  rfl

/-- Reading a bit inside a `true` block. -/
theorem getD_true_block (P Z : List Bool) {i k : ℕ} (hi : i < k) :
    (P ++ (List.replicate k true ++ Z)).getD (P.length + i) false = true := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simp; omega),
    List.getElem?_replicate]
  simp [hi]

/-- Reading the terminator immediately after a `true` block. -/
theorem getD_after_true_block (P Z : List Bool) (k : ℕ) :
    (P ++ (List.replicate k true ++ false :: Z)).getD
      (P.length + k) false = false := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp

/-- Phase `0` scans exactly `k` live unary bits. -/
theorem scan_phase0 (P Z : List Bool) (k : ℕ) :
    asmRun headerProgram k
      ⟨(0 : Fin 3), P.length, P ++ (List.replicate k true ++ Z)⟩ =
      ⟨(0 : Fin 3), P.length + k, P ++ (List.replicate k true ++ Z)⟩ := by
  induction k generalizing P with
  | zero => simp [asmRun_zero]
  | succ k ih =>
      simp only [List.replicate_succ]
      rw [show k + 1 = 1 + k by omega, asmRun_add]
      change asmRun headerProgram k
        (asmStep headerProgram
          ⟨(0 : Fin 3), P.length, P ++ (true :: List.replicate k true ++ Z)⟩) = _
      have hread :
          (P ++ (true :: List.replicate k true ++ Z)).getD P.length false =
            true := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega)]
        simp
      rw [step_phase0_true hread]
      have H := ih (P ++ [true])
      convert H using 1 <;> simp [List.append_assoc] <;> omega

/-- Phase `1` scans exactly `k` live threshold bits. -/
theorem scan_phase1 (P Z : List Bool) (k : ℕ) :
    asmRun headerProgram k
      ⟨(1 : Fin 3), P.length, P ++ (List.replicate k true ++ Z)⟩ =
      ⟨(1 : Fin 3), P.length + k, P ++ (List.replicate k true ++ Z)⟩ := by
  induction k generalizing P with
  | zero => simp [asmRun_zero]
  | succ k ih =>
      simp only [List.replicate_succ]
      rw [show k + 1 = 1 + k by omega, asmRun_add]
      change asmRun headerProgram k
        (asmStep headerProgram
          ⟨(1 : Fin 3), P.length, P ++ (true :: List.replicate k true ++ Z)⟩) = _
      have hread :
          (P ++ (true :: List.replicate k true ++ Z)).getD P.length false =
            true := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega)]
        simp
      rw [step_phase1_true hread]
      have H := ih (P ++ [true])
      convert H using 1 <;> simp [List.append_assoc] <;> omega

/-- Scan and consume the first unary field's terminator. -/
theorem scan_phase0_term (P Z : List Bool) (k : ℕ) :
    asmRun headerProgram (k + 1)
      ⟨(0 : Fin 3), P.length,
        P ++ (List.replicate k true ++ false :: Z)⟩ =
      ⟨(1 : Fin 3), P.length + k + 1,
        P ++ (List.replicate k true ++ false :: Z)⟩ := by
  rw [asmRun_succ, scan_phase0]
  rw [step_phase0_false (getD_after_true_block P Z k)]

/-- Scan and consume the second unary field's terminator. -/
theorem scan_phase1_term (P Z : List Bool) (k : ℕ) :
    asmRun headerProgram (k + 1)
      ⟨(1 : Fin 3), P.length,
        P ++ (List.replicate k true ++ false :: Z)⟩ =
      ⟨(2 : Fin 3), P.length + k + 1,
        P ++ (List.replicate k true ++ false :: Z)⟩ := by
  rw [asmRun_succ, scan_phase1]
  rw [step_phase1_false (getD_after_true_block P Z k)]

/-- Exact source run on a canonical two-field header. -/
theorem asmRun_header (n s : ℕ) (tableAndWitness : List Bool) :
    asmRun headerProgram (n + 1 + s + 1)
      (asmInit headerProgram
        (encodeNatBits n ++ encodeNatBits s ++ tableAndWitness)) =
      ⟨(2 : Fin 3), n + 1 + s + 1,
        encodeNatBits n ++ encodeNatBits s ++ tableAndWitness⟩ := by
  rw [show n + 1 + s + 1 = n + 1 + (s + 1) by omega,
    asmRun_add]
  rw [show encodeNatBits n ++ encodeNatBits s ++ tableAndWitness =
      List.replicate n true ++ false :: (encodeNatBits s ++ tableAndWitness) by
        simp [encodeNatBits, List.append_assoc],
    show asmInit headerProgram
        (List.replicate n true ++ false :: (encodeNatBits s ++ tableAndWitness)) =
      ⟨(0 : Fin 3), 0,
        List.replicate n true ++ false :: (encodeNatBits s ++ tableAndWitness)⟩ from rfl]
  have h0 := scan_phase0_term [] (encodeNatBits s ++ tableAndWitness) n
  simp only [List.length_nil, List.nil_append, Nat.zero_add] at h0
  rw [h0]
  rw [show List.replicate n true ++ false :: (encodeNatBits s ++ tableAndWitness) =
      (List.replicate n true ++ [false]) ++
        (List.replicate s true ++ false :: tableAndWitness) by
      simp [encodeNatBits, List.append_assoc]]
  have h1 := scan_phase1_term
    (List.replicate n true ++ [false]) tableAndWitness s
  simp only [List.length_append, List.length_replicate,
    List.length_singleton] at h1
  rw [h1]
  simp [List.append_assoc]
  omega

/-- Exact compiled-machine run on a canonical MCSP header. -/
theorem machine_run_header (n s : ℕ) (tableAndWitness : List Bool) :
    run headerMachine (n + 1 + s + 1)
      (init headerMachine
        (encodeNatBits n ++ encodeNatBits s ++ tableAndWitness)) =
      ⟨(2 : Fin 3), n + 1 + s + 1,
        encodeNatBits n ++ encodeNatBits s ++ tableAndWitness⟩ := by
  unfold headerMachine
  rw [compile_run_init, asmRun_header]
  rfl

/-- The compiled parser genuinely halts after the canonical header. -/
theorem machine_halts_header (n s : ℕ) (tableAndWitness : List Bool) :
    HaltsBy headerMachine
      (encodeNatBits n ++ encodeNatBits s ++ tableAndWitness)
      (n + 1 + s + 1) := by
  unfold HaltsBy
  rw [machine_run_header]
  rfl

/-- The canonical header clock is bounded by total tape length. -/
theorem header_clock_le_length (n s : ℕ) (z : List Bool) :
    n + 1 + s + 1 ≤
      (encodeNatBits n ++ encodeNatBits s ++ z).length := by
  simp [encodeNatBits]
  omega

/-- The uniform linear clock used by the parser. -/
def headerClock (N : ℕ) : ℕ := N + 2

theorem headerClock_poly : PolyBounded headerClock :=
  ⟨3, 1, fun N => by simp [headerClock]; omega⟩

end PallLean.Paper93.DeepMath.PathB.MCSPHeaderProgram

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPHeaderProgram.asmRun_header
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPHeaderProgram.machine_run_header
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPHeaderProgram.machine_halts_header
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPHeaderProgram.headerClock_poly
