import GodMoveSymbolicPinnedInput
import GodMoveCubeWitnessSearch
import GodMoveCircuitCNFSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitUniversality

/-!
# Circuit-existence queries executed by a supplied SAT machine

The query is the faithful encoding of the existing Tseitin CNF of the supplied
Boolean circuit. Its answer comes from running the actual supplied machine
for its supplied clock. Correctness is derived from `Decides M SATLang T` and
the proved circuit-to-CNF encoding; no general predicate oracle is assumed.

Circuit witness search fixes one input at a time using closed-gate
specialization, preserving the gate count. It uses at most `n+1` SAT-machine
calls and returns an accepting assignment exactly when one exists.

The SAT machine and its correctness remain hypotheses. These constructions
do not produce a SAT decider, assert a polynomial clock, implement a compiler
for rational wire relations, or prove a complete discovery runtime bound.
-/

namespace GodMoveMachineCircuitOracle

open GodMoveBooleanInterpolation GodMoveSymbolicPinnedInput
open GodMoveCubeWitnessSearch (exists_iff_head restrictHead)
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine NFrameBoundaryTransducer CookLevinEmitCodec
open SeparationTarget (SATLang SATLang_encode)
open CircuitUniversality (tseitin universality)

/-- The exact word supplied to the SAT decider, with every gate constraint
encoded by the existing circuit-to-CNF construction. -/
def circuitQuery {n : ℕ} (c : List (CGate n)) : List Bool :=
  encodeFormula' (tseitin c)

/-- This is an actual clocked machine answer, not an abstract oracle value. -/
def circuitSAT (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) : Bool :=
  decideOut M (circuitQuery c) (T (circuitQuery c).length)

theorem circuitSAT_halts (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    HaltsBy M (circuitQuery c) (T (circuitQuery c).length) :=
  (hD (circuitQuery c)).1

/-- The existential query is derived from machine correctness and the actual
Tseitin encoding, without a supplied circuit-answer equivalence. -/
theorem circuitSAT_correct (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    circuitSAT M T c = true ↔ ∃ a : Assignment n, output c a = true := by
  rw [circuitSAT, (hD (circuitQuery c)).2]
  exact (SATLang_encode (tseitin c)).trans (universality n c)

/-- The existing faithful codec gives a quadratic query-word size bound. -/
theorem circuitQuery_length_le {n : ℕ} (c : List (CGate n)) :
    (circuitQuery c).length ≤ 100 * (n + c.length + 1) ^ 2 :=
  GodMoveCircuitCNFSize.tseitin_encoded_length_le_quadratic c

/-- A supplied polynomial clock gives this explicit majorant for each actual
SAT-machine call. This excludes construction and interpreter overhead. -/
theorem circuitClock_le (T : ℕ → ℕ) (C d : ℕ)
    (hT : ∀ m, T m ≤ C * (m + 1) ^ d) {n : ℕ} (c : List (CGate n)) :
    T (circuitQuery c).length ≤ (C * 101 ^ d) * (n + c.length + 1) ^ (2 * d) := by
  have hlen : (circuitQuery c).length + 1 ≤ 101 * (n + c.length + 1) ^ 2 := by
    have h := circuitQuery_length_le c
    have hpos : 0 < (n + c.length + 1) ^ 2 := by positivity
    nlinarith only [h, hpos]
  calc
    _ ≤ C * ((circuitQuery c).length + 1) ^ d := hT _
    _ ≤ C * (101 * (n + c.length + 1) ^ 2) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hlen d)
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      ring

theorem circuitClock_polynomial (T : ℕ → ℕ)
    (hT : PvsNPSeparatingInvariant.PolyBounded T) :
    ∃ C d : ℕ, ∀ (n : ℕ) (c : List (CGate n)),
      T (circuitQuery c).length ≤ C * (n + c.length + 1) ^ d := by
  obtain ⟨C, d, hT⟩ := hT
  exact ⟨C * 101 ^ d, 2 * d, fun _ c => circuitClock_le T C d hT c⟩

/-- Fix the first input and renumber the others, changing no wire indices or
number of gates. The substitution consists entirely of closed input gates. -/
def fixHead {n : ℕ} (c : List (CGate (n + 1))) (b : Bool) : List (CGate n) :=
  specializeCircuit (Fin.cases (.cst b) (fun i => .var i)) c

theorem fixHead_length {n : ℕ} (c : List (CGate (n + 1))) (b : Bool) :
    (fixHead c b).length = c.length := by simp [fixHead]

theorem output_fixHead {n : ℕ} (c : List (CGate (n + 1))) (b : Bool)
    (a : Assignment n) : output (fixHead c b) a = output c (Fin.cons b a) := by
  have hclosed : ∀ i : Fin (n + 1),
      IsClosedGate (Fin.cases (.cst b) (fun j : Fin n => .var j) i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> trivial
  rw [fixHead, output_specialize _ hclosed]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Satisfiability of a circuit splits into the two restricted circuits. -/
theorem exists_output_iff_head {n : ℕ} (c : List (CGate (n + 1))) :
    (∃ a, output c a = true) ↔
      (∃ a, output (fixHead c false) a = true) ∨
      (∃ a, output (fixHead c true) a = true) := by
  simpa only [restrictHead, output_fixHead] using exists_iff_head (output c)

/-- The caller has established existence. Each level makes one actual SAT
query on a restricted circuit and records the number of such calls. -/
def descendWithCount (M : Machine) (T : ℕ → ℕ) :
    (n : ℕ) → List (CGate n) → Assignment n × ℕ
  | 0, _ => (fun i => Fin.elim0 i, 0)
  | n + 1, c =>
      let b := if circuitSAT M T (fixHead c false) then false else true
      let rest := descendWithCount M T n (fixHead c b)
      (Fin.cons b rest.1, rest.2 + 1)

theorem descendWithCount_count (M : Machine) (T : ℕ → ℕ)
    (n : ℕ) (c : List (CGate n)) : (descendWithCount M T n c).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [descendWithCount]; rw [ih]

theorem descendWithCount_correct (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (n : ℕ) (c : List (CGate n))
    (hex : ∃ a, output c a = true) : output c (descendWithCount M T n c).1 = true := by
  induction n with
  | zero =>
      obtain ⟨a, ha⟩ := hex
      have he : (fun i => Fin.elim0 i : Assignment 0) = a := by
        funext i
        exact Fin.elim0 i
      simpa only [descendWithCount, he] using ha
  | succ n ih =>
      cases hq : circuitSAT M T (fixHead c false) with
      | false =>
          have hn : ¬ ∃ a, output (fixHead c false) a = true := by
            intro h
            have hy := (circuitSAT_correct M T hD _).mpr h
            simp [hq] at hy
          have ht := ((exists_output_iff_head c).mp hex).resolve_left hn
          have hrec := ih (fixHead c true) ht
          rw [output_fixHead] at hrec
          simpa only [descendWithCount, hq, Bool.false_eq_true, ↓reduceIte] using hrec
      | true =>
          have hf := (circuitSAT_correct M T hD _).mp hq
          have hrec := ih (fixHead c false) hf
          rw [output_fixHead] at hrec
          simpa only [descendWithCount, hq, ↓reduceIte] using hrec

/-- One initial machine query followed by one query per coordinate on the
accepting branch. No assignment enumeration enters this definition. -/
def findWitnessWithCount (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    Option (Assignment n) × ℕ :=
  if circuitSAT M T c then
    let result := descendWithCount M T n c
    (some result.1, result.2 + 1)
  else (none, 1)

def findWitness (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    Option (Assignment n) := (findWitnessWithCount M T c).1

theorem findWitnessWithCount_count (M : Machine) (T : ℕ → ℕ)
    {n : ℕ} (c : List (CGate n)) :
    (findWitnessWithCount M T c).2 = if circuitSAT M T c then n + 1 else 1 := by
  cases h : circuitSAT M T c <;> simp [findWitnessWithCount, descendWithCount_count, h]

theorem findWitnessWithCount_count_le (M : Machine) (T : ℕ → ℕ)
    {n : ℕ} (c : List (CGate n)) : (findWitnessWithCount M T c).2 ≤ n + 1 := by
  rw [findWitnessWithCount_count]
  split <;> omega

theorem findWitness_some_correct (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) (a : Assignment n)
    (ha : findWitness M T c = some a) : output c a = true := by
  unfold findWitness findWitnessWithCount at ha
  split at ha
  next hq =>
    have he : (descendWithCount M T n c).1 = a := Option.some.inj ha
    rw [← he]
    exact descendWithCount_correct M T hD n c ((circuitSAT_correct M T hD c).mp hq)
  next hq => simp at ha

theorem findWitness_none_iff (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    findWitness M T c = none ↔ ¬ ∃ a : Assignment n, output c a = true := by
  simp only [findWitness, findWitnessWithCount]
  split
  next hq => simp [(circuitSAT_correct M T hD c).mp hq]
  next hq =>
    have hn : ¬ ∃ a : Assignment n, output c a = true :=
      fun h => hq ((circuitSAT_correct M T hD c).mpr h)
    simp [hn]

theorem findWitness_exists_some_iff (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (∃ a, findWitness M T c = some a) ↔ ∃ a : Assignment n, output c a = true := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, findWitness_some_correct M T hD c a ha⟩
  · intro hex
    cases h : findWitness M T c with
    | none => exact False.elim ((findWitness_none_iff M T hD c).mp h hex)
    | some a => exact ⟨a, rfl⟩

end GodMoveMachineCircuitOracle

#print axioms GodMoveMachineCircuitOracle.circuitSAT_halts
#print axioms GodMoveMachineCircuitOracle.circuitSAT_correct
#print axioms GodMoveMachineCircuitOracle.fixHead_length
#print axioms GodMoveMachineCircuitOracle.output_fixHead
#print axioms GodMoveMachineCircuitOracle.descendWithCount_count
#print axioms GodMoveMachineCircuitOracle.descendWithCount_correct
#print axioms GodMoveMachineCircuitOracle.findWitnessWithCount_count_le
#print axioms GodMoveMachineCircuitOracle.findWitness_some_correct
#print axioms GodMoveMachineCircuitOracle.findWitness_none_iff
#print axioms GodMoveMachineCircuitOracle.findWitness_exists_some_iff

#print axioms GodMoveMachineCircuitOracle.circuitQuery_length_le
#print axioms GodMoveMachineCircuitOracle.circuitClock_le
#print axioms GodMoveMachineCircuitOracle.circuitClock_polynomial
