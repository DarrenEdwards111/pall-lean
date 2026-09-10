import GodMoveWireSampleCertificate
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Executable exhaustive Boolean wire evaluation table

Assignments are constructed recursively by prepending `false` and `true`.
The resulting list contains every assignment exactly once and has exactly
`2^n` entries. Every row is obtained by running the original Boolean circuit
and reading its wire values, then converting Boolean values to rationals.
These values equal evaluations of the normalized symbolic wire polynomials.

The table is a concrete input for exact row-space scanning. Its exponential
assignment count is explicit; this construction makes no claim of polynomial
sample discovery and does not expand any normalized polynomial.
-/

namespace GodMoveBooleanWireTable

open GodMoveBooleanInterpolation GodMoveComputedWireRank
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate runFrom)

/-- Exhaustive assignments, in deterministic false-head/true-head order. -/
def allAssignments : (n : ℕ) → List (Assignment n)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (allAssignments n).map (Fin.cons false) ++
      (allAssignments n).map (Fin.cons true)

theorem allAssignments_complete (n : ℕ) (a : Assignment n) : a ∈ allAssignments n := by
  induction n with
  | zero =>
    simp only [allAssignments, List.mem_singleton]
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have ht := ih (Fin.tail a)
    have he := Fin.cons_self_tail a
    rw [allAssignments, List.mem_append]
    cases ha : a 0
    · left
      exact List.mem_map.mpr ⟨Fin.tail a, ht, by simpa only [ha] using he⟩
    · right
      exact List.mem_map.mpr ⟨Fin.tail a, ht, by simpa only [ha] using he⟩

theorem allAssignments_length (n : ℕ) : (allAssignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allAssignments, ih, Nat.pow_succ, Nat.mul_two]

theorem allAssignments_nodup (n : ℕ) : (allAssignments n).Nodup := by
  induction n with
  | zero => simp [allAssignments]
  | succ n ih =>
    rw [allAssignments, List.nodup_append]
    have hf : Function.Injective (@Fin.cons n (fun _ => Bool) false) := by
      intro a b h
      funext i
      exact congrFun h i.succ
    have ht : Function.Injective (@Fin.cons n (fun _ => Bool) true) := by
      intro a b h
      funext i
      exact congrFun h i.succ
    refine ⟨ih.map hf, ih.map ht, ?_⟩
    intro a ha b hb he
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    have hz := congrFun he 0
    simp at hz

/-- One exact numeric row, retaining the shared Boolean circuit execution.
The local `vals` list is produced before the row's coordinate function. -/
def wireRow {n : ℕ} (c : List (CGate n)) (a : Assignment n) : Fin c.length → ℚ :=
  let vals := runFrom a [] c
  fun i => bit (vals.getD i.val false)

theorem wireRow_eq_normalized_eval {n : ℕ} (c : List (CGate n))
    (a : Assignment n) (i : Fin c.length) :
    wireRow c a i = MvPolynomial.eval (booleanPoint a)
      ((normalizedWires c).getD i.val 0) :=
  (GodMoveWireSampleCertificate.eval_normalizedWire c a i.val).symm

/-- Numeric rows with their assignment labels, ready for a deterministic scan. -/
def wireTable {n : ℕ} (c : List (CGate n)) :
    List (Assignment n × (Fin c.length → ℚ)) :=
  (allAssignments n).map (fun a => (a, wireRow c a))

theorem wireTable_length {n : ℕ} (c : List (CGate n)) :
    (wireTable c).length = 2 ^ n := by
  simp [wireTable, allAssignments_length]

theorem wireTable_contains {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    (a, wireRow c a) ∈ wireTable c :=
  List.mem_map.mpr ⟨a, allAssignments_complete n a, rfl⟩

theorem wireTable_labels {n : ℕ} (c : List (CGate n)) :
    (wireTable c).map Prod.fst = allAssignments n := by
  simp [wireTable, List.map_map, Function.comp_def]

theorem wireTable_labels_nodup {n : ℕ} (c : List (CGate n)) :
    ((wireTable c).map Prod.fst).Nodup := by
  rw [wireTable_labels]
  exact allAssignments_nodup n

end GodMoveBooleanWireTable

#print axioms GodMoveBooleanWireTable.allAssignments_complete
#print axioms GodMoveBooleanWireTable.allAssignments_length
#print axioms GodMoveBooleanWireTable.allAssignments_nodup
#print axioms GodMoveBooleanWireTable.wireRow_eq_normalized_eval
#print axioms GodMoveBooleanWireTable.wireTable_length
#print axioms GodMoveBooleanWireTable.wireTable_contains
#print axioms GodMoveBooleanWireTable.wireTable_labels_nodup
