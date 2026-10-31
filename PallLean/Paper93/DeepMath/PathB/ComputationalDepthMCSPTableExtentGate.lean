import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPTableMaterializeMachine

/-!
# MCSP verifier: sound table-extent gate

This file closes the semantic soundness gap between the finite-control table
materializer and the already verified destructive unary comparators.

For a proposed bound `N`, the gate executes both finite-control comparisons

* `N ≤ table.length`;
* `table.length ≤ N`.

It accepts exactly when the two extents agree.  Consequently a short table
(the materializer would enter its past-end branch) and a long table (an
unvisited suffix would remain) are both rejected.  Acceptance is also proved
equivalent to the materializer emitting exactly the supplied table rather than
a padded prefix.

The input-side layout step which constructs `unaryD table.length` is separate;
no machine-level compiler for that layout is assumed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPTableExtentGate

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSP
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop
open PallLean.Paper93.DeepMath.PathB.MCSPTableCountComparator
open PallLean.Paper93.DeepMath.PathB.MCSPTableMaterializeMachine

/-- The exact-extent decision, implemented by two executions of the verified
finite-control unary comparator. -/
def extentGate (N : ℕ) (table : List Bool) : Bool :=
  counterLE N table.length && counterLE table.length N

theorem extentGate_eq (N : ℕ) (table : List Bool) :
    extentGate N table = decide (table.length = N) := by
  simp only [extentGate, counterLE_eq]
  by_cases h : table.length = N
  · simp [h]
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · simp [show ¬N ≤ table.length by omega, h]
    · simp [show ¬table.length ≤ N by omega, h]

theorem extentGate_true_iff (N : ℕ) (table : List Bool) :
    extentGate N table = true ↔ table.length = N := by
  rw [extentGate_eq]
  simp

theorem extentGate_false_iff (N : ℕ) (table : List Bool) :
    extentGate N table = false ↔ table.length ≠ N := by
  rw [extentGate_eq]
  simp

/-- A short table is precisely the materializer's past-end case, and is
rejected. -/
theorem extentGate_rejects_pastEnd (N : ℕ) (table : List Bool)
    (hshort : table.length < N) :
    extentGate N table = false := by
  rw [extentGate_false_iff]
  omega

/-- A long table leaves an unvisited suffix after `N` rounds, and is rejected. -/
theorem extentGate_rejects_leftover (N : ℕ) (table : List Bool)
    (hlong : N < table.length) :
    extentGate N table = false := by
  rw [extentGate_false_iff]
  omega

theorem bitsUpTo_length (table : List Bool) (N : ℕ) :
    (bitsUpTo table N).length = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      simp only [bitsUpTo, List.length_append, List.length_singleton, ih]

/-- The materialized sequential output is exact exactly when no past-end
padding and no leftover source suffix exists. -/
theorem bitsUpTo_eq_table_iff (table : List Bool) (N : ℕ) :
    bitsUpTo table N = table ↔ table.length = N := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [bitsUpTo_length] at hlen
    exact hlen.symm
  · intro h
    rw [← h]
    exact bitsUpTo_eq_self table

theorem extentGate_iff_materialized_exact (N : ℕ) (table : List Bool) :
    extentGate N table = true ↔ bitsUpTo table N = table := by
  rw [extentGate_true_iff, bitsUpTo_eq_table_iff]

/-- At the MCSP bound, this sound gate is exactly concrete well-formedness. -/
theorem extentGate_twoPow_iff_wellFormed (I : Instance) :
    extentGate (2 ^ I.n) I.table = true ↔ I.WellFormed := by
  exact extentGate_true_iff (2 ^ I.n) I.table

/-- Both load-bearing comparator executions are real finite-control runs and
halt at their explicit clocks. -/
theorem extentGate_forward_halts (N : ℕ) (table : List Bool) :
    HaltsBy compareMachine (unaryD N ++ unaryD table.length)
      (cmpClock N table.length) :=
  counterLE_halts N table.length

theorem extentGate_reverse_halts (N : ℕ) (table : List Bool) :
    HaltsBy compareMachine (unaryD table.length ++ unaryD N)
      (cmpClock table.length N) :=
  counterLE_halts table.length N

/-- Acceptance gives the exact materializer theorem needed by the later
circuit-evaluation phase. -/
theorem materialize_exact_of_extentGate (N : ℕ) (table : List Bool)
    (hgate : extentGate N table = true) :
    run tableMaterializeMachine (ilClock [] N table.length 0)
        (init tableMaterializeMachine (tableMaterializeInput N table)) =
      ⟨(96, ⟨0, Nat.succ_pos _⟩, false),
        2 * N + 2 + 4 * table.length + 1,
        unaryD N ++
          (xVis table 0 ++ (unaryD N ++ encodeD table))⟩ := by
  rw [tableMaterialize_run]
  rw [(extentGate_iff_materialized_exact N table).mp hgate]

end PallLean.Paper93.DeepMath.PathB.MCSPTableExtentGate

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableExtentGate.extentGate_twoPow_iff_wellFormed
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableExtentGate.materialize_exact_of_extentGate
