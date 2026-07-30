import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPTwoPowFinalizeMachine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPDoubledCodec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCounterCompare
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCounterCopy

/-!
# MCSP verifier: exact table-count comparison

This file connects the finalized `unaryD (2^n)` counter to the repository's
verified destructive unary comparator.

Equality is checked by two directed comparisons on preserved copies:

* `2^n ≤ table.length`;
* `table.length ≤ 2^n`.

The Boolean conjunction is proved equivalent to
`Instance.WellFormed`.  The copy machine theorems expose two exact adjacent
copies of each counter before destructive comparison, and all component clocks
retain explicit quadratic bounds.

The next operational connector must emit `unaryD table.length` while scanning
the self-delimiting table and arrange these copied counter tapes inside the
integrated verifier.  No such connector is assumed here.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPTableCountComparator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy

/-- Execute the verified comparator on two standard unary counters. -/
def counterLE (a b : ℕ) : Bool :=
  decideOut compareMachine (unaryD a ++ unaryD b) (cmpClock a b)

@[simp] theorem counterLE_eq (a b : ℕ) :
    counterLE a b = decide (a ≤ b) := by
  exact compare_decides a b

theorem counterLE_halts (a b : ℕ) :
    HaltsBy compareMachine (unaryD a ++ unaryD b) (cmpClock a b) := by
  exact compare_halts a b

/-- The two directed comparisons which certify the exact MCSP table extent. -/
def tableCountOK (n : ℕ) (table : List Bool) : Bool :=
  counterLE (2 ^ n) table.length &&
    counterLE table.length (2 ^ n)

theorem tableCountOK_eq (n : ℕ) (table : List Bool) :
    tableCountOK n table = decide (table.length = 2 ^ n) := by
  simp only [tableCountOK, counterLE_eq]
  by_cases h : table.length = 2 ^ n
  · rw [h]
    simp
  · have hor : table.length < 2 ^ n ∨ 2 ^ n < table.length :=
      lt_or_gt_of_ne h
    rcases hor with hlt | hgt
    · simp [show ¬2 ^ n ≤ table.length by omega, h]
    · simp [show ¬table.length ≤ 2 ^ n by omega, h]

theorem tableCountOK_true_iff (n : ℕ) (table : List Bool) :
    tableCountOK n table = true ↔ table.length = 2 ^ n := by
  rw [tableCountOK_eq]
  simp

/-- Exact count checking is exactly the concrete MCSP well-formedness
condition. -/
theorem tableCountOK_iff_wellFormed (I : Instance) :
    tableCountOK I.n I.table = true ↔ I.WellFormed := by
  exact tableCountOK_true_iff I.n I.table

/-! ## Preserved copies for the destructive comparisons -/

/-- The already-generated `2^n` counter can be copied without loss. -/
theorem copy_twoPow_counter (n : ℕ) :
    run copyMachine (cpyClock (2 ^ n))
      (init copyMachine (unaryD (2 ^ n))) =
      ⟨(10, false), 4 * (2 ^ n) + 3,
        unaryD (2 ^ n) ++ unaryD (2 ^ n)⟩ :=
  copy_run (2 ^ n)

/-- The table-length counter can likewise be copied without loss. -/
theorem copy_tableLength_counter (table : List Bool) :
    run copyMachine (cpyClock table.length)
      (init copyMachine (unaryD table.length)) =
      ⟨(10, false), 4 * table.length + 3,
        unaryD table.length ++ unaryD table.length⟩ :=
  copy_run table.length

theorem copy_twoPow_halts (n : ℕ) :
    HaltsBy copyMachine (unaryD (2 ^ n)) (cpyClock (2 ^ n)) :=
  copy_halted (2 ^ n)

theorem copy_tableLength_halts (table : List Bool) :
    HaltsBy copyMachine (unaryD table.length) (cpyClock table.length) :=
  copy_halted table.length

/-- Both comparison clocks have the repository's explicit quadratic bound. -/
theorem forward_compare_clock_le (n : ℕ) (table : List Bool) :
    cmpClock (2 ^ n) table.length ≤
      3 * (2 ^ n + table.length + 2) *
        (2 ^ n + table.length + 2) :=
  cmpClock_le (2 ^ n) table.length

theorem reverse_compare_clock_le (n : ℕ) (table : List Bool) :
    cmpClock table.length (2 ^ n) ≤
      3 * (table.length + 2 ^ n + 2) *
        (table.length + 2 ^ n + 2) :=
  cmpClock_le table.length (2 ^ n)

end PallLean.Paper93.DeepMath.PathB.MCSPTableCountComparator

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableCountComparator.tableCountOK_iff_wellFormed
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableCountComparator.copy_twoPow_counter
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPTableCountComparator.copy_tableLength_counter
