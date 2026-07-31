import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPTableCountTrackMachine

/-!
# MCSP verifier: comparator-ready counter layout

This file fixes the exact four-counter interface consumed by the two
destructive extent comparisons:

    tableLength, twoPow, twoPow, tableLength, payload.

The first pair decides `table.length ≤ 2^n`; the second decides
`2^n ≤ table.length`.  Their conjunction is proved equivalent to concrete
MCSP well-formedness.  Exact `take`/`drop` theorems ensure later head-routing
code cannot silently compare the wrong adjacent blocks.

The table-length blocks are supplied by
`MCSPTableCountTrackMachine`; this file specifies and verifies the destination
layout.  A single finite-control head-routing sequencer joining two count-track
runs remains a separate operational theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ConcreteMCSP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.MCSPTableCountComparator

def comparatorLayout (n : ℕ) (table payload : List Bool) : List Bool :=
  unaryD table.length ++
    (unaryD (2 ^ n) ++
      (unaryD (2 ^ n) ++
        (unaryD table.length ++ payload)))

def reverseTape (n : ℕ) (table : List Bool) : List Bool :=
  unaryD table.length ++ unaryD (2 ^ n)

def forwardTape (n : ℕ) (table : List Bool) : List Bool :=
  unaryD (2 ^ n) ++ unaryD table.length

private theorem take_two_blocks (a b rest : List Bool) :
    (a ++ b ++ rest).take (a.length + b.length) = a ++ b := by
  rw [← List.length_append]
  simpa [List.append_assoc] using
    (@List.take_left Bool (a ++ b) rest)

theorem comparatorLayout_reverse_prefix (n : ℕ)
    (table payload : List Bool) :
    (comparatorLayout n table payload).take
        ((unaryD table.length).length + (unaryD (2 ^ n)).length) =
      reverseTape n table := by
  simpa [comparatorLayout, reverseTape, List.append_assoc] using
    take_two_blocks (unaryD table.length) (unaryD (2 ^ n))
      (unaryD (2 ^ n) ++ unaryD table.length ++ payload)

theorem comparatorLayout_after_reverse (n : ℕ)
    (table payload : List Bool) :
    (comparatorLayout n table payload).drop
        ((unaryD table.length).length + (unaryD (2 ^ n)).length) =
      forwardTape n table ++ payload := by
  simp [comparatorLayout, forwardTape]

theorem comparatorLayout_forward_window (n : ℕ)
    (table payload : List Bool) :
    ((comparatorLayout n table payload).drop
        ((unaryD table.length).length + (unaryD (2 ^ n)).length)).take
          ((unaryD (2 ^ n)).length + (unaryD table.length).length) =
      forwardTape n table := by
  rw [comparatorLayout_after_reverse]
  simpa [forwardTape, List.append_assoc] using
    take_two_blocks (unaryD (2 ^ n)) (unaryD table.length) payload

/-- The two decisions are executions of the repository's verified
finite-control unary comparator. -/
def routedExtentDecision (n : ℕ) (table : List Bool) : Bool :=
  decideOut compareMachine (reverseTape n table)
      (cmpClock table.length (2 ^ n)) &&
    decideOut compareMachine (forwardTape n table)
      (cmpClock (2 ^ n) table.length)

theorem routedExtentDecision_eq (n : ℕ) (table : List Bool) :
    routedExtentDecision n table =
      (decide (table.length ≤ 2 ^ n) &&
        decide (2 ^ n ≤ table.length)) := by
  unfold routedExtentDecision decideOut
  simp only [reverseTape, forwardTape]
  rw [compare_decides, compare_decides]

theorem routedExtentDecision_true_iff (n : ℕ) (table : List Bool) :
    routedExtentDecision n table = true ↔ table.length = 2 ^ n := by
  rw [routedExtentDecision_eq]
  constructor
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · intro h
    simp [h]

theorem routedExtentDecision_iff_wellFormed (I : Instance) :
    routedExtentDecision I.n I.table = true ↔ I.WellFormed :=
  routedExtentDecision_true_iff I.n I.table

theorem reverse_routed_halts (n : ℕ) (table : List Bool) :
    HaltsBy compareMachine (reverseTape n table)
      (cmpClock table.length (2 ^ n)) := by
  exact counterLE_halts table.length (2 ^ n)

theorem forward_routed_halts (n : ℕ) (table : List Bool) :
    HaltsBy compareMachine (forwardTape n table)
      (cmpClock (2 ^ n) table.length) := by
  exact counterLE_halts (2 ^ n) table.length

theorem comparatorLayout_length (n : ℕ) (table payload : List Bool) :
    (comparatorLayout n table payload).length =
      4 * table.length + 4 * (2 ^ n) + 8 + payload.length := by
  simp [comparatorLayout, unaryD_length]
  omega

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout.routedExtentDecision_iff_wellFormed
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout.reverse_routed_halts
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout.forward_routed_halts
