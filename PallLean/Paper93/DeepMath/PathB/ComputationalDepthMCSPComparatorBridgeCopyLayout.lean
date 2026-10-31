import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPCounterLocalCopyFinish
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPComparatorReadyLayout

/-!
# MCSP verifier: bridge-copy layout for physical comparator staging

Two adjacent copies have order `table,table,pow,pow`, not the comparator's
required `table,pow,pow,table`.  Swapping variable-length blocks in place is
unnecessary.  The unary copy controller already seeks across any doubled pair
whose high cell is true.  Therefore the sound physical layout is to place the
two finalized power counters between the table source and its reserved target
scratch, then copy the table counter *across* that bridge.

This file defines the evolving round and restore tapes for that operation and
proves all structural writes.  The final terminator write is definitionally
the existing four-counter comparator layout.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCompare
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterCopy
open PallLean.Paper93.DeepMath.PathB.MCSPComparatorReadyLayout

/-- The two already finalized power counters crossed by the table copy. -/
def powBridge (n : ℕ) : List Bool :=
  unaryD (2 ^ n) ++ unaryD (2 ^ n)

theorem powBridge_length (n : ℕ) :
    (powBridge n).length = 4 * (2 ^ n) + 4 := by
  simp [powBridge, unaryD_length]
  omega

/-- Every doubled pair of the power bridge has true high cell, including the
`01` marker of each constituent counter. -/
theorem powBridge_getD_high (n i : ℕ)
    (hi : i < 2 * ((2 ^ n) + 1)) :
    (powBridge n).getD (2 * i + 1) false = true := by
  by_cases hfirst : i < 2 ^ n + 1
  · rw [powBridge, List.getD_append (h := by
      rw [unaryD_length]
      omega)]
    by_cases hdata : i < 2 ^ n
    · exact unaryD_getD_data (2 ^ n) (2 * i + 1) (by omega)
    · rw [show i = 2 ^ n by omega]
      exact unaryD_getD_markHi (2 ^ n)
  · rw [powBridge,
      List.getD_append_right (h := by rw [unaryD_length]; omega),
      unaryD_length]
    have hi' : i - (2 ^ n + 1) ≤ 2 ^ n := by omega
    by_cases hdata : i - (2 ^ n + 1) < 2 ^ n
    · rw [show 2 * i + 1 - (2 * 2 ^ n + 2) =
          2 * (i - (2 ^ n + 1)) + 1 by omega]
      exact unaryD_getD_data (2 ^ n)
        (2 * (i - (2 ^ n + 1)) + 1) (by omega)
    · rw [show 2 * i + 1 - (2 * 2 ^ n + 2) = 2 * (2 ^ n) + 1 by omega]
      exact unaryD_getD_markHi (2 ^ n)

/-- Copy-round tape with the power bridge between table source and target. -/
def bridgeCpyS (n a jA jC : ℕ) (suffix : List Bool) : List Bool :=
  markedD jA ++
    (List.replicate (2 * (a - jA)) true ++
      ([false, true] ++
        (powBridge n ++
          (List.replicate (2 * jC) true ++
            (List.replicate (2 * (a - jC) + 2) false ++ suffix)))))

theorem bridgeCpyS_zero (n a : ℕ) (suffix : List Bool) :
    bridgeCpyS n a 0 0 suffix =
      unaryD a ++ powBridge n ++
        List.replicate (2 * a + 2) false ++ suffix := by
  simp [bridgeCpyS, markedD, unaryD_eq, List.append_assoc]

theorem bridgeCpyS_length (n a jA jC : ℕ) (suffix : List Bool)
    (hA : jA ≤ a) (hC : jC ≤ a) :
    (bridgeCpyS n a jA jC suffix).length =
      4 * a + 4 * (2 ^ n) + 8 + suffix.length := by
  simp [bridgeCpyS, markedD_length, powBridge_length]
  omega

/-- Mark the next table-source `11` pair as processed. -/
theorem bridgeCpyS_mark (n a j : ℕ) (suffix : List Bool)
    (hj : j < a) :
    writeAt (bridgeCpyS n a j j suffix) (2 * j + 1) false =
      bridgeCpyS n a (j + 1) j suffix := by
  rw [writeAt_of_lt false (by
      rw [bridgeCpyS_length n a j j suffix (by omega) (by omega)]
      omega),
    bridgeCpyS,
    set_append_left_length' _ _ (markedD_length j),
    show 2 * (a - j) = 2 * (a - j - 1) + 1 + 1 by omega,
    List.replicate_succ, List.replicate_succ]
  simp only [List.cons_append, List.nil_append,
    List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc, markedD_snoc,
    show a - j - 1 = a - (j + 1) by omega]
  rw [show 2 * (a - (j + 1)) + 1 + 1 + 2 =
      2 * (a - j) + 2 by omega]
  rfl

/-- Append one copied table pair after the complete power bridge. -/
theorem bridgeCpyS_grow (n a j : ℕ) (suffix : List Bool)
    (hj : j < a) :
    let p := 2 * a + 2 + (powBridge n).length + 2 * j
    writeAt (writeAt (bridgeCpyS n a (j + 1) j suffix) p true)
      (p + 1) true = bridgeCpyS n a (j + 1) (j + 1) suffix := by
  intro p
  let A := markedD (j + 1) ++
    (List.replicate (2 * (a - (j + 1))) true ++
      ([false, true] ++ (powBridge n ++ List.replicate (2 * j) true)))
  let tail := List.replicate (2 * (a - (j + 1)) + 2) false ++ suffix
  have hlen : A.length = p := by
    simp [A, p, markedD_length, powBridge_length]
    omega
  have hshape : bridgeCpyS n a (j + 1) j suffix =
      A ++ false :: false :: tail := by
    simp only [bridgeCpyS, A, tail]
    rw [show 2 * (a - j) + 2 =
      2 + (2 * (a - (j + 1)) + 2) by omega,
      List.replicate_add]
    simp [List.append_assoc]
  rw [hshape, ← hlen]
  rw [PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  rw [show A ++ true :: false :: tail =
      (A ++ [true]) ++ false :: tail by simp,
    show A.length + 1 = (A ++ [true]).length by simp,
    PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  simp [bridgeCpyS, A, tail, List.append_assoc,
    show 2 * (j + 1) = 2 * j + 2 by omega, List.replicate_add]

/-- Restore tape: the bridge and copied target are already complete. -/
def bridgeResS (n a i : ℕ) (suffix : List Bool) : List Bool :=
  List.replicate (2 * i) true ++
    (markedD (a - i) ++
      ([false, true] ++
        (powBridge n ++
          (List.replicate (2 * a) true ++ ([false, false] ++ suffix)))))

theorem bridgeResS_zero (n a : ℕ) (suffix : List Bool) :
    bridgeResS n a 0 suffix = bridgeCpyS n a a a suffix := by
  simp [bridgeResS, bridgeCpyS]

theorem bridgeResS_length (n a i : ℕ) (suffix : List Bool)
    (hi : i ≤ a) :
    (bridgeResS n a i suffix).length =
      4 * a + 4 * (2 ^ n) + 8 + suffix.length := by
  simp [bridgeResS, markedD_length, powBridge_length]
  omega

/-- Heal one processed table-source pair; bridge and target are untouched. -/
theorem bridgeResS_heal (n a i : ℕ) (suffix : List Bool)
    (hi : i < a) :
    writeAt (bridgeResS n a i suffix) (2 * i + 1) true =
      bridgeResS n a (i + 1) suffix := by
  rw [writeAt_of_lt true (by
      rw [bridgeResS_length n a i suffix (by omega)]
      omega),
    bridgeResS,
    set_append_left_length' _ _ List.length_replicate,
    show a - i = (a - i - 1) + 1 by omega]
  simp only [markedD, List.cons_append, List.nil_append,
    List.set_cons_succ, List.set_cons_zero]
  rw [cons_cons_append, ← List.append_assoc,
    show ([true, true] : List Bool) = List.replicate 2 true from rfl,
    ← List.replicate_add,
    show 2 * i + 2 = 2 * (i + 1) by ring,
    show a - i - 1 = a - (i + 1) by omega]
  rfl

/-- The final high-cell write creates the copied table marker after the power
bridge, yielding the required physical order. -/
theorem bridgeResS_finish (n a : ℕ) (suffix : List Bool) :
    let p := 4 * a + 4 * (2 ^ n) + 7
    writeAt (bridgeResS n a a suffix) p true =
      unaryD a ++ powBridge n ++ unaryD a ++ suffix := by
  intro p
  unfold bridgeResS
  simp only [Nat.sub_self]
  have hp : p =
      (List.replicate (2 * a) true ++
        ([false, true] ++
          (powBridge n ++ (List.replicate (2 * a) true ++ [false])))).length := by
    simp [p, powBridge_length]
    omega
  rw [hp]
  rw [show
      List.replicate (2 * a) true ++
          (markedD 0 ++
            ([false, true] ++
              (powBridge n ++
                (List.replicate (2 * a) true ++ ([false, false] ++ suffix))))) =
        (List.replicate (2 * a) true ++
          ([false, true] ++
            (powBridge n ++ (List.replicate (2 * a) true ++ [false])))) ++
          false :: suffix by simp [markedD, List.append_assoc]]
  rw [PallLean.Paper93.DeepMath.PathB.DIndexMachine.writeAt_boundary]
  simp [unaryD_eq, List.append_assoc, powBridge]

/-- The bridge-copy output is exactly the already verified comparator layout. -/
theorem bridge_output_eq_comparatorLayout (n : ℕ)
    (table payload : List Bool) :
    unaryD table.length ++ powBridge n ++
        unaryD table.length ++ payload =
      comparatorLayout n table payload := by
  simp [powBridge, comparatorLayout, List.append_assoc]

theorem bridgeResS_finish_comparatorLayout (n : ℕ)
    (table payload : List Bool) :
    writeAt (bridgeResS n table.length table.length payload)
        (4 * table.length + 4 * (2 ^ n) + 7) true =
      comparatorLayout n table payload := by
  rw [bridgeResS_finish,
    bridge_output_eq_comparatorLayout]

end PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout.powBridge_getD_high
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout.bridgeCpyS_mark
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout.bridgeCpyS_grow
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout.bridgeResS_heal
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPComparatorBridgeCopyLayout.bridgeResS_finish_comparatorLayout
