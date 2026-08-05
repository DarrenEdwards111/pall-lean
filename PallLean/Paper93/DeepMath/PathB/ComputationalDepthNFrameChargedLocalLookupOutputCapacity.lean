import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupReturnBit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitAppendBlock

/-!
# Charged local lookup: reserved doubled-output capacity

A growing doubled output cannot sit immediately before the next lookup
payload: the fresh `01` terminator would overwrite that payload.  This file
introduces a fixed-footprint output region.  `outputCap B out` contains the
ordinary doubled stream followed by enough zero cells for `B - |out|`
further bits.

The main structural theorem proves that the standard four snoc writes consume
exactly one blank pair, advance the doubled terminator, preserve the region's
total length, and leave an arbitrary following payload byte-for-byte intact.
This is the tape contract needed by the truth-bit routing pass.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController

/-- A doubled output with room for `B` total data bits. -/
def outputCap (B : Nat) (out : List Bool) : List Bool :=
  encodeD out ++ List.replicate (2 * (B - out.length)) false

theorem outputCap_length (B : Nat) (out : List Bool)
    (hout : out.length ≤ B) :
    (outputCap B out).length = 2 * B + 2 := by
  simp only [outputCap, List.length_append, encodeD_length,
    List.length_replicate]
  omega

/-- Four writes used by doubled snoc, starting on the old terminator. -/
def writeReturnedBit (T : List Bool) (p : Nat) (b : Bool) : List Bool :=
  writeAt (writeAt (writeAt (writeAt T p b) (p + 1) b)
    (p + 2) false) (p + 3) true

private theorem writeAt_inside_left (A R : List Bool) (p : Nat)
    (w : Bool) (hp : p < A.length) :
    writeAt (A ++ R) p w = writeAt A p w ++ R := by
  rw [writeAt_of_lt w (by simp; omega), writeAt_of_lt w hp,
    List.set_append_left _ _ hp]

private theorem writeAt_inside_right (P X : List Bool) (p : Nat)
    (w : Bool) (hp : p < X.length) :
    writeAt (P ++ X) (P.length + p) w = P ++ writeAt X p w := by
  rw [writeAt_of_lt w (by simp; omega), writeAt_of_lt w hp,
    set_append_left_length]

/-- The four snoc writes consume two reserved zero cells rather than growing
into the following payload. -/
theorem writeReturnedBit_reserved (PRE out R : List Bool) (b : Bool) :
    writeReturnedBit
        (PRE ++ encodeD out ++ false :: false :: R)
        (PRE.length + 2 * out.length) b =
      PRE ++ encodeD (out ++ [b]) ++ R := by
  let A := PRE ++ encodeD out
  let p := PRE.length + 2 * out.length
  let A1 := writeAt A p b
  let A2 := writeAt A1 (p + 1) b
  have hp : p < A.length := by
    simp only [p, A, List.length_append, encodeD_length]
    omega
  have hp1 : p + 1 < A1.length := by
    dsimp only [A1]
    rw [writeAt_of_lt b hp, List.length_set]
    simpa only [A, List.length_append, encodeD_length, p] using
      (show PRE.length + 2 * out.length + 1 <
          PRE.length + (2 * out.length + 2) by omega)
  have e1 : writeAt (A ++ false :: false :: R) p b =
      A1 ++ false :: false :: R := by
    exact writeAt_inside_left A _ p b hp
  have e2 : writeAt (A1 ++ false :: false :: R) (p + 1) b =
      A2 ++ false :: false :: R := by
    exact writeAt_inside_left A1 _ (p + 1) b hp1
  have hA2 : A2.length = p + 2 := by
    calc
      A2.length = A1.length := by
        dsimp only [A2]
        rw [writeAt_of_lt b hp1, List.length_set]
      _ = A.length := by
        dsimp only [A1]
        rw [writeAt_of_lt b hp, List.length_set]
      _ = p + 2 := by
        simp only [A, p, List.length_append, encodeD_length]
        omega
  have e3 : writeAt (A2 ++ false :: false :: R) (p + 2) false =
      A2 ++ false :: false :: R := by
    rw [show p + 2 = A2.length + 0 by omega,
      writeAt_inside_right A2 (false :: false :: R) 0 false (by simp)]
    simp [writeAt]
  have e4 : writeAt (A2 ++ false :: false :: R) (p + 3) true =
      A2 ++ false :: true :: R := by
    rw [show p + 3 = A2.length + 1 by omega,
      writeAt_inside_right A2 (false :: false :: R) 1 true (by simp)]
    simp [writeAt, List.set]
  have hcore : A2 ++ [false, true] = PRE ++ encodeD (out ++ [b]) := by
    have hsn := writes_snoc PRE out PRE.length rfl b
    change writeReturnedBit A p b = PRE ++ encodeD (out ++ [b]) at hsn
    have hA : A.length = p + 2 := by
      simp only [A, p, List.length_append, encodeD_length]
      omega
    have ha1 : writeAt A p b = A1 := rfl
    have ha2 : writeAt A1 (p + 1) b = A2 := rfl
    rw [writeReturnedBit, ha1, ha2,
      show p + 2 = A2.length by omega, writeAt_append_end,
      show p + 3 = (A2 ++ [false]).length by simp [hA2],
      writeAt_append_end] at hsn
    simpa [List.append_assoc] using hsn
  change writeReturnedBit (A ++ false :: false :: R) p b = _
  rw [writeReturnedBit, e1, e2, e3, e4]
  simpa [A, List.append_assoc] using congrArg (fun X => X ++ R) hcore

/-- Appending one returned bit advances a fixed-capacity output region while
preserving every following payload cell. -/
theorem outputCap_snoc (B : Nat) (out payload PRE : List Bool) (b : Bool)
    (hout : out.length < B) :
    writeReturnedBit
        (PRE ++ outputCap B out ++ payload)
        (PRE.length + 2 * out.length) b =
      PRE ++ outputCap B (out ++ [b]) ++ payload := by
  have hsplit : 2 * (B - out.length) =
      2 + 2 * (B - (out.length + 1)) := by omega
  have hpad : List.replicate (2 * (B - out.length)) false =
      false :: false ::
        List.replicate (2 * (B - (out.length + 1))) false := by
    rw [hsplit, List.replicate_add]
    rfl
  unfold outputCap
  rw [hpad]
  have hwrite := writeReturnedBit_reserved PRE out
    (List.replicate (2 * (B - (out.length + 1))) false ++ payload) b
  simpa only [List.length_append, List.length_singleton,
    List.append_assoc] using hwrite

/-- Capacity remains fixed after one live append. -/
theorem outputCap_snoc_length (B : Nat) (out : List Bool) (b : Bool)
    (hout : out.length < B) :
    (outputCap B (out ++ [b])).length = 2 * B + 2 := by
  apply outputCap_length
  simp only [List.length_append, List.length_singleton]
  omega

/-! ## Alignment with the decoded literal schedule -/

/-- Flat truth values in exactly the order used by the lookup schedule. -/
def scheduledTruths (x w : List Bool) : List Bool :=
  (decodedLiterals x).map
    (evalLit (fun k => w.getD k false))

theorem scheduledTruths_length (x w : List Bool) :
    (scheduledTruths x w).length = (decodedLiterals x).length := by
  simp [scheduledTruths]

theorem scheduledTruths_take_succ (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    (scheduledTruths x w).take (t + 1) =
      (scheduledTruths x w).take t ++
        [evalLit (fun k => w.getD k false) (scheduledLiteral x t)] := by
  rw [take_snoc_getD (scheduledTruths x w) false t (by
    simpa only [scheduledTruths_length] using ht)]
  change _ ++ [((decodedLiterals x).map
      (evalLit (fun k => w.getD k false))).getD t false] =
    _ ++ [evalLit (fun k => w.getD k false)
      ((decodedLiterals x).getD t (0, false))]
  rw [List.getD_eq_getElem _ _ (by simpa using ht),
    List.getD_eq_getElem _ _ ht]
  simp

/-- Round `t` consumes one reserved pair and extends precisely the semantic
truth prefix through literal `t`, preserving an arbitrary later payload. -/
theorem outputCap_scheduled_step (x w payload PRE : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    writeReturnedBit
        (PRE ++ outputCap (decodedLiterals x).length
          ((scheduledTruths x w).take t) ++ payload)
        (PRE.length + 2 * ((scheduledTruths x w).take t).length)
        (evalLit (fun k => w.getD k false) (scheduledLiteral x t)) =
      PRE ++ outputCap (decodedLiterals x).length
        ((scheduledTruths x w).take (t + 1)) ++ payload := by
  have hlen : ((scheduledTruths x w).take t).length = t := by
    rw [List.length_take, scheduledTruths_length, Nat.min_eq_left (by omega)]
  have h := outputCap_snoc (decodedLiterals x).length
    ((scheduledTruths x w).take t) payload PRE
    (evalLit (fun k => w.getD k false) (scheduledLiteral x t)) (by
      rw [hlen]
      exact ht)
  rw [← scheduledTruths_take_succ x w ht] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity.outputCap_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity.writeReturnedBit_reserved
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity.outputCap_snoc
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity.outputCap_snoc_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity.scheduledTruths_take_succ
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity.outputCap_scheduled_step
