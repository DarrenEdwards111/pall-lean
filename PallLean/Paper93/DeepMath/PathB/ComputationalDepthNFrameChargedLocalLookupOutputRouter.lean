import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupOutputCapacity

/-!
# Charged local lookup: route one returned bit into reserved output

The repository's verified `appendMachine [bv]` is lifted from a terminal
doubled stream to the capacity-padded verifier layout.  It scans only the live
output pairs, detects their current `01` terminator, consumes one reserved
blank pair, writes the returned bit twice, installs the next terminator, and
halts without touching an arbitrary following lookup payload.

This supplies the two finite routing branches (`bv = false` and `bv = true`)
needed after lookup return.  A later dynamic handoff chooses the branch from
the accepting bit retained by `returnBitMachine`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAppendBlock
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity

/-! ## Capacity-padded scan facts -/

theorem outputCap_payload_data_eq (B : Nat) (out payload : List Bool)
    {i : Nat} (hi : i < out.length) :
    (outputCap B out ++ payload).getD (2 * i) false =
      (outputCap B out ++ payload).getD (2 * i + 1) false := by
  unfold outputCap
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [encodeD_length]; omega),
    List.getD_append (h := by rw [encodeD_length]; omega),
    encodeD_lo out i hi, encodeD_hi out i hi]

theorem outputCap_payload_mark_lo (B : Nat) (out payload : List Bool) :
    (outputCap B out ++ payload).getD (2 * out.length) false = false := by
  unfold outputCap
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [encodeD_length]; omega),
    encodeD_mark_lo]

theorem outputCap_payload_mark_hi (B : Nat) (out payload : List Bool) :
    (outputCap B out ++ payload).getD (2 * out.length + 1) false = true := by
  unfold outputCap
  simp only [List.append_assoc]
  rw [List.getD_append (h := by rw [encodeD_length]; omega),
    encodeD_mark_hi]

/-! ## Exact one-bit routing execution -/

/-- Exact clock for scanning `out` and performing the four reserved writes. -/
def outputRouteClock (out : List Bool) : Nat := 2 * out.length + 6

/-- A one-bit append runs unchanged on a capacity-padded output followed by
an arbitrary payload. -/
theorem outputRouter_run (bv : Bool) (B : Nat) (out payload : List Bool)
    (hout : out.length < B) :
    run (appendMachine [bv]) (outputRouteClock out)
        (init (appendMachine [bv]) (outputCap B out ++ payload)) =
      ⟨(6, ⟨0, by omega⟩, false),
        2 * out.length + 3,
        outputCap B (out ++ [bv]) ++ payload⟩ := by
  let T := outputCap B out ++ payload
  let idx : Fin ([bv].length + 1) := ⟨0, by simp⟩
  have hscan := run_scan [bv] T 0 idx false out.length
    (fun i hi => by
      simpa only [Nat.zero_add] using
        outputCap_payload_data_eq B out payload hi)
  have hdetect := run_two_detect (bits := [bv]) (idx := idx)
    (s := storedD T 0 false out.length)
    (outputCap_payload_mark_lo B out payload)
    (outputCap_payload_mark_hi B out payload)
  have hlast := run_four_last (bits := [bv]) (idx := idx)
    (s := false) (T := T) (p := 2 * out.length) (by simp [idx])
  have hwrite : writeReturnedBit T (2 * out.length) bv =
      outputCap B (out ++ [bv]) ++ payload := by
    dsimp only [T]
    simpa using outputCap_snoc B out payload [] bv hout
  change run (appendMachine [bv]) (2 * out.length + 6)
      ⟨(0, idx, false), 0, T⟩ = _
  rw [show 2 * out.length + 6 = 2 * out.length + (2 + 4) by omega,
    run_add, hscan, Nat.zero_add, run_add, hdetect, hlast]
  simp only [idx, List.getD_cons_zero]
  rw [show writeAt
      (writeAt (writeAt (writeAt T (2 * out.length) bv)
        (2 * out.length + 1) bv) (2 * out.length + 2) false)
        (2 * out.length + 3) true =
      writeReturnedBit T (2 * out.length) bv from rfl,
    hwrite]

theorem outputRouter_halts (bv : Bool) (B : Nat) (out payload : List Bool)
    (hout : out.length < B) :
    HaltsBy (appendMachine [bv]) (outputCap B out ++ payload)
      (outputRouteClock out) := by
  change (appendMachine [bv]).halt
    (run (appendMachine [bv]) (outputRouteClock out)
      (init (appendMachine [bv]) (outputCap B out ++ payload))).st = true
  rw [outputRouter_run bv B out payload hout]
  rfl

theorem outputRouteClock_le (B : Nat) (out : List Bool)
    (hout : out.length ≤ B) :
    outputRouteClock out ≤ 2 * B + 6 := by
  simp only [outputRouteClock]
  omega

/-! ## Scheduled semantic specialization -/

theorem scheduledOutputRouter_run (x w payload : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let out := (scheduledTruths x w).take t
    let bv := evalLit (fun k => w.getD k false) (scheduledLiteral x t)
    run (appendMachine [bv]) (outputRouteClock out)
        (init (appendMachine [bv])
          (outputCap (decodedLiterals x).length out ++ payload)) =
      ⟨(6, ⟨0, by omega⟩, false),
        2 * out.length + 3,
        outputCap (decodedLiterals x).length
          ((scheduledTruths x w).take (t + 1)) ++ payload⟩ := by
  dsimp only
  have hlen : ((scheduledTruths x w).take t).length = t := by
    rw [List.length_take, scheduledTruths_length, Nat.min_eq_left (by omega)]
  have h := outputRouter_run
    (evalLit (fun k => w.getD k false) (scheduledLiteral x t))
    (decodedLiterals x).length ((scheduledTruths x w).take t) payload
    (by rw [hlen]; exact ht)
  rw [← scheduledTruths_take_succ x w ht] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter.outputRouter_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter.outputRouter_halts
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter.outputRouteClock_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter.scheduledOutputRouter_run
