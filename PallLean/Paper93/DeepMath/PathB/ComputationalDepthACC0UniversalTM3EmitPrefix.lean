import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteFieldBit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteEncode

/-!
# Entry 425 — universal-TM-table build: the field-then-bit machine emits the encoded prefix `writeFieldBit3_emits` (proved)

The field-then-bit emitter (entry 423) lays down a `writeFieldBlock` then a symbol cell; this brick proves that what it
emits is *exactly* the encoded prefix `encodeNatBits3 n ++ w :: rest` — the shape of a transition/config prefix
(`encodeTransBits3` entry 393, `configEncode3` entry 413).  It combines the emitter's run (423) with the
writer-emits-the-encoding correctness (entry 424) plus the boundary write that lays the symbol cell.

## What is proved (clean axioms, no `sorry`)

* **`writeFieldBit3_emits`** (PROVED) — `n+1 < X.length ⇒ ∃ N, reachIn N (s, pre.length, pre ++ X) (sOut, pre.length+n+1,
  pre ++ encodeNatBits3 n ++ w :: X.drop (n+2))`: running the field-then-bit emitter lays the encoded prefix
  `encodeNatBits3 n ++ [w]` over the next `n+2` cells, prefix and tail intact.

## Honest scope

This is the **emit-the-encoded-prefix** correctness.  It does **not** yet emit a full encoded configuration (a second field
for the next state, etc.), nor assemble `EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitPrefix

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3 encodeNatBits3_length)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteFieldBit (writeFieldBit3 writeFieldBit3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteEncode (writeFieldBlock_eq_encode)

/-- An in-bounds write is a `List.set`. -/
private theorem writeAt3_eq_set (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    writeAt3 tp p w = tp.set p w := by
  unfold writeAt3
  rw [show p + 1 - tp.length = 0 from by omega, List.replicate_zero, List.append_nil]

/-- Setting the cell just past a prefix replaces the head of the suffix. -/
private theorem set_at_boundary (A l : List Sym3) (x y : Sym3) :
    (A ++ (x :: l)).set A.length y = A ++ (y :: l) := by
  induction A with
  | nil => rfl
  | cons a A ih =>
      show a :: ((A ++ (x :: l)).set A.length y) = a :: (A ++ (y :: l))
      rw [ih]

/-- Writing at the cell just past a prefix replaces the head of the suffix. -/
private theorem writeAt3_cons_boundary (A l : List Sym3) (x w : Sym3) :
    writeAt3 (A ++ (x :: l)) A.length w = A ++ (w :: l) := by
  rw [writeAt3_eq_set _ _ _ (by simp only [List.length_append, List.length_cons]; omega), set_at_boundary]

/-- **The field-then-bit machine emits the encoded prefix (PROVED).**  Lays `encodeNatBits3 n ++ [w]` at `pre.length`. -/
theorem writeFieldBit3_emits (s sOut n : ℕ) (w : Sym3) (pre X : List Sym3) (hX : n + 1 < X.length) :
    ∃ N, reachIn (toNTM3 (writeFieldBit3 s sOut n w)) N (s, pre.length, pre ++ X)
      (sOut, pre.length + n + 1, pre ++ encodeNatBits3 n ++ w :: X.drop (n + 2)) := by
  obtain ⟨N, h⟩ := writeFieldBit3_run s sOut n pre.length w (pre ++ X) (by simp only [List.length_append]; omega)
  rw [writeFieldBlock_eq_encode pre X n (by omega), List.drop_eq_getElem_cons (show n + 1 < X.length from hX)] at h
  have hidx : pre.length + n + 1 = (pre ++ encodeNatBits3 n).length := by
    rw [List.length_append, encodeNatBits3_length]; omega
  rw [hidx, writeAt3_cons_boundary, ← hidx] at h
  exact ⟨N, h⟩

/-!
**The field-then-bit machine emits the encoded prefix, proved.**  `writeFieldBit3_emits` shows the emitter's output is
exactly the encoded prefix `encodeNatBits3 n ++ w :: rest`.  Next: emit the remaining fields to build a full encoded
configuration, and assemble `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitPrefix

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitPrefix.writeFieldBit3_emits
