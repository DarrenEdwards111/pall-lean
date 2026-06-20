import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteField
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Move

/-!
# Entry 423 — universal-TM-table build: the field-then-bit emitter `writeFieldBit3` (proved)

Emitting encoded structures (toward `EmitsEncodedStep3`) means laying down consecutive encoded fields.  The basic unit is
a **unary field followed by a single symbol cell** — `encodeNatBits3 n ++ [w]` — which is exactly the shape of a
transition/config prefix (a state field then its read symbol, cf. `encodeTransBits3` entry 393, `configEncode3` entry 413).

This brick is that emitter: write the unary field (`writeUnaryFieldN3`, entry 422), step past its separator, and write the
symbol bit.  It is the first *composition* on the output side, chaining the field writer with a bit write so the head
flows naturally from one field to the next.

## What is proved (clean axioms, no `sorry`)

* **`writeFieldBlock_length`** (PROVED) — `j+n < tp.length ⇒ (writeFieldBlock tp j n).length = tp.length` (the field writer
  stays in bounds).
* **`writeFieldBit3 s sOut n w`** — `writeUnaryFieldN3 s (s+n+1) n ++ moveRight3 (s+n+1) (s+n+2) ++ unmark3 (s+n+2) sOut w`.
* **`writeFieldBit3_run`** (PROVED) — `j+n < tp.length ⇒ ∃ N, reachIn N (s, j, tp) (sOut, j+n+1, writeAt3 (writeFieldBlock
  tp j n) (j+n+1) w)`: lays down `encodeNatBits3 n` at `j` then the symbol `w` at `j+n+1`, head on the symbol cell.

## Honest scope

This is the **field-then-bit emitter** — an output composition for encoded structures.  It does **not** yet emit a full
encoded configuration, nor assemble `EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteFieldBit

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteField (writeUnaryFieldN3 writeUnaryFieldN3_run writeFieldBlock)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- Length is preserved by an in-bounds write. -/
private theorem writeAt3_length_eq (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    (writeAt3 tp p w).length = tp.length := by
  simp only [writeAt3, List.length_set, List.length_append, List.length_replicate]
  omega

/-- **The field writer stays in bounds (PROVED).**  `j+n < tp.length ⇒ length preserved`. -/
theorem writeFieldBlock_length (n j : ℕ) (tp : List Sym3) (h : j + n < tp.length) :
    (writeFieldBlock tp j n).length = tp.length := by
  induction n generalizing j tp with
  | zero => exact writeAt3_length_eq tp j Sym3.O (by omega)
  | succ n ih =>
      have hlen : (writeAt3 tp j Sym3.I).length = tp.length := writeAt3_length_eq tp j Sym3.I (by omega)
      have := ih (j + 1) (writeAt3 tp j Sym3.I) (by rw [hlen]; omega)
      rw [show writeFieldBlock tp j (n + 1) = writeFieldBlock (writeAt3 tp j Sym3.I) (j + 1) n from rfl, this, hlen]

/-- **The field-then-bit emitter.**  Write the unary field, step past its separator, write the symbol. -/
def writeFieldBit3 (s sOut n : ℕ) (w : Sym3) : TMachine3 :=
  writeUnaryFieldN3 s (s + n + 1) n ++ moveRight3 (s + n + 1) (s + n + 2) ++ unmark3 (s + n + 2) sOut w

/-- **The field-then-bit emit run (PROVED).**  Lays down `encodeNatBits3 n` at `j` and the symbol `w` at `j+n+1`. -/
theorem writeFieldBit3_run (s sOut n j : ℕ) (w : Sym3) (tp : List Sym3) (h : j + n < tp.length) :
    ∃ N, reachIn (toNTM3 (writeFieldBit3 s sOut n w)) N (s, j, tp)
      (sOut, j + n + 1, writeAt3 (writeFieldBlock tp j n) (j + n + 1) w) := by
  obtain ⟨N1, hw⟩ := writeUnaryFieldN3_run (s + n + 1) n s j tp
  have hlen : (writeFieldBlock tp j n).length = tp.length := writeFieldBlock_length n j tp h
  have hmr := moveRight3_run_eq (s + n + 1) (s + n + 2) (j + n) (writeFieldBlock tp j n) (by rw [hlen]; omega)
  have hun := unmark3_run (s + n + 2) sOut w (j + n + 1) (writeFieldBlock tp j n)
  have s1 := reachIn_seq3 (writeUnaryFieldN3 s (s + n + 1) n) (moveRight3 (s + n + 1) (s + n + 2)) N1 1 _ _ _ hw hmr
  exact ⟨N1 + 1 + 1, reachIn_seq3 (writeUnaryFieldN3 s (s + n + 1) n ++ moveRight3 (s + n + 1) (s + n + 2))
    (unmark3 (s + n + 2) sOut w) (N1 + 1) 1 _ _ _ s1 hun⟩

/-!
**The field-then-bit emitter, proved.**  `writeFieldBit3` lays down a unary field followed by a symbol — the basic encoded
prefix unit — composing the field writer with a bit write.  Next: chain these to emit a full encoded configuration, and
assemble `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteFieldBit

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteFieldBit.writeFieldBit3_run
