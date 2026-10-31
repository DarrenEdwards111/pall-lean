import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EmitPrefix
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Config

/-!
# Entry 426 — universal-TM-table build: the emitter emits a configuration `writeFieldBit3_emits_config` (proved)

Entry 425 showed the field-then-bit emitter lays down `encodeNatBits3 n ++ w :: rest`.  This brick identifies that output
with the **configuration encoding** `configEncode3` (entry 413): with the symbol `w = boolToSym3 sym`, the emitter writes
exactly `pre ++ configEncode3 n sym rest` — i.e. it emits an *encoded configuration* (state field + current symbol +
rest).

This is the clean payoff of the emit-side correctness chain: the machine's tape output is the abstract config encoding.

## What is proved (clean axioms, no `sorry`)

* **`writeFieldBit3_emits_config`** (PROVED) — `n+1 < X.length ⇒ ∃ N, reachIn N (s, pre.length, pre ++ X) (sOut,
  pre.length+n+1, pre ++ configEncode3 n sym (X.drop (n+2)))`: running the field-then-bit emitter with `w = boolToSym3 sym`
  emits the encoded configuration `configEncode3 n sym _`.

## Honest scope

This is the **emit-a-configuration** correctness — the output side fully linked to the config encoding.  It does **not**
yet connect the emitted config to the abstract simulated *step*, nor assemble `EmitsEncodedStep3` (which also needs the
input/transfer side).  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitConfig

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config (configEncode3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteFieldBit (writeFieldBit3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitPrefix (writeFieldBit3_emits)

/-- **The emitter emits a configuration (PROVED).**  With `w = boolToSym3 sym`, the field-then-bit emitter lays down the
encoded configuration `pre ++ configEncode3 n sym (X.drop (n+2))`. -/
theorem writeFieldBit3_emits_config (s sOut n : ℕ) (sym : Bool) (pre X : List Sym3) (hX : n + 1 < X.length) :
    ∃ N, reachIn (toNTM3 (writeFieldBit3 s sOut n (boolToSym3 sym))) N (s, pre.length, pre ++ X)
      (sOut, pre.length + n + 1, pre ++ configEncode3 n sym (X.drop (n + 2))) := by
  obtain ⟨N, h⟩ := writeFieldBit3_emits s sOut n (boolToSym3 sym) pre X hX
  rw [show pre ++ encodeNatBits3 n ++ boolToSym3 sym :: X.drop (n + 2)
        = pre ++ configEncode3 n sym (X.drop (n + 2)) from by rw [configEncode3, List.append_assoc]] at h
  exact ⟨N, h⟩

/-!
**The emitter emits a configuration, proved.**  `writeFieldBit3_emits_config` shows the machine's output is exactly the
abstract `configEncode3` — the output side fully linked to the config encoding.  Next: connect the emitted config to the
abstract simulated step (the input/transfer side), toward `EmitsEncodedStep3` — fragment by verified fragment, not faked.
Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitConfig

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EmitConfig.writeFieldBit3_emits_config
