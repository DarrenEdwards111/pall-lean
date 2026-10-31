import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EncTrans

/-!
# Entry 394 — universal-TM-table build: the 3-symbol machine encoding `encodeMachineBits3` (proved)

The `Sym3` port of `encodeMachineBits` (entry 338): a machine `M` is encoded as its length (an `I`-run + separator)
followed by its transitions concatenated.

## What is proved (clean axioms, no `sorry`)

* **`encodeMachineBits3 M`** — `encodeNatBits3 M.length ++ M.flatMap encodeTransBits3`.
* **`encodeMachineBits3_length`** (PROVED) — `(encodeMachineBits3 M).length = (M.length + 1) + (M.flatMap
  encodeTransBits3).length`: the count field plus the concatenated transitions.

## Honest scope

This **ports the machine encoding** to the marker alphabet, completing the encoding layer's structure.  It does **not**
yet build any `Sym3` scanner, nor the rule-loop, nor `EmitsEncodedStep`.  Building those fragment by fragment is the
genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncMachine

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3 encodeNatBits3_length)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (encodeTransBits3)

/-- **Encode a machine over `Sym3`**: its length, then its transitions concatenated. -/
def encodeMachineBits3 (M : List TMTrans) : List Sym3 :=
  encodeNatBits3 M.length ++ M.flatMap encodeTransBits3

theorem encodeMachineBits3_length (M : List TMTrans) :
    (encodeMachineBits3 M).length = (M.length + 1) + (M.flatMap encodeTransBits3).length := by
  rw [encodeMachineBits3, List.length_append, encodeNatBits3_length]

/-!
**The 3-symbol machine encoding, proved.**  `encodeMachineBits3` mirrors entry 338 over the marker alphabet,
completing the encoding layer's shape.  Next: the configuration encoding and the `Sym3` scanners — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncMachine

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncMachine.encodeMachineBits3_length
