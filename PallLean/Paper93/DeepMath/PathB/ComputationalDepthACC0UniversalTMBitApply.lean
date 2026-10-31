import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMBitLookup

/-!
# Entry 340 — universal-TM-table build, brick 7: bit-level apply (proved)

Brick 6 (entry 339) implemented the rule lookup over the scannable encoding.  Brick 7 implements the **apply-step** over
it: given the encoded current configuration and the matched transition, produce the encoded *next* configuration, and
prove it matches the abstract `applyTrans`.

**The config encoding.**  A configuration `(state, head, tape)` is encoded with the brick-338 nat grammar plus a
length-prefixed tape: `encodeConfig c := encodeNatBits state ++ encodeNatBits head ++ (encodeNatBits tape.length ++
tape)`, with a verified round-trip `decodeConfig (encodeConfig c ++ rest) = (c, rest)`.  The bit-level apply decodes the
config, applies the transition abstractly, and re-encodes: `bitApply bits t := encodeConfig (applyTrans (decodeConfig
bits).1 t)`, and `bitApply (encodeConfig c) t = encodeConfig (applyTrans c t)` — the bit-level apply *is* the abstract
`applyTrans`, up to encoding.

## What is proved (clean axioms, no `sorry`)

* **`encodeBoolList` / `decodeBoolList`** + **`decodeBoolList_encodeBoolList`** — length-prefixed bit-block round-trip.
* **`encodeConfig` / `decodeConfig`** + **`decodeConfig_encodeConfig`** — configuration round-trip: scan a `(state,
  head, tape)` config, leave the rest.
* **`bitApply`** + **`bitApply_encodeConfig`** (PROVED) — `bitApply (encodeConfig c) t = encodeConfig (applyTrans c t)`:
  the bit-level apply equals the abstract transition application, up to the config encoding.

## Honest scope

This implements the **apply-step over the scannable encoding** and proves it equals the abstract `applyTrans` (up to
encoding) — the config-update step of the simulation cycle, on the encoded tape format.  With brick 6 (lookup) this
gives both halves of one simulation step at the encoding level: scan-and-match the rule, then update the encoded config.
What remains is assembling these into one concrete `TMachine` `U` whose transitions realise the decode/scan/update as
actual moves over the tape, and proving `Realizes physU U φ cost` (+ the `f`-timing) — brick 8 (341), the construction,
built as verified bricks, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (CConfig TMTrans applyTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable
  (encodeNatBits decodeNatBits decodeNatBits_encodeNatBits)

/-- **Encode a bit-block**: its length, then the bits. -/
def encodeBoolList (l : List Bool) : List Bool := encodeNatBits l.length ++ l

/-- **Decode a bit-block**: read the length, take that many bits, return `(bits, rest)`. -/
def decodeBoolList (bits : List Bool) : List Bool × List Bool :=
  let r := decodeNatBits bits
  (r.2.take r.1, r.2.drop r.1)

/-- **Bit-block round-trip (PROVED).**  `decodeBoolList (encodeBoolList l ++ rest) = (l, rest)`. -/
theorem decodeBoolList_encodeBoolList (l rest : List Bool) :
    decodeBoolList (encodeBoolList l ++ rest) = (l, rest) := by
  unfold encodeBoolList decodeBoolList
  rw [List.append_assoc, decodeNatBits_encodeNatBits]
  simp

/-- **Encode a configuration** `(state, head, tape)`. -/
def encodeConfig (c : CConfig) : List Bool :=
  encodeNatBits c.1 ++ encodeNatBits c.2.1 ++ encodeBoolList c.2.2

/-- **Decode a configuration.** -/
def decodeConfig (bits : List Bool) : CConfig × List Bool :=
  let r1 := decodeNatBits bits
  let r2 := decodeNatBits r1.2
  let r3 := decodeBoolList r2.2
  ((r1.1, r2.1, r3.1), r3.2)

/-- **Configuration round-trip (PROVED).**  `decodeConfig (encodeConfig c ++ rest) = (c, rest)` — scan a config, leave
the rest. -/
theorem decodeConfig_encodeConfig (c : CConfig) (rest : List Bool) :
    decodeConfig (encodeConfig c ++ rest) = (c, rest) := by
  simp only [encodeConfig, decodeConfig, List.append_assoc, decodeNatBits_encodeNatBits,
    decodeBoolList_encodeBoolList]

/-- **Bit-level apply**: decode the config, apply the transition abstractly, re-encode. -/
def bitApply (bits : List Bool) (t : TMTrans) : List Bool :=
  encodeConfig (applyTrans (decodeConfig bits).1 t)

/-- **Bit-level apply is the abstract apply (PROVED).**  `bitApply (encodeConfig c) t = encodeConfig (applyTrans c t)`:
applying a transition at the encoding level produces the encoding of the abstractly-applied transition. -/
theorem bitApply_encodeConfig (c : CConfig) (t : TMTrans) :
    bitApply (encodeConfig c) t = encodeConfig (applyTrans c t) := by
  unfold bitApply
  rw [← List.append_nil (encodeConfig c), decodeConfig_encodeConfig]

/-!
**Brick 7, built.**  The configuration encoding round-trips (`decodeConfig_encodeConfig`), and the bit-level apply equals
the abstract `applyTrans` up to encoding (`bitApply_encodeConfig`).  With brick 6 this gives both halves of one
simulation step on the encoded tape — scan-and-match (lookup), then update (apply).  Next: assemble these into a
concrete `TMachine` `U` realising the decode/scan/update as tape moves, and prove `Realizes physU U φ cost` (+ `f`-timing)
— brick 8 (341), built as verified bricks, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply.decodeBoolList_encodeBoolList
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply.decodeConfig_encodeConfig
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitApply.bitApply_encodeConfig
