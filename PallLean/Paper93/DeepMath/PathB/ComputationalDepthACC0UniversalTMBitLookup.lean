import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScannable

/-!
# Entry 339 — universal-TM-table build, brick 6: bit-level rule lookup (proved)

Brick 5 (entry 338) gave the scannable bit-grammar with verified scan-and-leave-rest round-trips.  Brick 6 implements
the **rule lookup over that encoding** — scan the encoded transition table for the rule matching the current
`(state, symbol)` — and proves it agrees with the abstract `lookup` (entry 336), hence is sound and complete w.r.t.
`concreteStep`.

**The bit-level lookup.**  `bitLookup bits c` decodes the encoded machine from `bits` (the brick-338 scan) and applies
the abstract `lookup` to find the matching rule: `bitLookup bits c := (decodeMachineBits bits).bind (lookup ·.1 c)`.
The key theorem is that on a correctly-encoded table it *is* the abstract lookup — `bitLookup (encodeMachineBits M) c =
lookup M c` — via the brick-338 round-trip.  Soundness and completeness w.r.t. `concreteStep` then follow from brick 6.

## What is proved (clean axioms, no `sorry`)

* **`bitLookup`** — decode the encoded table and find the matching rule.
* **`bitLookup_encodeMachineBits`** (PROVED) — `bitLookup (encodeMachineBits M) c = lookup M c`: the bit-level lookup
  over the encoding is exactly the abstract lookup (via the brick-338 machine round-trip).
* **`bitLookup_sound`** (PROVED) — `bitLookup (encodeMachineBits M) c = some t → concreteStep M c (applyTrans c t)`.
* **`bitLookup_complete`** (PROVED) — `concreteStep M c d → ∃ t, bitLookup (encodeMachineBits M) c = some t`.

## Honest scope

This implements the **rule lookup over the scannable encoding** and proves it equals the abstract `lookup` (so sound and
complete) — the lookup step of the simulation cycle, now operating on the encoded tape format.  The "scan" is the
brick-338 `decodeMachineBits` (left-to-right bit consumption); what remains is realising `decodeMachineBits`/the find as
actual `TMachine` transitions (walking the bits with the brick-1 traversal) — folded into the assembly of `U`.  Next:
brick 7 (bit-level apply, 340), then assemble `U` and prove `Realizes physU U φ cost` (341).  Those remain the
construction, built as verified bricks, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitLookup

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine TMTrans CConfig concreteStep applyTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable
  (encodeMachineBits decodeMachineBits decodeMachineBits_encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup (lookup lookup_sound lookup_complete)

/-- **Bit-level rule lookup.**  Decode the encoded transition table from `bits` (the brick-338 scan) and find the rule
matching the current config `c`. -/
def bitLookup (bits : List Bool) (c : CConfig) : Option TMTrans :=
  (decodeMachineBits bits).bind (fun p => lookup p.1 c)

/-- **Bit-level lookup is the abstract lookup (PROVED).**  On a correctly-encoded table, `bitLookup (encodeMachineBits
M) c = lookup M c` — decoding recovers `M` exactly (brick-338 round-trip), so the bit-level and abstract lookups
coincide. -/
theorem bitLookup_encodeMachineBits (M : TMachine) (c : CConfig) :
    bitLookup (encodeMachineBits M) c = lookup M c := by
  unfold bitLookup
  rw [← List.append_nil (encodeMachineBits M), decodeMachineBits_encodeMachineBits]
  rfl

/-- **Bit-level lookup is sound (PROVED).**  A rule found by scanning the encoded table, applied to `c`, is a genuine
`concreteStep`. -/
theorem bitLookup_sound (M : TMachine) (c : CConfig) (t : TMTrans)
    (h : bitLookup (encodeMachineBits M) c = some t) : concreteStep M c (applyTrans c t) := by
  rw [bitLookup_encodeMachineBits] at h
  exact lookup_sound M c t h

/-- **Bit-level lookup is complete (PROVED).**  Whenever a step exists, scanning the encoded table finds a matching
rule. -/
theorem bitLookup_complete (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    ∃ t, bitLookup (encodeMachineBits M) c = some t := by
  rw [bitLookup_encodeMachineBits]
  exact lookup_complete M c d h

/-!
**Brick 6, built.**  `bitLookup` performs the rule lookup over the scannable encoding (decode the table via brick 338,
match via brick 336), and `bitLookup_encodeMachineBits` proves it equals the abstract `lookup` — hence sound
(`bitLookup_sound`) and complete (`bitLookup_complete`) w.r.t. `concreteStep`.  The lookup step now operates on the
encoded tape format.  Next: bit-level apply (340), then assemble `U` + `Realizes physU U φ cost` (341), realising the
decode/scan as `TMachine` transitions — built as verified bricks, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitLookup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitLookup.bitLookup_encodeMachineBits
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitLookup.bitLookup_sound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitLookup.bitLookup_complete
