import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MatchTable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Config

/-!
# Entry 458 — universal-TM-table build: the rule-record layout `record_RecOK` (proved)

The rule-table region of the assembly layout `φ`: an encoded rule record satisfies the matcher's `RecOK` precondition
(entry 410).  A rule's key is encoded exactly as a configuration is — `configEncode3 b rs rest` (state field `b`, read
symbol `rs`, then the rest of the table) — so the matcher reads a record's `(state length, read symbol)` the same way it
reads the config key.  Placing such a record at offset `c + d` (prefix of length `c + d`), the content fields of `RecOK`
(state field of `b` ones at `c+d`, separator at `c+d+b`, symbol cell at `c+d+b+1`) are *precisely* `configEncode3_content`.

## What is proved (clean axioms, no `sorry`)

* **`record_RecOK`** (PROVED) — with `pre.length = c + d`, `1 ≤ d`, `min a b < L`, and the bound: `RecOK (pre ++
  configEncode3 b rs rest) c a L (d, b, boolToSym3 rs)` — the encoded record at offset `c+d` meets the matcher's
  per-record obligation, with its `RecMatch` key `(b, boolToSym3 rs)`.

## Honest scope

This is the **per-record** layout bridge (encoding ⇒ `RecOK`).  It does **not** yet lay out a *list* of records at their
cumulative offsets, nor place the simulated tape's head marker, nor define the full `φ` / prove `EmitsEncodedStepEx3` (the
large but obstruction-free remaining assembly, per entry 456).  Building the rest fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordLayout

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config (configEncode3 configEncode3_content)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable (RecOK)

/-- **An encoded rule record meets `RecOK` (PROVED).**  A record `configEncode3 b rs rest` at offset `c+d` satisfies the
matcher's per-record obligation with key `(b, boolToSym3 rs)`. -/
theorem record_RecOK (pre rest : List Sym3) (c d b a L : ℕ) (rs : Bool) (hpre : pre.length = c + d)
    (hd : 1 ≤ d) (hmin : min a b < L) (hbnd : c + a + 1 + d < (pre ++ configEncode3 b rs rest).length) :
    RecOK (pre ++ configEncode3 b rs rest) c a L (d, b, boolToSym3 rs) := by
  have hc := configEncode3_content pre rest b rs
  refine ⟨hd, hmin, hbnd, ?_, ?_, ?_⟩
  · intro i hi
    have := hc.1 i hi; rwa [hpre] at this
  · have := hc.2.1; rwa [hpre] at this
  · have := hc.2.2; rwa [hpre] at this

/-!
**The rule-record layout, proved.**  An encoded rule record satisfies the matcher's `RecOK` precondition — the rule-table
region's per-record bridge from the encoding to the matcher.  Next: lay out a list of records at their cumulative offsets,
place the simulated tape with its head marker, and assemble `φ` / `U` toward `EmitsEncodedStepEx3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordLayout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordLayout.record_RecOK
