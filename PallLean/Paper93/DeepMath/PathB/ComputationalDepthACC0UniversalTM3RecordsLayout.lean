import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3RecordLayout

/-!
# Entry 459 — universal-TM-table build: the records-list cumulative layout `recordsTape3` / `records_RecOK` (proved)

The rule table laid out as a contiguous list of encoded records — the cumulative-offset structure the matcher walks.  Each
record `(b, rs)` is the block `recordBlock (b,rs) = encodeNatBits3 b ++ [boolToSym3 rs]` (length `b+2`); the whole table is
their concatenation, `recordsTape3 recs`.  Because a record nests as `configEncode3 b rs rest = recordBlock (b,rs) ++ rest`,
the table splits at any record, putting that record at the cumulative offset `(front.flatMap recordBlock).length` — so the
per-record bridge (`record_RecOK`, entry 458) applies to *every* record in the list.

## What is proved (clean axioms, no `sorry`)

* **`recordBlock r`** / **`recordsTape3 recs`** — a record's cells / the contiguous table.
* **`configEncode3_eq_recordBlock`** (PROVED) — `configEncode3 b rs X = recordBlock (b,rs) ++ X`.
* **`recordsTape3_split`** (PROVED) — `recordsTape3 (front ++ (b,rs) :: back) = front.flatMap recordBlock ++ configEncode3 b
  rs (recordsTape3 back)`.
* **`records_RecOK`** (PROVED) — every record of the list, at its cumulative offset, satisfies the matcher's `RecOK`.

## Honest scope

This is the **records-list cumulative layout** (the matcher can walk the whole table).  It does **not** yet place the
simulated tape's head marker, nor define the full `φ` / prove `EmitsEncodedStepEx3` (the large but obstruction-free
remaining assembly, per entry 456).  Building the rest fragment by fragment is the genuine remaining construction, **not
faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config (configEncode3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable (RecOK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordLayout (record_RecOK)

/-- A record's cells: its state field then its read-symbol cell. -/
def recordBlock (r : ℕ × Bool) : List Sym3 := encodeNatBits3 r.1 ++ [boolToSym3 r.2]

/-- The contiguous rule table: each record encoded with the rest of the table as its tail. -/
def recordsTape3 : List (ℕ × Bool) → List Sym3
  | [] => []
  | r :: rest => configEncode3 r.1 r.2 (recordsTape3 rest)

/-- **A record factors as its block then the rest (PROVED).** -/
theorem configEncode3_eq_recordBlock (b : ℕ) (rs : Bool) (X : List Sym3) :
    configEncode3 b rs X = recordBlock (b, rs) ++ X := by
  rw [recordBlock, configEncode3, List.append_assoc]; rfl

/-- **The records table splits at any record (PROVED).** -/
theorem recordsTape3_split (front : List (ℕ × Bool)) (b : ℕ) (rs : Bool) (back : List (ℕ × Bool)) :
    recordsTape3 (front ++ (b, rs) :: back) = front.flatMap recordBlock ++ configEncode3 b rs (recordsTape3 back) := by
  induction front with
  | nil => simp [recordsTape3]
  | cons f fs ih =>
      show configEncode3 f.1 f.2 (recordsTape3 (fs ++ (b, rs) :: back))
        = (f :: fs).flatMap recordBlock ++ configEncode3 b rs (recordsTape3 back)
      rw [configEncode3_eq_recordBlock f.1 f.2, ih, List.flatMap_cons, List.append_assoc]

/-- **Every record of the list satisfies `RecOK` at its cumulative offset (PROVED).** -/
theorem records_RecOK (pre : List Sym3) (front : List (ℕ × Bool)) (b : ℕ) (rs : Bool) (back : List (ℕ × Bool))
    (c d a L : ℕ) (hpre : (pre ++ front.flatMap recordBlock).length = c + d) (hd : 1 ≤ d) (hmin : min a b < L)
    (hbnd : c + a + 1 + d < (pre ++ recordsTape3 (front ++ (b, rs) :: back)).length) :
    RecOK (pre ++ recordsTape3 (front ++ (b, rs) :: back)) c a L (d, b, boolToSym3 rs) := by
  rw [recordsTape3_split, ← List.append_assoc] at *
  exact record_RecOK (pre ++ front.flatMap recordBlock) (recordsTape3 back) c d b a L rs hpre hd hmin hbnd

/-!
**The records-list cumulative layout, proved.**  `recordsTape3` lays the rule table contiguously and `records_RecOK` shows
every record meets the matcher's per-record obligation at its cumulative offset — so the matcher can walk the whole table.
Next: place the simulated tape with its head marker, and assemble `φ` / `U` toward `EmitsEncodedStepEx3` — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout.records_RecOK
