import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3HomeLayout
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3RecordsLayout

/-!
# Entry 461 — universal-TM-table build: the stitched full tape `fullTape3` (proved)

The `φ` stitching: combine the config region (entry 457) and the rule table (entries 458–459) into one tape, with the
simulated tape as a trailing region.  The layout is `home M | config key | rule table | simulated tape`:
`fullTape3 a cs rules simtape := M :: configEncode3 a cs (recordsTape3 rules ++ simtape)`.

Two facts compose the region lemmas onto the full tape:
* the config-key invariants hold (it is definitionally `homeConfigTape3 a cs (recordsTape3 rules ++ simtape)`), and
* every rule record satisfies the matcher's `RecOK` *on the full tape* — via `recordsTape3_split` and the fact that a
  record absorbs the trailing tape (`configEncode3 b rs X ++ Y = configEncode3 b rs (X ++ Y)`), reducing to the per-record
  bridge (entry 458).

## What is proved (clean axioms, no `sorry`)

* **`fullTape3 a cs rules simtape`** — the stitched tape.
* **`fullTape3_config`** (PROVED) — the config-key invariants (home marker, state field, cache) on the full tape.
* **`configEncode3_absorb_tail`** (PROVED) — `configEncode3 b rs X ++ Y = configEncode3 b rs (X ++ Y)`.
* **`fullTape3_record_RecOK`** (PROVED) — every rule record of `rules` satisfies `RecOK` on the full tape at `c = 1`.

## Honest scope

This is the **config + rule-table stitching** onto the full tape (the matcher side).  It does **not** yet expose the
simulated tape's head marker at its full-tape offset, nor define the bit-decoding `φ : List Bool → List Bool → CConfig3`,
nor the windowed matcher / `U` / `EmitsEncodedStepEx3` (the large but obstruction-free remaining assembly, per entry 456).
Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3 encodeNatBits3_length)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config (configEncode3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable (RecOK)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3HomeLayout (homeConfigTape3 homeConfigTape3_content)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordsLayout (recordBlock recordsTape3 recordsTape3_split)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3RecordLayout (record_RecOK)

/-- **The stitched full tape.**  Home marker, config key, rule table, simulated tape. -/
def fullTape3 (a : ℕ) (cs : Bool) (rules : List (ℕ × Bool)) (simtape : List Sym3) : List Sym3 :=
  Sym3.M :: configEncode3 a cs (recordsTape3 rules ++ simtape)

/-- The config head (home marker, state field, cache), length `a+3`. -/
def cfgHead (a : ℕ) (cs : Bool) : List Sym3 :=
  Sym3.M :: encodeNatBits3 a ++ [boolToSym3 cs]

/-- **A record absorbs the trailing tape (PROVED).** -/
theorem configEncode3_absorb_tail (b : ℕ) (rs : Bool) (X Y : List Sym3) :
    configEncode3 b rs X ++ Y = configEncode3 b rs (X ++ Y) := by
  rw [configEncode3, configEncode3, List.append_assoc, List.cons_append]

/-- **The config-key invariants on the full tape (PROVED).** -/
theorem fullTape3_config (a : ℕ) (cs : Bool) (rules : List (ℕ × Bool)) (simtape : List Sym3) :
    (fullTape3 a cs rules simtape).getD 0 Sym3.O = Sym3.M
    ∧ (∀ i, i < a → (fullTape3 a cs rules simtape).getD (1 + i) Sym3.O = Sym3.I)
    ∧ (fullTape3 a cs rules simtape).getD (1 + a) Sym3.O = Sym3.O
    ∧ (fullTape3 a cs rules simtape).getD (1 + a + 1) Sym3.O = boolToSym3 cs :=
  homeConfigTape3_content a cs (recordsTape3 rules ++ simtape)

/-- The full tape rewritten with the config head as an explicit prefix. -/
theorem fullTape3_eq_cfgHead (a : ℕ) (cs : Bool) (rules : List (ℕ × Bool)) (simtape : List Sym3) :
    fullTape3 a cs rules simtape = cfgHead a cs ++ (recordsTape3 rules ++ simtape) := by
  rw [fullTape3, cfgHead, configEncode3]; simp [List.append_assoc]

private theorem cfgHead_length (a : ℕ) (cs : Bool) : (cfgHead a cs).length = a + 3 := by
  simp [cfgHead, encodeNatBits3_length]

/-- **Every rule record satisfies `RecOK` on the full tape (PROVED).** -/
theorem fullTape3_record_RecOK (a : ℕ) (cs : Bool) (front : List (ℕ × Bool)) (b : ℕ) (rs : Bool)
    (back : List (ℕ × Bool)) (simtape : List Sym3) (L : ℕ) (hmin : min a b < L)
    (hbnd : 1 + a + 1 + (a + 2 + (front.flatMap recordBlock).length)
      < (fullTape3 a cs (front ++ (b, rs) :: back) simtape).length) :
    RecOK (fullTape3 a cs (front ++ (b, rs) :: back) simtape) 1 a L
      (a + 2 + (front.flatMap recordBlock).length, b, boolToSym3 rs) := by
  have hsplit : fullTape3 a cs (front ++ (b, rs) :: back) simtape
      = (cfgHead a cs ++ front.flatMap recordBlock) ++ configEncode3 b rs (recordsTape3 back ++ simtape) := by
    rw [fullTape3_eq_cfgHead, recordsTape3_split, List.append_assoc, configEncode3_absorb_tail, ← List.append_assoc]
  rw [hsplit]
  refine record_RecOK (cfgHead a cs ++ front.flatMap recordBlock) (recordsTape3 back ++ simtape) 1
    (a + 2 + (front.flatMap recordBlock).length) b a L rs ?_ (by omega) hmin (by rw [← hsplit]; exact hbnd)
  rw [List.length_append, cfgHead_length]; omega

/-!
**The stitched full tape, proved.**  `fullTape3` combines config + rule table (+ trailing simulated tape), with the
config-key invariants and every record's `RecOK` proven on the full tape — the matcher side of `φ` assembled.  Next: expose
the simulated tape's head marker at its full-tape offset, define the bit-decoding `φ`, and assemble `U` toward
`EmitsEncodedStepEx3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FullLayout.fullTape3_record_RecOK
