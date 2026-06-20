import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FieldContent
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Compose

/-!
# Entry 397 — universal-TM-table build: the 3-symbol record scanner `scanTransFrom3` (proved)

The `Sym3` port of the list-preserving record scanner (entry 371).  It composes the five field scanners
(`scanNatFrom3`/`scanBit3`, entry 395) into a relocatable scanner for one encoded transition, on the marker tape
`T = pre ++ encodeTransBits3 t ++ rest`, returning `T` **exactly** — the property the rule-table loop needs to re-run the
scanner on the post-scan tape.  Because every field scan keeps the same tape `T` (the `_run_eq` versions), all five field
runs are on `T`, composed directly by `reachIn_seq3`.

## What is proved (clean axioms, no `sorry`)

* **`scanTransFrom3 base`** — `scanNatFrom3 base (base+1) ++ scanBit3 (base+1) (base+2) ++ scanNatFrom3 (base+2) (base+3)
  ++ scanBit3 (base+3) (base+4) ++ scanNatFrom3 (base+4) (base+5)`.
* **`scanTransFrom3_run_eq`** (PROVED) — `reachIn (toNTM3 (scanTransFrom3 base)) (rs+ws+mv+5)
  (base, pre.length, pre ++ encodeTransBits3 t ++ rest) (base+5, pre.length + (rs+ws+mv+5), pre ++ encodeTransBits3 t ++
  rest)`: the record scan from state `base` returns the *identical* tape, head past the record.

## Honest scope

This is the **list-preserving `Sym3` record scanner** — `scanTrans` at an arbitrary state base and head offset over the
marker alphabet, the loopable unit the rule-table traversal chains.  It does **not** yet loop over the whole table
(`scanTable3`), nor the rule-table scan-and-match, nor the apply.  Building those fragment by fragment is the genuine
remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanTrans

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans Move)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3 encodeTransBits3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Scan (scanNatFrom3 scanBit3 scanNatFrom3_run_eq scanBit3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldContent (field_content3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The relocatable `Sym3` record scanner.**  Five fields (`nat, sym, nat, sym, nat`) scanned through states
`base..base+5`. -/
def scanTransFrom3 (base : ℕ) : TMachine3 :=
  scanNatFrom3 base (base + 1) ++ scanBit3 (base + 1) (base + 2) ++ scanNatFrom3 (base + 2) (base + 3) ++
    scanBit3 (base + 3) (base + 4) ++ scanNatFrom3 (base + 4) (base + 5)

/-- **The `Sym3` record scan leaves the tape identical (PROVED).**  Scanning one transition on `T = pre ++
encodeTransBits3 t ++ rest` from state `base` returns `T` exactly, head past the record. -/
theorem scanTransFrom3_run_eq (base : ℕ) (t : TMTrans) (pre rest : List Sym3) :
    reachIn (toNTM3 (scanTransFrom3 base)) (t.1.1 + t.2.1 + t.2.2.2.val + 5)
      (base, pre.length, pre ++ encodeTransBits3 t ++ rest)
      (base + 5, pre.length + (t.1.1 + t.2.1 + t.2.2.2.val + 5), pre ++ encodeTransBits3 t ++ rest) := by
  obtain ⟨⟨rs, rsym⟩, ws, wsym, mv⟩ := t
  set T := pre ++ encodeTransBits3 (((rs, rsym), (ws, wsym, mv)) : TMTrans) ++ rest with hTdef
  have hTlen : pre.length + (rs + ws + mv.val + 5) ≤ T.length := by
    rw [hTdef]; simp only [List.length_append, encodeTransBits3, encodeNatBits3, List.length_replicate,
      List.length_cons, List.length_nil]; omega
  have hT1 : T = pre ++ (encodeNatBits3 rs ++ (boolToSym3 rsym ::
      ((encodeNatBits3 ws ++ boolToSym3 wsym :: encodeNatBits3 mv.val) ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits3, List.append_assoc, List.cons_append]
  have hT3 : T = (pre ++ encodeNatBits3 rs ++ [boolToSym3 rsym]) ++
      (encodeNatBits3 ws ++ (boolToSym3 wsym :: (encodeNatBits3 mv.val ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits3, List.append_assoc, List.cons_append]
  have hT5 : T = (pre ++ encodeNatBits3 rs ++ [boolToSym3 rsym] ++ encodeNatBits3 ws ++ [boolToSym3 wsym]) ++
      (encodeNatBits3 mv.val ++ rest) := by
    rw [hTdef]; simp [encodeTransBits3, List.append_assoc, List.cons_append]
  have hlen3 : (pre ++ encodeNatBits3 rs ++ [boolToSym3 rsym]).length = (pre.length + rs + 1) + 1 := by
    simp only [encodeNatBits3, List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega
  have hlen5 : (pre ++ encodeNatBits3 rs ++ [boolToSym3 rsym] ++ encodeNatBits3 ws ++ [boolToSym3 wsym]).length
      = (((pre.length + rs + 1) + 1) + ws + 1) + 1 := by
    simp only [encodeNatBits3, List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega
  obtain ⟨fc1l, fc1r⟩ := field_content3 pre _ T rs pre.length rfl hT1
  obtain ⟨fc3l, fc3r⟩ := field_content3 (pre ++ encodeNatBits3 rs ++ [boolToSym3 rsym]) _ T ws
    ((pre.length + rs + 1) + 1) hlen3 hT3
  obtain ⟨fc5l, fc5r⟩ := field_content3 (pre ++ encodeNatBits3 rs ++ [boolToSym3 rsym] ++ encodeNatBits3 ws ++
    [boolToSym3 wsym]) _ T mv.val ((((pre.length + rs + 1) + 1) + ws + 1) + 1) hlen5 hT5
  have run1 := scanNatFrom3_run_eq base (base + 1) rs pre.length T fc1l fc1r (by omega)
  have run2 := scanBit3_run_eq (base + 1) (base + 2) (pre.length + rs + 1) T (by omega)
  have run3 := scanNatFrom3_run_eq (base + 2) (base + 3) ws ((pre.length + rs + 1) + 1) T fc3l fc3r (by omega)
  have run4 := scanBit3_run_eq (base + 3) (base + 4) (((pre.length + rs + 1) + 1) + ws + 1) T (by omega)
  have run5 := scanNatFrom3_run_eq (base + 4) (base + 5) mv.val ((((pre.length + rs + 1) + 1) + ws + 1) + 1) T
    fc5l fc5r (by omega)
  have c1 := reachIn_seq3 _ _ _ _ _ _ _ run1 run2
  have c2 := reachIn_seq3 _ _ _ _ _ _ _ c1 run3
  have c3 := reachIn_seq3 _ _ _ _ _ _ _ c2 run4
  have c4 := reachIn_seq3 _ _ _ _ _ _ _ c3 run5
  convert c4 using 1
  · dsimp only; omega
  · dsimp only; rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨rfl, by omega, rfl⟩

/-!
**The list-preserving `Sym3` record scanner, proved.**  `scanTransFrom3_run_eq` returns the identical tape after scanning
one transition — every field scan is on the same `T`, so there is no transport.  Next: loop it over the whole table
(`scanTable3`), where the inductive step re-runs the scanner on the preserved list, then the scan-and-match and the apply
— fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanTrans

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ScanTrans.scanTransFrom3_run_eq
