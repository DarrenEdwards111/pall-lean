import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanTransFrom

/-!
# Entry 368 — universal-TM-table build: the record scan preserves the tape (proved)

`scanTransFrom_run` (entry 367) gives the relocatable record scan but discards the fact that the scan is
*non-destructive*.  Looping the scanner (the rule-table traversal) and interleaving it with key comparisons both need
to *re-read* the tape after a scan, so we must know the scan leaves the tape intact.  Every field scanner the record
scanner is built from (`scanNatFrom_run_pres`, `scanBit_run_pres`) already writes back what it reads, so the composed
scan preserves every cell; this brick threads those preservations through.

## What is proved (clean axioms, no `sorry`)

* **`scanTransFrom_run_pres`** (PROVED) — `∃ tp', reachIn (toNTM (scanTransFrom base)) (rs+ws+mv+5)
  (base, pre.length, pre ++ encodeTransBits t ++ rest) (base+5, pre.length + (rs+ws+mv+5), tp') ∧
  ∀ q, tp'.getD q false = (pre ++ encodeTransBits t ++ rest).getD q false`: the record scan of entry 367, additionally
  preserving the tape on every cell.

## Honest scope

This **strengthens** the relocatable record scan with tape preservation — the property the rule-table loop and the
scan-and-match need to re-read the tape across scans.  It does **not** yet loop the scanner over the whole table, nor
the rule-table scan-and-match, nor the apply.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFromPres

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans Move TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeNatBits encodeTransBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField (scanNatFrom)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFieldCompose (scanNatFrom_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit scanBit_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans (field_content)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFrom (scanTransFrom)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The record scan preserves the tape (PROVED).**  Like `scanTransFrom_run`, but additionally the resulting tape
agrees with the input on every cell (the scan is non-destructive). -/
theorem scanTransFrom_run_pres (base : ℕ) (t : TMTrans) (pre rest : List Bool) :
    ∃ tp', reachIn (toNTM (scanTransFrom base)) (t.1.1 + t.2.1 + t.2.2.2.val + 5)
        (base, pre.length, pre ++ encodeTransBits t ++ rest)
        (base + 5, pre.length + (t.1.1 + t.2.1 + t.2.2.2.val + 5), tp') ∧
      ∀ q, tp'.getD q false = (pre ++ encodeTransBits t ++ rest).getD q false := by
  obtain ⟨⟨rs, rsym⟩, ws, wsym, mv⟩ := t
  set T := pre ++ encodeTransBits (((rs, rsym), (ws, wsym, mv)) : TMTrans) ++ rest with hTdef
  have hT1 : T = pre ++ (encodeNatBits rs ++ (rsym :: ((encodeNatBits ws ++ wsym :: encodeNatBits mv.val) ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT3 : T = (pre ++ encodeNatBits rs ++ [rsym]) ++ (encodeNatBits ws ++ (wsym :: (encodeNatBits mv.val ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT5 : T = (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) ++ (encodeNatBits mv.val ++ rest) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  obtain ⟨fc1l, fc1r⟩ := field_content pre _ T rs pre.length rfl hT1
  obtain ⟨tp1, run1, pres1⟩ := scanNatFrom_run_pres base (base + 1) rs pre.length T fc1l fc1r
  obtain ⟨tp2, run2, pres2⟩ := scanBit_run_pres (base + 1) (base + 2) (pre.length + rs + 1) tp1
  have pres_t2 : ∀ q, tp2.getD q false = T.getD q false := fun q => (pres2 q).trans (pres1 q)
  have hlen3 : (pre ++ encodeNatBits rs ++ [rsym]).length = (pre.length + rs + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]; omega
  obtain ⟨fc3l, fc3r⟩ := field_content (pre ++ encodeNatBits rs ++ [rsym]) _ T ws ((pre.length + rs + 1) + 1) hlen3 hT3
  obtain ⟨tp3, run3, pres3⟩ := scanNatFrom_run_pres (base + 2) (base + 3) ws ((pre.length + rs + 1) + 1) tp2
    (fun i hi => (pres_t2 _).trans (fc3l i hi)) ((pres_t2 _).trans fc3r)
  obtain ⟨tp4, run4, pres4⟩ := scanBit_run_pres (base + 3) (base + 4) (((pre.length + rs + 1) + 1) + ws + 1) tp3
  have pres_t4 : ∀ q, tp4.getD q false = T.getD q false :=
    fun q => (pres4 q).trans ((pres3 q).trans (pres_t2 q))
  have hlen5 : (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]).length
      = (((pre.length + rs + 1) + 1) + ws + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]; omega
  obtain ⟨fc5l, fc5r⟩ := field_content (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) _ T mv.val
    ((((pre.length + rs + 1) + 1) + ws + 1) + 1) hlen5 hT5
  obtain ⟨tp5, run5, pres5⟩ := scanNatFrom_run_pres (base + 4) (base + 5) mv.val
    ((((pre.length + rs + 1) + 1) + ws + 1) + 1) tp4
    (fun i hi => (pres_t4 _).trans (fc5l i hi)) ((pres_t4 _).trans fc5r)
  have c1 := reachIn_seq _ _ _ _ _ _ _ run1 run2
  have c2 := reachIn_seq _ _ _ _ _ _ _ c1 run3
  have c3 := reachIn_seq _ _ _ _ _ _ _ c2 run4
  have c4 := reachIn_seq _ _ _ _ _ _ _ c3 run5
  refine ⟨tp5, ?_, fun q => (pres5 q).trans ((pres4 q).trans ((pres3 q).trans ((pres2 q).trans (pres1 q))))⟩
  convert c4 using 1
  · dsimp only; omega
  · dsimp only; rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨rfl, by omega, rfl⟩

/-!
**The record scan preserves the tape, proved.**  `scanTransFrom_run_pres` exposes that scanning a transition leaves the
tape intact, so the rule-table loop and the scan-and-match can re-read it across scans.  Next: loop the scanner over the
whole table (`scanTable`), the rule-table scan-and-match, and the apply — fragment by verified fragment, not faked.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFromPres

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFromPres.scanTransFrom_run_pres
