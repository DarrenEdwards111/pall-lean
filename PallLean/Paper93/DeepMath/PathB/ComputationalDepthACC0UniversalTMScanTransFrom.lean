import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMCopyBlockReturn

/-!
# Entry 367 — universal-TM-table build: the relocatable record scanner `scanTransFrom` (proved)

`scanTrans` (entry 350) scans one encoded transition, but with fixed states `0..5` starting at head `0`.  The
rule-table loop scans *successive* transitions, each at a different head and continuing the control state.  This brick
generalises `scanTrans` to a **relocatable** record scanner `scanTransFrom base`: states `base..base+5`, scanning a
transition that begins at an arbitrary head `h` (the length of a prefix `pre`), ending at state `base+5` with the head
advanced past the record.

## What is proved (clean axioms, no `sorry`)

* **`scanTransFrom base`** — `scanNatFrom base (base+1) ++ scanBit (base+1) (base+2) ++ scanNatFrom (base+2) (base+3) ++
  scanBit (base+3) (base+4) ++ scanNatFrom (base+4) (base+5)`.
* **`scanTransFrom_run`** (PROVED) — `∃ tp', reachIn (toNTM (scanTransFrom base)) (rs+ws+mv+5)
  (base, pre.length, pre ++ encodeTransBits t ++ rest) (base+5, pre.length + (rs+ws+mv+5), tp')`: from state `base` at
  the start of the record (offset `pre.length`), the scanner consumes the whole `encodeTransBits t` in `rs+ws+mv+5`
  steps, ending in state `base+5` with the head at the next record.

## Honest scope

This is the **relocatable record scanner** — `scanTrans` at an arbitrary state base and head offset, the loopable unit
the rule-table traversal chains.  It does **not** yet loop it over the whole table (`scanTable`), nor the rule-table
scan-and-match, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFrom

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans Move TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeNatBits encodeTransBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField (scanNatFrom)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFieldCompose (scanNatFrom_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit scanBit_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans (field_content)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The relocatable record scanner.**  Five fields (`nat, sym, nat, sym, nat`) scanned through states `base..base+5`. -/
def scanTransFrom (base : ℕ) : TMachine :=
  scanNatFrom base (base + 1) ++ scanBit (base + 1) (base + 2) ++ scanNatFrom (base + 2) (base + 3) ++
    scanBit (base + 3) (base + 4) ++ scanNatFrom (base + 4) (base + 5)

/-- **The relocatable record scan run (PROVED).**  From state `base` at the start of a record (head `pre.length`),
`scanTransFrom base` scans the whole `encodeTransBits t` in `rs+ws+mv+5` steps to state `base+5`, head past the record. -/
theorem scanTransFrom_run (base : ℕ) (t : TMTrans) (pre rest : List Bool) :
    ∃ tp', reachIn (toNTM (scanTransFrom base)) (t.1.1 + t.2.1 + t.2.2.2.val + 5)
      (base, pre.length, pre ++ encodeTransBits t ++ rest)
      (base + 5, pre.length + (t.1.1 + t.2.1 + t.2.2.2.val + 5), tp') := by
  obtain ⟨⟨rs, rsym⟩, ws, wsym, mv⟩ := t
  set T := pre ++ encodeTransBits (((rs, rsym), (ws, wsym, mv)) : TMTrans) ++ rest with hTdef
  have hT1 : T = pre ++ (encodeNatBits rs ++ (rsym :: ((encodeNatBits ws ++ wsym :: encodeNatBits mv.val) ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT3 : T = (pre ++ encodeNatBits rs ++ [rsym]) ++ (encodeNatBits ws ++ (wsym :: (encodeNatBits mv.val ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT5 : T = (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) ++ (encodeNatBits mv.val ++ rest) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  -- field 1 (rs), at offset pre.length
  obtain ⟨fc1l, fc1r⟩ := field_content pre _ T rs pre.length rfl hT1
  obtain ⟨tp1, run1, pres1⟩ := scanNatFrom_run_pres base (base + 1) rs pre.length T fc1l fc1r
  -- field 2 (rsym), one bit
  obtain ⟨tp2, run2, pres2⟩ := scanBit_run_pres (base + 1) (base + 2) (pre.length + rs + 1) tp1
  have pres_t2 : ∀ q, tp2.getD q false = T.getD q false := fun q => (pres2 q).trans (pres1 q)
  -- field 3 (ws)
  have hlen3 : (pre ++ encodeNatBits rs ++ [rsym]).length = (pre.length + rs + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]; omega
  obtain ⟨fc3l, fc3r⟩ := field_content (pre ++ encodeNatBits rs ++ [rsym]) _ T ws ((pre.length + rs + 1) + 1) hlen3 hT3
  obtain ⟨tp3, run3, pres3⟩ := scanNatFrom_run_pres (base + 2) (base + 3) ws ((pre.length + rs + 1) + 1) tp2
    (fun i hi => (pres_t2 _).trans (fc3l i hi)) ((pres_t2 _).trans fc3r)
  -- field 4 (wsym), one bit
  obtain ⟨tp4, run4, pres4⟩ := scanBit_run_pres (base + 3) (base + 4) (((pre.length + rs + 1) + 1) + ws + 1) tp3
  have pres_t4 : ∀ q, tp4.getD q false = T.getD q false :=
    fun q => (pres4 q).trans ((pres3 q).trans (pres_t2 q))
  -- field 5 (mv)
  have hlen5 : (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]).length
      = (((pre.length + rs + 1) + 1) + ws + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]; omega
  obtain ⟨fc5l, fc5r⟩ := field_content (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) _ T mv.val
    ((((pre.length + rs + 1) + 1) + ws + 1) + 1) hlen5 hT5
  obtain ⟨tp5, run5, pres5⟩ := scanNatFrom_run_pres (base + 4) (base + 5) mv.val
    ((((pre.length + rs + 1) + 1) + ws + 1) + 1) tp4
    (fun i hi => (pres_t4 _).trans (fc5l i hi)) ((pres_t4 _).trans fc5r)
  -- chain the five runs
  have c1 := reachIn_seq _ _ _ _ _ _ _ run1 run2
  have c2 := reachIn_seq _ _ _ _ _ _ _ c1 run3
  have c3 := reachIn_seq _ _ _ _ _ _ _ c2 run4
  have c4 := reachIn_seq _ _ _ _ _ _ _ c3 run5
  refine ⟨tp5, ?_⟩
  convert c4 using 1
  · dsimp only; omega
  · dsimp only; rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨rfl, by omega, rfl⟩

/-!
**The relocatable record scanner, proved.**  `scanTransFrom base` scans one transition at an arbitrary head and state
base, ending at `base+5` with the head past the record — the loopable unit of the rule-table traversal.  Next: loop it
over the whole table (`scanTable`), the rule-table scan-and-match, and the apply — fragment by verified fragment, not
faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFrom

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFrom.scanTransFrom_run
