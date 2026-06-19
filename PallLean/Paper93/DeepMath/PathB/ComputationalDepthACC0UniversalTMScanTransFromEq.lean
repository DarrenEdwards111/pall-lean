import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanListPres

/-!
# Entry 371 — universal-TM-table build: the list-preserving record scanner `scanTransFrom_run_eq` (proved)

Entry 370 upgraded the field scanners to *list*-preservation (the tape returns identical, not merely `getD`-equal),
under an in-bounds hypothesis.  This brick composes them into a list-preserving **record** scanner: scanning one
transition on the tape `T = pre ++ encodeTransBits t ++ rest` returns `T` **exactly** — the property the rule-table loop
needs to re-run the scanner on the post-scan tape.

Because every field scan now keeps the same tape `T`, there is *no* preservation-transport between fields (unlike entry
367/368): all five field runs are on `T`, composed directly by `reachIn_seq`.

## What is proved (clean axioms, no `sorry`)

* **`scanTransFrom_run_eq`** (PROVED) — `reachIn (toNTM (scanTransFrom base)) (rs+ws+mv+5)
  (base, pre.length, pre ++ encodeTransBits t ++ rest) (base+5, pre.length + (rs+ws+mv+5), pre ++ encodeTransBits t ++
  rest)`: the record scan from state `base` returns the *identical* tape, head past the record.

## Honest scope

This is the **list-preserving record scanner** — the record scan leaves the tape exactly unchanged.  It does **not** yet
loop over the whole table (`scanTable`), nor the rule-table scan-and-match, nor the apply.  Building those fragment by
fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFromEq

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans Move TMachine toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeNatBits encodeTransBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField (scanNatFrom)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans (field_content)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFrom (scanTransFrom)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanListPres (scanNatFrom_run_eq scanBit_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **The record scan leaves the tape identical (PROVED).**  Scanning one transition on `T = pre ++ encodeTransBits t
++ rest` from state `base` returns `T` exactly, head past the record. -/
theorem scanTransFrom_run_eq (base : ℕ) (t : TMTrans) (pre rest : List Bool) :
    reachIn (toNTM (scanTransFrom base)) (t.1.1 + t.2.1 + t.2.2.2.val + 5)
      (base, pre.length, pre ++ encodeTransBits t ++ rest)
      (base + 5, pre.length + (t.1.1 + t.2.1 + t.2.2.2.val + 5), pre ++ encodeTransBits t ++ rest) := by
  obtain ⟨⟨rs, rsym⟩, ws, wsym, mv⟩ := t
  set T := pre ++ encodeTransBits (((rs, rsym), (ws, wsym, mv)) : TMTrans) ++ rest with hTdef
  have hTlen : pre.length + (rs + ws + mv.val + 5) ≤ T.length := by
    rw [hTdef]; simp only [List.length_append, encodeTransBits, encodeNatBits, List.length_replicate,
      List.length_cons, List.length_nil]; omega
  have hT1 : T = pre ++ (encodeNatBits rs ++ (rsym :: ((encodeNatBits ws ++ wsym :: encodeNatBits mv.val) ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT3 : T = (pre ++ encodeNatBits rs ++ [rsym]) ++ (encodeNatBits ws ++ (wsym :: (encodeNatBits mv.val ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT5 : T = (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) ++ (encodeNatBits mv.val ++ rest) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hlen3 : (pre ++ encodeNatBits rs ++ [rsym]).length = (pre.length + rs + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega
  have hlen5 : (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]).length
      = (((pre.length + rs + 1) + 1) + ws + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega
  obtain ⟨fc1l, fc1r⟩ := field_content pre _ T rs pre.length rfl hT1
  obtain ⟨fc3l, fc3r⟩ := field_content (pre ++ encodeNatBits rs ++ [rsym]) _ T ws ((pre.length + rs + 1) + 1) hlen3 hT3
  obtain ⟨fc5l, fc5r⟩ := field_content (pre ++ encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) _ T mv.val
    ((((pre.length + rs + 1) + 1) + ws + 1) + 1) hlen5 hT5
  have run1 := scanNatFrom_run_eq base (base + 1) rs pre.length T fc1l fc1r (by omega)
  have run2 := scanBit_run_eq (base + 1) (base + 2) (pre.length + rs + 1) T (by omega)
  have run3 := scanNatFrom_run_eq (base + 2) (base + 3) ws ((pre.length + rs + 1) + 1) T fc3l fc3r (by omega)
  have run4 := scanBit_run_eq (base + 3) (base + 4) (((pre.length + rs + 1) + 1) + ws + 1) T (by omega)
  have run5 := scanNatFrom_run_eq (base + 4) (base + 5) mv.val ((((pre.length + rs + 1) + 1) + ws + 1) + 1) T
    fc5l fc5r (by omega)
  have c1 := reachIn_seq _ _ _ _ _ _ _ run1 run2
  have c2 := reachIn_seq _ _ _ _ _ _ _ c1 run3
  have c3 := reachIn_seq _ _ _ _ _ _ _ c2 run4
  have c4 := reachIn_seq _ _ _ _ _ _ _ c3 run5
  convert c4 using 1
  · dsimp only; omega
  · dsimp only; rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨rfl, by omega, rfl⟩

/-!
**The list-preserving record scanner, proved.**  `scanTransFrom_run_eq` returns the identical tape after scanning one
transition — every field scan is on the same `T`, so there is no transport.  Next: loop it over the whole table
(`scanTable`), where the inductive step now re-runs the scanner on the preserved list, then the scan-and-match and the
apply — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFromEq

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTransFromEq.scanTransFrom_run_eq
