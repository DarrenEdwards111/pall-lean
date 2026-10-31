import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanBit

/-!
# Entry 350 — universal-TM-table build: the full five-field transition scan `scanTrans` (proved)

Entries 344–349 built the field-scan primitives: `scanNatFrom` (relocatable nat scanner, 346), `scanBit` (one-bit
scanner, 349), `reachIn_seq` (the union-machine wiring law, 347), and `scanNatFrom_run_pres` (preservation-tracking run,
348).  This brick **assembles them into the full scan of one encoded transition**.

The `encodeTransBits` layout (entry 338) is the five fields `nat, sym, nat, sym, nat` — concretely
`encodeNatBits rs ++ rsym :: (encodeNatBits ws ++ wsym :: encodeNatBits mv)`.  The machine
`scanNatFrom 0 1 ++ scanBit 1 2 ++ scanNatFrom 2 3 ++ scanBit 3 4 ++ scanNatFrom 4 5` scans all five fields in sequence,
each field's scanner handing the preserved tape and new state to the next via `reachIn_seq`; the content hypothesis of
each nat field is discharged on the post-scan tape through accumulated preservation.

## What is proved (clean axioms, no `sorry`)

* **`getD_append_shift`** (PROVED) — `(pre ++ X).getD (pre.length + i) false = X.getD i false`: reading at an offset
  past a prefix is reading the suffix.
* **`field_content`** (PROVED) — for a tape `T = pre ++ (encodeNatBits n ++ rest)` with `pre.length = h`, the cells
  `h .. h+n-1` read `true` and cell `h+n` reads `false` (the content hypothesis a nat-field scan needs, reusing the
  entry-345 `encodeNatBits` content lemmas).
* **`scanTrans`** (PROVED) — `∃ tp', reachIn (toNTM (scanNatFrom 0 1 ++ scanBit 1 2 ++ scanNatFrom 2 3 ++ scanBit 3 4 ++
  scanNatFrom 4 5)) (rs+ws+mv+5) (0, 0, encodeTransBits t ++ rest) (5, rs+ws+mv+5, tp')`: the five-field machine scans a
  whole encoded transition in `|encodeTransBits t| = rs+ws+mv+5` steps, ending in state `5` with the head exactly past
  the transition (at the start of `rest`).

## Honest scope

This is the **full five-field transition scan** — the first complete traversal of one `encodeTransBits` record, built by
composing the verified field scanners.  It does **not** yet scan-and-match the *rule table* (locate the transition whose
`(state, read)` key matches the current configuration — the genuinely new decision step), nor apply the matched rule.
Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMTrans Move toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeNatBits encodeTransBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNatRun (encNat_getD_lt encNat_getD_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField (scanNatFrom)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMFieldCompose (scanNatFrom_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit scanBit_run_pres)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMCompose (reachIn_seq)

/-- **Reading past a prefix is reading the suffix (PROVED).** -/
theorem getD_append_shift (pre X : List Bool) (i : ℕ) :
    (pre ++ X).getD (pre.length + i) false = X.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right pre.length i),
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

/-- **Content of a nat field embedded in a tape (PROVED).**  If `T = pre ++ (encodeNatBits n ++ rest)` with
`pre.length = h`, then the cells `h .. h+n-1` read `true` and cell `h+n` reads `false`. -/
theorem field_content (pre rest T : List Bool) (n h : ℕ) (hlen : pre.length = h)
    (hT : T = pre ++ (encodeNatBits n ++ rest)) :
    (∀ i, i < n → T.getD (h + i) false = true) ∧ T.getD (h + n) false = false := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hT, ← hlen, getD_append_shift]; exact encNat_getD_lt n rest i hi
  · rw [hT, ← hlen, getD_append_shift]; exact encNat_getD_eq n rest

/-- **The full five-field transition scan (PROVED).**  The machine `scanNatFrom 0 1 ++ scanBit 1 2 ++ scanNatFrom 2 3
++ scanBit 3 4 ++ scanNatFrom 4 5` scans a whole encoded transition `encodeTransBits t ++ rest` in `rs+ws+mv+5` steps
(`= |encodeTransBits t|`), ending in state `5` with the head exactly past the transition. -/
theorem scanTrans (t : TMTrans) (rest : List Bool) :
    ∃ tp', reachIn (toNTM (scanNatFrom 0 1 ++ scanBit 1 2 ++ scanNatFrom 2 3 ++ scanBit 3 4 ++ scanNatFrom 4 5))
      (t.1.1 + t.2.1 + t.2.2.2.val + 5)
      (0, 0, encodeTransBits t ++ rest)
      (5, t.1.1 + t.2.1 + t.2.2.2.val + 5, tp') := by
  obtain ⟨⟨rs, rsym⟩, ws, wsym, mv⟩ := t
  set T := encodeTransBits (((rs, rsym), (ws, wsym, mv)) : TMTrans) ++ rest with hTdef
  -- the three nat-field content tapes
  have hT1 : T = [] ++ (encodeNatBits rs ++ (rsym :: ((encodeNatBits ws ++ wsym :: encodeNatBits mv.val) ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT3 : T = (encodeNatBits rs ++ [rsym]) ++ (encodeNatBits ws ++ (wsym :: (encodeNatBits mv.val ++ rest))) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  have hT5 : T = (encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) ++ (encodeNatBits mv.val ++ rest) := by
    rw [hTdef]; simp [encodeTransBits, List.append_assoc, List.cons_append]
  -- field 1 (rs), at offset 0
  obtain ⟨fc1l, fc1r⟩ := field_content [] _ T rs 0 rfl hT1
  obtain ⟨tp1, run1, pres1⟩ := scanNatFrom_run_pres 0 1 rs 0 T fc1l fc1r
  -- field 2 (rsym), one bit
  obtain ⟨tp2, run2, pres2⟩ := scanBit_run_pres 1 2 (0 + rs + 1) tp1
  have pres_t2 : ∀ q, tp2.getD q false = T.getD q false := fun q => (pres2 q).trans (pres1 q)
  -- field 3 (ws)
  have hlen3 : (encodeNatBits rs ++ [rsym]).length = (0 + rs + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]; omega
  obtain ⟨fc3l, fc3r⟩ := field_content (encodeNatBits rs ++ [rsym]) _ T ws ((0 + rs + 1) + 1) hlen3 hT3
  obtain ⟨tp3, run3, pres3⟩ := scanNatFrom_run_pres 2 3 ws ((0 + rs + 1) + 1) tp2
    (fun i hi => (pres_t2 _).trans (fc3l i hi)) ((pres_t2 _).trans fc3r)
  -- field 4 (wsym), one bit
  obtain ⟨tp4, run4, pres4⟩ := scanBit_run_pres 3 4 (((0 + rs + 1) + 1) + ws + 1) tp3
  have pres_t4 : ∀ q, tp4.getD q false = T.getD q false :=
    fun q => (pres4 q).trans ((pres3 q).trans (pres_t2 q))
  -- field 5 (mv)
  have hlen5 : (encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]).length
      = (((0 + rs + 1) + 1) + ws + 1) + 1 := by
    simp only [encodeNatBits, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]; omega
  obtain ⟨fc5l, fc5r⟩ := field_content (encodeNatBits rs ++ [rsym] ++ encodeNatBits ws ++ [wsym]) _ T mv.val
    ((((0 + rs + 1) + 1) + ws + 1) + 1) hlen5 hT5
  obtain ⟨tp5, run5, pres5⟩ := scanNatFrom_run_pres 4 5 mv.val ((((0 + rs + 1) + 1) + ws + 1) + 1) tp4
    (fun i hi => (pres_t4 _).trans (fc5l i hi)) ((pres_t4 _).trans fc5r)
  -- chain the five runs through the union machine
  have c1 := reachIn_seq _ _ _ _ _ _ _ run1 run2
  have c2 := reachIn_seq _ _ _ _ _ _ _ c1 run3
  have c3 := reachIn_seq _ _ _ _ _ _ _ c2 run4
  have c4 := reachIn_seq _ _ _ _ _ _ _ c3 run5
  refine ⟨tp5, ?_⟩
  convert c4 using 1
  · dsimp only; omega
  · dsimp only; rw [Prod.mk.injEq, Prod.mk.injEq]; exact ⟨rfl, by omega, rfl⟩

/-!
**The full five-field transition scan, proved.**  `scanTrans` traverses a whole `encodeTransBits` record by composing
the verified nat/bit scanners under `reachIn_seq`, discharging each nat field's content hypothesis on the post-scan tape
via accumulated preservation.  Next: scan-and-match the rule table (locate the transition whose `(state, read)` key
matches the current configuration), then apply the matched rule — fragment by verified fragment, not faked.  Not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans.getD_append_shift
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans.field_content
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanTrans.scanTrans
