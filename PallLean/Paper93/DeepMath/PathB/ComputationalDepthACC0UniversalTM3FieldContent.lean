import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Scan

/-!
# Entry 396 — universal-TM-table build: the 3-symbol field-content lemma `field_content3` (proved)

The `Sym3` port of entry 350's tape-content helper.  To run the field scanners (`scanNatFrom3`, entry 395) on a record
embedded in a larger tape, the rule-loop must know what the cells of an embedded unary field read.  This brick proves it:
if `T = pre ++ (encodeNatBits3 n ++ rest)` with `pre.length = h`, then cells `h .. h+n-1` read `I` and cell `h+n` (the
separator) reads `O`.

## What is proved (clean axioms, no `sorry`)

* **`getD_append_shift3`** (PROVED) — `(pre ++ X).getD (pre.length + i) O = X.getD i O`: reading past a prefix shifts the
  index.
* **`field_content3`** (PROVED) — `T = pre ++ (encodeNatBits3 n ++ rest)`, `pre.length = h` ⇒
  `(∀ i < n, T.getD (h+i) O = I) ∧ T.getD (h+n) O = O`: the embedded field's content, exactly the hypotheses
  `scanNatFrom3_run_eq` consumes.

## Honest scope

This is the **content lemma** feeding the `Sym3` record scanner.  It does **not** yet build the record scanner, the
table scan, nor the rule-loop.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldContent

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3 encNat3_getD_lt encNat3_getD_eq)

/-- **Reading past a prefix shifts the index (PROVED).** -/
theorem getD_append_shift3 (pre X : List Sym3) (i : ℕ) :
    (pre ++ X).getD (pre.length + i) Sym3.O = X.getD i Sym3.O := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right pre.length i),
      Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

/-- **Content of a nat field embedded in a tape (PROVED).**  If `T = pre ++ (encodeNatBits3 n ++ rest)` with
`pre.length = h`, then cells `h .. h+n-1` read `I` and cell `h+n` reads `O`. -/
theorem field_content3 (pre rest T : List Sym3) (n h : ℕ) (hlen : pre.length = h)
    (hT : T = pre ++ (encodeNatBits3 n ++ rest)) :
    (∀ i, i < n → T.getD (h + i) Sym3.O = Sym3.I) ∧ T.getD (h + n) Sym3.O = Sym3.O := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hT, ← hlen, getD_append_shift3]; exact encNat3_getD_lt n rest i hi
  · rw [hT, ← hlen, getD_append_shift3]; exact encNat3_getD_eq n rest

/-!
**The 3-symbol field-content lemma, proved.**  `field_content3` supplies exactly the content hypotheses
`scanNatFrom3_run_eq` consumes, so the next brick composes the field scanners into a `Sym3` record scanner — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldContent

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldContent.field_content3
