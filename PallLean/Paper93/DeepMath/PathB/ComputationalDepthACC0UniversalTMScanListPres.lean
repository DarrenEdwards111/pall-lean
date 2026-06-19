import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMWriteAtId

/-!
# Entry 370 — universal-TM-table build: list-preserving field scanners (proved)

Entry 369 (`writeAt_id_of_lt`) showed an in-bounds write-back is the identity *as a list*.  Since the field scanners
write back exactly the symbol they read, when the scanned positions are in bounds each step leaves the tape *unchanged
as a list* — so the whole scan keeps the **same list** `tp`, not merely a `getD`-equal one.  This brick upgrades the
nat- and bit-field scanners to that list-level guarantee, the property the rule-table loop needs to re-run the scanner
on the post-scan tape.

## What is proved (clean axioms, no `sorry`)

* **`scanBit_run_eq`** (PROVED) — `h < tp.length → reachIn (toNTM (scanBit s s')) 1 (s, h, tp) (s', h+1, tp)`: one bit
  scan leaving the tape *identical*.
* **`scanNatFrom_run_eq`** (PROVED) — given the content hypotheses and `h + n < tp.length` (the whole field, separator
  included, in bounds), `reachIn (toNTM (scanNatFrom s s')) (n+1) (s, h, tp) (s', h+n+1, tp)`: the nat-field scan
  leaving the tape *identical*.

## Honest scope

These are the **list-preserving field scanners** — the scan returns the same tape list, not just a `getD`-equal one,
under an in-bounds hypothesis.  They do **not** yet compose into a list-preserving record scanner (`scanTransFrom`), nor
the table loop, nor the apply.  Building those fragment by fragment is the genuine remaining construction, **not faked**.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanListPres

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM writeAt)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanField (scanNatFrom scanNatFrom_step_true scanNatFrom_step_false)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanBit (scanBit scanBit_step)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMWriteAtId (writeAt_id_of_lt)

/-- **`scanBit` leaves the tape identical (PROVED).**  At an in-bounds head, the one-step bit scan returns the same tape
list. -/
theorem scanBit_run_eq (s s' h : ℕ) (tp : List Bool) (hbound : h < tp.length) :
    reachIn (toNTM (scanBit s s')) 1 (s, h, tp) (s', h + 1, tp) := by
  have hstep := scanBit_step s s' h tp
  rw [writeAt_id_of_lt tp h hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-- **`scanNatFrom` leaves the tape identical (PROVED).**  Given the field content hypotheses and the whole field
(separator included) in bounds, the scan returns the same tape list. -/
theorem scanNatFrom_run_eq (s s' n h : ℕ) (tp : List Bool)
    (htrue : ∀ i, i < n → tp.getD (h + i) false = true)
    (hfalse : tp.getD (h + n) false = false)
    (hbound : h + n < tp.length) :
    reachIn (toNTM (scanNatFrom s s')) (n + 1) (s, h, tp) (s', h + n + 1, tp) := by
  have scan : ∀ j, j ≤ n → reachIn (toNTM (scanNatFrom s s')) j (s, h, tp) (s, h + j, tp) := by
    intro j
    induction j with
    | zero => intro _; exact rfl
    | succ j ih =>
        intro hj
        have hr := ih (by omega)
        have htrue' : tp.getD (h + j) false = true := htrue j (by omega)
        have hstep := scanNatFrom_step_true s s' (h + j) tp htrue'
        have heq : writeAt tp (h + j) true = tp := by
          rw [← htrue']; exact writeAt_id_of_lt tp (h + j) (by omega)
        rw [heq] at hstep
        exact (reachIn_add (toNTM (scanNatFrom s s')) j 1 _ _).mpr ⟨(s, h + j, tp), hr, ⟨_, hstep, rfl⟩⟩
  have hr := scan n (le_refl n)
  have hstep := scanNatFrom_step_false s s' (h + n) tp hfalse
  have heq : writeAt tp (h + n) false = tp := by
    rw [← hfalse]; exact writeAt_id_of_lt tp (h + n) hbound
  rw [heq] at hstep
  exact (reachIn_add (toNTM (scanNatFrom s s')) n 1 _ _).mpr ⟨(s, h + n, tp), hr, ⟨_, hstep, rfl⟩⟩

/-!
**The list-preserving field scanners, proved.**  Under an in-bounds hypothesis, `scanBit` and `scanNatFrom` return the
*same tape list*, since each write-back is the identity (`writeAt_id_of_lt`).  Next: compose them into a list-preserving
record scanner, then loop it over the table (`scanTable`), then the scan-and-match and the apply — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanListPres

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanListPres.scanBit_run_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanListPres.scanNatFrom_run_eq
