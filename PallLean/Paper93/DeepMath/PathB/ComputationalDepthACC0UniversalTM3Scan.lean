import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EncMachine

/-!
# Entry 395 — universal-TM-table build: the 3-symbol field scanners (proved)

The `Sym3` ports of the field scanners (`scanNatFrom`, `scanBit`, entries 346/349) and their *list-preserving* runs
(entry 370): the universal machine must scan the `Sym3`-encoded tape (`I`-runs for nats, single `I`/`O` cells for
symbols).  Each writes back what it reads, so in bounds it leaves the tape identical (`writeAt3_id_of_lt`, entry 383).

## What is proved (clean axioms, no `sorry`)

* **`scanNatFrom3 s s'`** — scans a unary field: on `I` stay in `s` and move right; on the `O` separator go to `s'` and
  move right.  **`scanNatFrom3_run_eq`** (PROVED) — content hypotheses + `h+n < tp.length` ⇒ `reachIn (toNTM3
  (scanNatFrom3 s s')) (n+1) (s, h, tp) (s', h+n+1, tp)`, tape identical.
* **`scanBit3 s s'`** — scans one symbol cell, writing it back.  **`scanBit3_run_eq`** (PROVED) — `h < tp.length →
  reachIn (toNTM3 (scanBit3 s s')) 1 (s, h, tp) (s', h+1, tp)`, tape identical.

## Honest scope

These **port the field scanners** to the marker alphabet.  They do **not** yet compose into a record scanner, nor the
rule-loop.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Scan

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym
  (Sym3 TMachine3 concreteStep3 readSym3 writeAt3 applyTrans3 toNTM3 writeAt3_id_of_lt)

/-- **The unary-field scanner.**  State `s` scanning: on `I` stay and move right; on `O` (separator) go to `s'` and move
right. -/
def scanNatFrom3 (s s' : ℕ) : TMachine3 :=
  [((s, Sym3.I), (s, Sym3.I, (1 : Move))), ((s, Sym3.O), (s', Sym3.O, (1 : Move)))]

theorem scanNatFrom3_step_true (s s' j : ℕ) (tp : List Sym3) (h : tp.getD j Sym3.O = Sym3.I) :
    concreteStep3 (scanNatFrom3 s s') (s, j, tp) (s, j + 1, writeAt3 tp j Sym3.I) := by
  refine ⟨((s, Sym3.I), (s, Sym3.I, (1 : Move))), ?_, ?_, ?_⟩
  · simp [scanNatFrom3]
  · show (s, Sym3.I) = ((s, j, tp).1, readSym3 (s, j, tp))
    simp only [readSym3, h]
  · simp [applyTrans3, moveHead]

theorem scanNatFrom3_step_false (s s' j : ℕ) (tp : List Sym3) (h : tp.getD j Sym3.O = Sym3.O) :
    concreteStep3 (scanNatFrom3 s s') (s, j, tp) (s', j + 1, writeAt3 tp j Sym3.O) := by
  refine ⟨((s, Sym3.O), (s', Sym3.O, (1 : Move))), ?_, ?_, ?_⟩
  · simp [scanNatFrom3]
  · show (s, Sym3.O) = ((s, j, tp).1, readSym3 (s, j, tp))
    simp only [readSym3, h]
  · simp [applyTrans3, moveHead]

/-- **The unary-field scan leaves the tape identical (PROVED).** -/
theorem scanNatFrom3_run_eq (s s' n h : ℕ) (tp : List Sym3)
    (htrue : ∀ i, i < n → tp.getD (h + i) Sym3.O = Sym3.I) (hfalse : tp.getD (h + n) Sym3.O = Sym3.O)
    (hbound : h + n < tp.length) :
    reachIn (toNTM3 (scanNatFrom3 s s')) (n + 1) (s, h, tp) (s', h + n + 1, tp) := by
  have scan : ∀ j, j ≤ n → reachIn (toNTM3 (scanNatFrom3 s s')) j (s, h, tp) (s, h + j, tp) := by
    intro j
    induction j with
    | zero => intro _; exact rfl
    | succ j ih =>
        intro hj
        have hr := ih (by omega)
        have htrue' : tp.getD (h + j) Sym3.O = Sym3.I := htrue j (by omega)
        have hstep := scanNatFrom3_step_true s s' (h + j) tp htrue'
        have heq : writeAt3 tp (h + j) Sym3.I = tp := by
          rw [← htrue']; exact writeAt3_id_of_lt tp (h + j) (by omega)
        rw [heq] at hstep
        exact (reachIn_add (toNTM3 (scanNatFrom3 s s')) j 1 _ _).mpr ⟨(s, h + j, tp), hr, ⟨_, hstep, rfl⟩⟩
  have hr := scan n (le_refl n)
  have hstep := scanNatFrom3_step_false s s' (h + n) tp hfalse
  have heq : writeAt3 tp (h + n) Sym3.O = tp := by
    rw [← hfalse]; exact writeAt3_id_of_lt tp (h + n) hbound
  rw [heq] at hstep
  exact (reachIn_add (toNTM3 (scanNatFrom3 s s')) n 1 _ _).mpr ⟨(s, h + n, tp), hr, ⟨_, hstep, rfl⟩⟩

/-- **The one-bit scanner.**  On any symbol, write it back, move right, go to `s'`. -/
def scanBit3 (s s' : ℕ) : TMachine3 :=
  [((s, Sym3.I), (s', Sym3.I, (1 : Move))), ((s, Sym3.O), (s', Sym3.O, (1 : Move))),
   ((s, Sym3.M), (s', Sym3.M, (1 : Move)))]

theorem scanBit3_step (s s' j : ℕ) (tp : List Sym3) :
    concreteStep3 (scanBit3 s s') (s, j, tp) (s', j + 1, writeAt3 tp j (readSym3 (s, j, tp))) := by
  rcases h : readSym3 (s, j, tp) with _ | _ | _
  · exact ⟨((s, Sym3.O), (s', Sym3.O, (1 : Move))), by simp [scanBit3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.I), (s', Sym3.I, (1 : Move))), by simp [scanBit3], by simp [h], by simp [applyTrans3, moveHead]⟩
  · exact ⟨((s, Sym3.M), (s', Sym3.M, (1 : Move))), by simp [scanBit3], by simp [h], by simp [applyTrans3, moveHead]⟩

/-- **The one-bit scan leaves the tape identical (PROVED).** -/
theorem scanBit3_run_eq (s s' j : ℕ) (tp : List Sym3) (hbound : j < tp.length) :
    reachIn (toNTM3 (scanBit3 s s')) 1 (s, j, tp) (s', j + 1, tp) := by
  have hstep := scanBit3_step s s' j tp
  rw [show readSym3 (s, j, tp) = tp.getD j Sym3.O from rfl, writeAt3_id_of_lt tp j hbound] at hstep
  exact ⟨_, hstep, rfl⟩

/-!
**The 3-symbol field scanners, proved.**  `scanNatFrom3`/`scanBit3` scan the marker-tape encoding leaving it identical
in bounds, mirroring entries 346/349/370.  Next: the record scanner and the table scan over `Sym3` — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Scan

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Scan.scanNatFrom3_run_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Scan.scanBit3_run_eq
