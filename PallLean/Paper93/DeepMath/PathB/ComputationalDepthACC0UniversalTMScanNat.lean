import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMDecide

/-!
# Entry 344 — universal-TM-table build, the transition table begins: `scanNat` (proved)

This starts the *actual transition-table* construction (the one socket `EmitsEncodedStep` of bricks 9–10).  The first
real machine fragment is **`scanNat`**: a concrete `TMachine` that scans past one unary-encoded nat
(`encodeNatBits n = n` `true`s then a `false`) — the cursor-advance the universal scanner needs.  This brick proves the
**foundational tape lemma** (a scan step's write-back preserves the tape contents) and the `scanNat` single-step
behaviours.

## What is proved (clean axioms, no `sorry`)

* **`writeAt_getD`** (PROVED) — `(writeAt tape p w).getD q false = if q = p then w else tape.getD q false`: a write
  changes only the written cell.
* **`writeAt_getD_self`** (PROVED) — writing back the read symbol preserves *every* cell: `(writeAt tape p (tape.getD p
  false)).getD q false = tape.getD q false`.  The non-destructive-scan invariant.
* **`scanNat`** — the scanning machine: in state `0`, on `true` move right (stay scanning), on `false` (separator) go
  to state `1` and move right.
* **`scanNat_step_true`** (PROVED) — at a `true` cell the head advances, staying in state `0`.
* **`scanNat_step_false`** (PROVED) — at a `false` cell `scanNat` halts in state `1`, head advanced.

## Honest scope

This is the **first verified fragment of the universal-TM transition table** — the write-back-preserves-tape invariant
and the `scanNat` scanner's per-step behaviour.  It does **not** yet prove the full scan run (head reaches `n+1` after
scanning `encodeNatBits n`) — that is the next brick (a tape-invariant induction using `writeAt_getD_self`) — nor the
full `EmitsEncodedStep`.  Building those, fragment by verified fragment, is the genuine remaining low-level
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine Move concreteStep readSym applyTrans moveHead writeAt)

/-- **A write changes only the written cell (PROVED).** -/
theorem writeAt_getD (tape : List Bool) (p q : ℕ) (w : Bool) :
    (writeAt tape p w).getD q false = if q = p then w else tape.getD q false := by
  unfold writeAt
  rcases eq_or_ne q p with rfl | hne
  · have hlen : q < (tape ++ List.replicate (q + 1 - tape.length) false).length := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlen, if_pos rfl, Option.getD_some]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm, if_neg hne,
        ← List.getD_eq_getElem?_getD]
    rcases lt_or_ge q tape.length with hlt | hge
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
          List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hge]
      simp only [List.getElem?_replicate, Option.getD_none]
      split <;> rfl

/-- **Writing back the read symbol preserves every cell (PROVED).**  The non-destructive-scan invariant. -/
theorem writeAt_getD_self (tape : List Bool) (p q : ℕ) :
    (writeAt tape p (tape.getD p false)).getD q false = tape.getD q false := by
  rw [writeAt_getD]
  rcases eq_or_ne q p with rfl | hne
  · rw [if_pos rfl]
  · rw [if_neg hne]

/-- **The scan-one-nat machine.**  State `0` = scanning: on `true` move right and keep scanning; on `false` (the
separator) go to state `1` (done) and move right past it. -/
def scanNat : TMachine :=
  [((0, true), (0, true, (1 : Move))), ((0, false), (1, false, (1 : Move)))]

/-- **`scanNat` advances over a `true` cell (PROVED).**  At `(0, j, tp)` reading `true`, it steps to `(0, j+1, …)`,
staying in the scanning state. -/
theorem scanNat_step_true (j : ℕ) (tp : List Bool) (h : tp.getD j false = true) :
    concreteStep scanNat (0, j, tp) (0, j + 1, writeAt tp j true) := by
  refine ⟨((0, true), (0, true, (1 : Move))), ?_, ?_, ?_⟩
  · simp [scanNat]
  · show ((0 : ℕ), true) = (((0 : ℕ), j, tp).1, readSym ((0 : ℕ), j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-- **`scanNat` halts at the `false` separator (PROVED).**  At `(0, j, tp)` reading `false`, it steps to `(1, j+1, …)`
— state `1` (done), head advanced past the separator. -/
theorem scanNat_step_false (j : ℕ) (tp : List Bool) (h : tp.getD j false = false) :
    concreteStep scanNat (0, j, tp) (1, j + 1, writeAt tp j false) := by
  refine ⟨((0, false), (1, false, (1 : Move))), ?_, ?_, ?_⟩
  · simp [scanNat]
  · show ((0 : ℕ), false) = (((0 : ℕ), j, tp).1, readSym ((0 : ℕ), j, tp))
    simp only [readSym, h]
  · simp [applyTrans, moveHead]

/-!
**The transition table begins.**  The foundational write-back invariant (`writeAt_getD_self`: scanning preserves the
tape) and `scanNat`'s single-step behaviours (`scanNat_step_true`, `scanNat_step_false`) are the first verified
fragments of the universal-TM transition table.  Next: the full `scanNat` run (head reaches `n+1` after one encoded nat,
by a tape-invariant induction on `writeAt_getD_self`), then the field/rule scans, the apply, and `EmitsEncodedStep` —
built fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat.writeAt_getD
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat.writeAt_getD_self
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat.scanNat_step_true
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat.scanNat_step_false
