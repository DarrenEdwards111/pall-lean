import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMScanNat

/-!
# Entry 345 — universal-TM-table build: the full `scanNat` run (proved)

Entry 344 gave `scanNat` and its single-step behaviours.  This brick proves the **full scan**: started at the beginning
of an encoded nat `encodeNatBits n` (followed by arbitrary `rest`), `scanNat` runs `n + 1` steps and halts in state `1`
with the head at position `n + 1` — having consumed exactly the encoded nat and stopped at `rest`.

The proof is a tape-invariant induction: after `j ≤ n` steps the machine is in state `0` at head `j`, and the tape
still reads as the original (the write-back invariant `writeAt_getD_self`, entry 344); so each cell `j < n` reads
`true` (advance) and cell `n` reads `false` (halt) — using the `encodeNatBits` content lemmas.

## What is proved (clean axioms, no `sorry`)

* **`encNat_getD_lt`** — `(encodeNatBits n ++ rest).getD j false = true` for `j < n` (the unary `true`s).
* **`encNat_getD_eq`** — `(encodeNatBits n ++ rest).getD n false = false` (the separator).
* **`scanNat_scan`** — the tape-invariant: after `j ≤ n` steps, state `0`, head `j`, tape contents preserved.
* **`scanNat_run`** (PROVED) — `∃ tp, reachIn (toNTM scanNat) (n+1) (0, 0, encodeNatBits n ++ rest) (1, n+1, tp)`: the
  full scan consumes one encoded nat in `n+1` steps, halting in state `1` at head `n+1`.

## Honest scope

This proves the **full `scanNat` run** — the verified cursor-advance over one encoded nat, the core scanning primitive of
the universal machine.  The next fragments compose such scans (skip the five transition fields, scan the rule table for
a match), then the apply, then `EmitsEncodedStep` — built fragment by verified fragment, **not faked**.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNatRun

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (toNTM concreteStep writeAt)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn reachIn_add)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeNatBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNat
  (scanNat scanNat_step_true scanNat_step_false writeAt_getD_self)

/-- **The unary `true`s (PROVED).**  `(encodeNatBits n ++ rest).getD j false = true` for `j < n`. -/
theorem encNat_getD_lt (n : ℕ) (rest : List Bool) (j : ℕ) (hj : j < n) :
    (encodeNatBits n ++ rest).getD j false = true := by
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp [encodeNatBits]; omega)]
  simp only [encodeNatBits]
  rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hj),
      List.getElem?_replicate_of_lt hj]
  rfl

/-- **The separator (PROVED).**  `(encodeNatBits n ++ rest).getD n false = false`. -/
theorem encNat_getD_eq (n : ℕ) (rest : List Bool) :
    (encodeNatBits n ++ rest).getD n false = false := by
  rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp [encodeNatBits])]
  simp only [encodeNatBits]
  rw [List.getElem?_append_right (by rw [List.length_replicate])]
  simp

/-- **The scan tape-invariant (PROVED).**  After `j ≤ n` steps from the start, `scanNat` is in state `0` at head `j`,
with the tape contents preserved (each cell still reads as in the original encoding). -/
theorem scanNat_scan (n : ℕ) (rest : List Bool) : ∀ j, j ≤ n →
    ∃ tp, reachIn (toNTM scanNat) j (0, 0, encodeNatBits n ++ rest) (0, j, tp) ∧
      ∀ q, tp.getD q false = (encodeNatBits n ++ rest).getD q false := by
  intro j
  induction j with
  | zero => intro _; exact ⟨encodeNatBits n ++ rest, rfl, fun _ => rfl⟩
  | succ j ih =>
      intro hj
      obtain ⟨tp, hr, hpres⟩ := ih (by omega)
      have htrue : tp.getD j false = true := by rw [hpres j, encNat_getD_lt n rest j (by omega)]
      have hstep := scanNat_step_true j tp htrue
      refine ⟨writeAt tp j true, ?_, ?_⟩
      · exact (reachIn_add (toNTM scanNat) j 1 _ _).mpr ⟨(0, j, tp), hr, ⟨_, hstep, rfl⟩⟩
      · intro q
        have hwb : (writeAt tp j true).getD q false = (writeAt tp j (tp.getD j false)).getD q false := by
          rw [htrue]
        rw [hwb, writeAt_getD_self, hpres q]

/-- **The full `scanNat` run (PROVED).**  From `(0, 0, encodeNatBits n ++ rest)`, `scanNat` runs `n + 1` steps to a
configuration in state `1` with head at `n + 1` — having scanned exactly one encoded nat and stopped at `rest`. -/
theorem scanNat_run (n : ℕ) (rest : List Bool) :
    ∃ tp, reachIn (toNTM scanNat) (n + 1) (0, 0, encodeNatBits n ++ rest) (1, n + 1, tp) := by
  obtain ⟨tp, hr, hpres⟩ := scanNat_scan n rest n (le_refl n)
  have hfalse : tp.getD n false = false := by rw [hpres n, encNat_getD_eq]
  have hstep := scanNat_step_false n tp hfalse
  exact ⟨writeAt tp n false,
    (reachIn_add (toNTM scanNat) n 1 _ _).mpr ⟨(0, n, tp), hr, ⟨_, hstep, rfl⟩⟩⟩

/-!
**The full `scanNat` run, proved.**  `scanNat_run` verifies the universal scanner's cursor-advance over one encoded nat
(`n + 1` steps, halting in state `1` at head `n + 1`), via the tape-invariant `scanNat_scan` (write-back preservation,
entry 344) and the `encodeNatBits` content lemmas.  Next: compose scans to skip the five transition fields, scan the
rule table for a match, the apply, and `EmitsEncodedStep` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNatRun

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNatRun.encNat_getD_lt
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNatRun.encNat_getD_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScanNatRun.scanNat_run
