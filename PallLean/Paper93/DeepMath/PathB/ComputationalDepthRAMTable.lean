import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMCell
import Mathlib.Tactic

/-!
# RAM memo DP — indexed table access, verified (PROVED) — step 2, brick 2

`cellCopy` (brick 1) validated the *atom*: read/write a single cell **by a pointer already held in memory**.
The memo DP, however, addresses its table by a *running index* `i`: it needs `table[i]` where the address is
`base + i`, computed at run time.  This brick supplies that — genuine **indexed** addressable access — and is
exactly what the `Code` model cannot do cheaply (the table is one blowing-up `Nat`; there is no `base + i`
arithmetic on cells).

Memory layout convention (scratch cells, table elsewhere):

  `mem[0] = base`  (table start address) `mem[1] = i` (index) `mem[2] = value / result` `mem[3] = scratch`.

  `tableSet` — `table[i] := mem[2]`, i.e. `mem[base + i] := mem[2]` (DP **update**).
  `tableGet` — `mem[2] := table[i]`, i.e. `mem[2] := mem[base + i]` (DP **lookup**).

  `tableSet_correct` — after the run, `mem[base + i]` holds the written value (unconditional).
  `tableGet_correct` — after the run, `mem[2]` holds `mem[base + i]` (needs the table disjoint from scratch
                       cell `3`, the honest non-overlap side condition).
  `tableSet_cost` / `tableGet_cost` — both run in bit-cost `≤ 5·(3W + 1)`, polynomial in the bit-width, under
                       a width bound on the cells and on the computed address `base + i`.

The full memo DP iterates these two operations over the rank range.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- DP **update** `table[i] := mem[2]`: compute `base + i` into scratch cell `3`, then store through it. -/
def tableSet : List Instr :=
  [Instr.loadI 0, Instr.addI 1, Instr.storeI 3, Instr.loadI 2, Instr.storeIndI 3, Instr.haltI]

/-- DP **lookup** `mem[2] := table[i]`: compute `base + i` into scratch cell `3`, then read through it. -/
def tableGet : List Instr :=
  [Instr.loadI 0, Instr.addI 1, Instr.storeI 3, Instr.loadIndI 3, Instr.storeI 2, Instr.haltI]

/-- **`tableSet` writes `mem[2]` to the indexed cell `base + i`** — indexed addressable write works
end-to-end (unconditional: the write lands at `base + i` regardless of overlap). -/
theorem tableSet_correct (m : Mem) (acc0 : ℕ) :
    (run tableSet ⟨m, acc0, 0, false⟩ 5).mem (m 0 + m 1) = m 2 := by
  show (step tableSet (step tableSet (step tableSet (step tableSet
        (step tableSet ⟨m, acc0, 0, false⟩))))).mem (m 0 + m 1) = m 2
  simp [step, tableSet, List.getD, Mem.set]

/-- **`tableGet` reads the indexed cell `base + i` into `mem[2]`** — indexed addressable read works
end-to-end, provided the table cell `base + i` is disjoint from the scratch cell `3`. -/
theorem tableGet_correct (m : Mem) (acc0 : ℕ) (h : m 0 + m 1 ≠ 3) :
    (run tableGet ⟨m, acc0, 0, false⟩ 5).mem 2 = m (m 0 + m 1) := by
  show (step tableGet (step tableGet (step tableGet (step tableGet
        (step tableGet ⟨m, acc0, 0, false⟩))))).mem 2 = m (m 0 + m 1)
  simp [step, tableGet, List.getD, Mem.set, h]

/-- Bit-length facts for the small literal addresses used by the table programs. -/
private theorem bitlen_two_le : bitlen 2 ≤ 2 := by unfold bitlen; exact Nat.size_le.mpr (by norm_num)
private theorem bitlen_three_le : bitlen 3 ≤ 2 := by unfold bitlen; exact Nat.size_le.mpr (by norm_num)

/-- **`tableSet`'s bit-cost is polynomial in the bit-width**: `≤ 5·(3W + 1)`.  The hypotheses bound every
touched cell (`hmem`) and the computed address `base + i` (`hsum`) by `W`; `2 ≤ W` covers the literal
scratch addresses `2, 3`. -/
theorem tableSet_cost (m : Mem) (W : ℕ) (hW : 2 ≤ W)
    (hmem : ∀ x, bitlen (m x) ≤ W) (hsum : bitlen (m 0 + m 1) ≤ W) :
    runCost tableSet ⟨m, 0, 0, false⟩ 5 ≤ 5 * (3 * W + 1) := by
  have e0 : bitlen 0 = 0 := Nat.size_zero
  have e2 := bitlen_two_le
  have e3 := bitlen_three_le
  have b0 := hmem 0; have b1 := hmem 1; have b2 := hmem 2
  have hset2 : (m.set 3 (m 0 + m 1)) 2 = m 2 := Mem.set_get_ne m 3 (m 0 + m 1) 2 (by decide)
  simp only [runCost, stepCost, step, tableSet, List.getD_cons_zero, List.getD_cons_succ,
    Bool.false_eq_true, if_false, Mem.set_get_eq, e0, hset2]
  omega

/-- **`tableGet`'s bit-cost is polynomial in the bit-width**: `≤ 5·(3W + 1)`.  Same width hypotheses, plus the
non-overlap side condition `base + i ≠ 3` so the indexed read resolves to the table cell. -/
theorem tableGet_cost (m : Mem) (W : ℕ) (hW : 2 ≤ W)
    (hmem : ∀ x, bitlen (m x) ≤ W) (hsum : bitlen (m 0 + m 1) ≤ W) (hne : m 0 + m 1 ≠ 3) :
    runCost tableGet ⟨m, 0, 0, false⟩ 5 ≤ 5 * (3 * W + 1) := by
  have e0 : bitlen 0 = 0 := Nat.size_zero
  have e2 := bitlen_two_le
  have e3 := bitlen_three_le
  have b0 := hmem 0; have b1 := hmem 1; have bsum := hmem (m 0 + m 1)
  have hset3 : (m.set 3 (m 0 + m 1)) 3 = m 0 + m 1 := Mem.set_get_eq m 3 (m 0 + m 1)
  have hsetsum : (m.set 3 (m 0 + m 1)) (m 0 + m 1) = m (m 0 + m 1) :=
    Mem.set_get_ne m 3 (m 0 + m 1) (m 0 + m 1) hne
  simp only [runCost, stepCost, step, tableGet, List.getD_cons_zero, List.getD_cons_succ,
    Bool.false_eq_true, if_false, e0, hset3, hsetsum]
  omega

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.tableSet_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.tableGet_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.tableSet_cost
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.tableGet_cost
