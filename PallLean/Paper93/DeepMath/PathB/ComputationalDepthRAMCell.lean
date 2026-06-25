import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRAMWidth
import Mathlib.Tactic

/-!
# RAM memo DP — addressable cell access, verified (PROVED) — step 2, brick 1

The first brick of compiling the memo DP into a RAM program: validate its **atom** — read a table cell by
pointer and write it by pointer — both correct and polynomial-bit-cost.

  `cellCopy` — `mem[mem[1]] := mem[mem[0]]` (read-by-pointer, write-by-pointer).
  `cellCopy_correct` — after the program runs, the cell at address `mem[1]` holds the value from `mem[0]`.
  `cellCopy_cost` — its bit-cost is `≤ 2·(3W+1)`, polynomial in the bit-width.

This is exactly the addressable access the `Code` model cannot do cheaply (there the table is one `Nat` that
blows up); on the RAM it costs `O(bit-width)` per access.  The full memo DP iterates this atom over the rank
range.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.BitCost (bitlen)

namespace PallLean.Paper93.DeepMath.PathB.RAM

/-- Read the cell whose address is held in `mem[0]`, write it to the cell whose address is held in `mem[1]`
(the atom of an addressable memo table). -/
def cellCopy : List Instr := [Instr.loadIndI 0, Instr.storeIndI 1, Instr.haltI]

/-- **`cellCopy` correctly copies a table cell by pointer** — addressable access works end-to-end. -/
theorem cellCopy_correct (m : Mem) (acc0 : ℕ) :
    (run cellCopy ⟨m, acc0, 0, false⟩ 2).mem (m 1) = m (m 0) := by
  show (step cellCopy (step cellCopy ⟨m, acc0, 0, false⟩)).mem (m 1) = m (m 0)
  simp [step, cellCopy, List.getD]

/-- **`cellCopy`'s bit-cost is polynomial in the bit-width**: `≤ 2·(3W+1)`. -/
theorem cellCopy_cost (m : Mem) (W : ℕ) (hW : 1 ≤ W) (hmem : ∀ x, bitlen (m x) ≤ W) :
    runCost cellCopy ⟨m, 0, 0, false⟩ 2 ≤ 2 * (3 * W + 1) := by
  have e0 : bitlen 0 = 0 := Nat.size_zero
  have e1 : bitlen 1 = 1 := Nat.size_one
  have b0 := hmem 0; have b1 := hmem (m 0); have b2 := hmem 1
  show stepCost cellCopy ⟨m, 0, 0, false⟩
      + (stepCost cellCopy (step cellCopy ⟨m, 0, 0, false⟩) + 0) ≤ 2 * (3 * W + 1)
  simp only [stepCost, step, cellCopy, List.getD_cons_zero, List.getD_cons_succ,
    Bool.false_eq_true, if_false, e0, e1]
  omega

end PallLean.Paper93.DeepMath.PathB.RAM

#print axioms PallLean.Paper93.DeepMath.PathB.RAM.cellCopy_correct
#print axioms PallLean.Paper93.DeepMath.PathB.RAM.cellCopy_cost
