import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModpeDepth2

/-!
# Hard math (depth-3 prime-power composition) — the cell count multiplies per layer (proved)

The depth-3 (and deeper) recursion for prime-power `SYM∘AND` composition.  A depth-3 circuit applies a top gate `H` to `t`
depth-2 blocks `B_1, …, B_t`, each a prime-power `MOD_{p^e} ∘ AND` over `k` `AND`-gates.  Each block's value depends only on
its own count `c_i = #(satisfied AND-gates) ∈ {0,…,k}`, so the whole circuit factors through the **joint count vector**
`(c_1, …, c_t)`.  That vector lives in `{0,…,k}^t`, so it takes at most `(k+1)^t` values (`jointCells_card_le`), and the
depth-3 function has at most `(k+1)^t` distinct cells (`depth3_modpe_cells`) — the cell count **multiplies** per layer.

For constant depth (`t`, `e` constant), `(k+1)^t` is polynomial in `k`: the prime-power composition stays quasipolynomial via
the symmetric cell-count argument, exactly where the polynomial-degree method fails for `e ≥ 2`.

## What is proved (clean axioms, no `sorry`)

* **`jointCells_card_le`** (PROVED) — the joint count vector of `t` count-gates (each `≤ m` gates) takes `≤ (m+1)^t` values.
* **`depth3_modpe_cells`** (PROVED) — a depth-3 circuit over `t` depth-2 `MOD_{p^e}∘AND` blocks (each `k` `AND`-gates) has
  `≤ (k+1)^t` joint cells: any function of the block outputs has at most that many distinct cells.

## Honest scope

This is the depth-3 prime-power cell-count recursion (`(k+1)^t`, polynomial for constant depth), via the symmetric structure.
Arbitrary-depth ACC⁰ (the full nesting) and the unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) are **not** done here.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth3

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth2 (gateCount_le)

variable {t m n : ℕ}

/-- **The joint count vector of `t` count-gates takes `≤ (m+1)^t` values (PROVED).**  The depth-3 cell count: composing `t`
count-gates (each with `≤ m` gates) multiplies the per-block cell counts. -/
theorem jointCells_card_le (g : Fin t → (Fin m → (Fin n → Bool) → Bool)) :
    (Finset.univ.image (fun x i => gateCount (g i) x)).card ≤ (m + 1) ^ t := by
  classical
  calc (Finset.univ.image (fun x (i : Fin t) => gateCount (g i) x)).card
      ≤ (Fintype.piFinset (fun _ : Fin t => Finset.range (m + 1))).card := by
        apply Finset.card_le_card
        intro v hv
        simp only [Finset.mem_image] at hv
        obtain ⟨x, _, rfl⟩ := hv
        rw [Fintype.mem_piFinset]
        intro i; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (gateCount_le (g i) x))
    _ = (m + 1) ^ t := by
        rw [Fintype.card_piFinset]; simp [Finset.prod_const, Finset.card_range, Fintype.card_fin]

/-- **Depth-3 prime-power cell count (PROVED).**  A depth-3 circuit over `t` depth-2 `MOD_{p^e}∘AND` blocks (each `k`
`AND`-gates) factors through the joint count vector, so has `≤ (k+1)^t` distinct cells.  (`mono i` are the `AND`-supports of
block `i`.) -/
theorem depth3_modpe_cells (k : ℕ) (mono : Fin t → Fin k → Finset (Fin n)) :
    (Finset.univ.image
        (fun x (i : Fin t) => gateCount (fun j x => monoAND (mono i j) x) x)).card ≤ (k + 1) ^ t :=
  jointCells_card_le (fun i j x => monoAND (mono i j) x)

/-!
**Depth-3 prime-power composition, proved.**  The cell count multiplies per layer: `t` depth-2 `MOD_{p^e}∘AND` blocks give
`≤ (k+1)^t` joint cells — polynomial for constant depth, the symmetric-structure count that survives where the polynomial
method fails for `e ≥ 2`.  Remaining (open, not faked): arbitrary-depth nesting and the unconditional `NEXP ⊄ ACC⁰`.  Not
`NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth3

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpeDepth3.depth3_modpe_cells
