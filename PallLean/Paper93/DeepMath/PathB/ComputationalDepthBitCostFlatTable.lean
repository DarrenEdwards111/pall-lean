import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostCellCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneTableCorrect
import Mathlib.Tactic

/-!
# Bit-cost model — the flat table has polynomial bit-size (PROVED)

The same memo table that is `≥ 2 ^ cells` as a single `Nat` (`encodeList`,
`ComputationalDepthKleeneMemoBlowup`) costs only **linearly many bits** when stored *flat* as addressable
cells (a `List ℕ`): its total bit-size is `≤ (cell count) · (max cell bit-length)`
(`flat_table_bitsize_le`).  Combined with the polynomial cell count (`cfgRank_le_poly`), the flat table at the
diagonal target has bit-size `≤ (B+1)²(E+1) · S` where `S` bounds each cell's bit-length
(`diagonal_flat_table_poly`) — **polynomial**, given poly-bit-length cell values.

This isolates the fix precisely: the blow-up was an artefact of packing the table into one `Nat`; addressable
(flat) storage is poly-size, the representation a bit-cost model must use.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneUCode (tableList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- Total bit-size of a list stored flat: the sum of the bit-lengths of its entries. -/
def listBitSize (L : List ℕ) : ℕ := (L.map bitlen).sum

@[simp] theorem listBitSize_nil : listBitSize [] = 0 := rfl
@[simp] theorem listBitSize_cons (x : ℕ) (xs : List ℕ) :
    listBitSize (x :: xs) = bitlen x + listBitSize xs := by simp [listBitSize]

/-- **The flat (list) table has bit-size `≤ (cell count) · (max cell bit-length)`.** -/
theorem flat_table_bitsize_le (spec : ℕ → ℕ) (S : ℕ) :
    ∀ N, (∀ M, M < N → bitlen (spec M) ≤ S) → listBitSize (tableList spec N) ≤ N * S := by
  intro N
  induction N with
  | zero => intro _; simp [tableList]
  | succ N ih =>
    intro hb
    have hhead : bitlen (spec N) ≤ S := hb N (by omega)
    have htail : listBitSize (tableList spec N) ≤ N * S := ih (fun M hM => hb M (by omega))
    show listBitSize (spec N :: tableList spec N) ≤ (N + 1) * S
    rw [listBitSize_cons]
    calc bitlen (spec N) + listBitSize (tableList spec N) ≤ S + N * S := by omega
      _ = (N + 1) * S := by ring

/-- **The flat memo table at the diagonal target has polynomial bit-size** (given poly-bit-length cells):
`≤ (B+1)²(E+1) · S`.  The efficient representation — to be contrasted with the `2 ^ cells` single-`Nat`
encoding. -/
theorem diagonal_flat_table_poly (E B K ec n S : ℕ) (spec : ℕ → ℕ)
    (hK : K ≤ B) (hec : ec ≤ E) (hn : n ≤ B)
    (hcells : ∀ M, M < cfgRank E B K ec n + 1 → bitlen (spec M) ≤ S) :
    listBitSize (tableList spec (cfgRank E B K ec n + 1)) ≤ ((B + 1) * (B + 1) * (E + 1) + 1) * S := by
  have h1 : listBitSize (tableList spec (cfgRank E B K ec n + 1)) ≤ (cfgRank E B K ec n + 1) * S :=
    flat_table_bitsize_le spec S _ hcells
  have h2 : cfgRank E B K ec n + 1 ≤ (B + 1) * (B + 1) * (E + 1) + 1 := by
    have := cfgRank_le_poly E B K ec n hK hec hn; omega
  calc listBitSize (tableList spec (cfgRank E B K ec n + 1))
        ≤ (cfgRank E B K ec n + 1) * S := h1
    _ ≤ ((B + 1) * (B + 1) * (E + 1) + 1) * S := Nat.mul_le_mul_right S h2

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.diagonal_flat_table_poly
