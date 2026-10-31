import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBitCostDiagDP
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyAny
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract
import Mathlib.Tactic

/-!
# Bit-cost model — the concrete interpreter read schedule, fully discharged (PROVED)

The read-structure hypothesis of `diagonal_flat_dp_poly` is here **discharged for the concrete interpreter**:
`interpReads E B M` lists the (worst-case) `≤ 3` sub-ranks the DP reads when filling cell `M` (decoded from
`M`), and every such read is at *strictly lower rank* (`interp_reads_lt_self`, via `cfgRank_reconstruct` +
`cfgRank_lt_code` / `cfgRank_lt_fuel`).  Hence, with no assumed hypothesis,

  `interp_flat_dp_poly` : `buildReadCost (interpReads E B) (cfgRank … + 1) ≤ 3 · P²`,  `P = (B+1)²(E+1)+1`.

So the flat/`List` reformulation of the universal interpreter's DP runs in **polynomial read-cost** — the
addressable counterpart of the `2 ^ cfgRank` single-`Nat` blow-up (`ComputationalDepthKleeneMemoBlowup`).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code cfgRank_lt_fuel)
open PallLean.Paper93.DeepMath.PathB.KleeneUCode (cfgRank_reconstruct fstSub_lt sndSub_lt)

namespace PallLean.Paper93.DeepMath.PathB.BitCost

/-- The (worst-case) sub-ranks the interpreter reads when filling cell `M`: `≤ 3` reads, decoded from `M`
(base/default: none; `pair`/`comp`/`rfind'`: 2; `prec`: 3). -/
def interpReads (E B M : ℕ) : List ℕ :=
  let k := M / (B + 1) / (E + 1)
  let ec := (M / (B + 1)) % (E + 1)
  let n := M % (B + 1)
  if k = 0 then []
  else if (Nat.unpair ec).1 = 4 then
    [cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n, cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n]
  else if (Nat.unpair ec).1 = 5 then
    [cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n, cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 B]
  else if (Nat.unpair ec).1 = 6 then
    [cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n, cfgRank E B (k - 1) ec B,
      cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 B]
  else if (Nat.unpair ec).1 = 7 then
    [cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 n, cfgRank E B (k - 1) ec B]
  else []

theorem interp_reads_len (E B M : ℕ) : (interpReads E B M).length ≤ 3 := by
  unfold interpReads; dsimp only; split_ifs <;> simp

theorem interp_reads_lt_self (E B M : ℕ) : ∀ r ∈ interpReads E B M, r < M := by
  have hrec : cfgRank E B (M / (B + 1) / (E + 1)) ((M / (B + 1)) % (E + 1)) (M % (B + 1)) = M :=
    cfgRank_reconstruct E B M
  have hecE : (M / (B + 1)) % (E + 1) ≤ E := Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos E))
  have hnB : M % (B + 1) ≤ B := Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos B))
  intro r hr
  unfold interpReads at hr; dsimp only at hr
  rw [← hrec]
  set k := M / (B + 1) / (E + 1) with hk
  set ec := (M / (B + 1)) % (E + 1) with hec
  set n := M % (B + 1) with hn
  split_ifs at hr with h0 h4 h5 h6 h7 <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
  · rcases hr with h | h
    · rw [h]; exact cfgRank_lt_code E B k ec _ n n (fstSub_lt ec (by omega)) hecE hnB
    · rw [h]; exact cfgRank_lt_code E B k ec _ n n (sndSub_lt ec (by omega)) hecE hnB
  · rcases hr with h | h
    · rw [h]; exact cfgRank_lt_code E B k ec _ n n (sndSub_lt ec (by omega)) hecE hnB
    · rw [h]; exact cfgRank_lt_code E B k ec _ n B (fstSub_lt ec (by omega)) hecE (le_refl B)
  · rcases hr with h | h | h
    · rw [h]; exact cfgRank_lt_code E B k ec _ n n (fstSub_lt ec (by omega)) hecE hnB
    · rw [h]; exact cfgRank_lt_fuel E B k (k - 1) ec ec n B (Nat.sub_one_lt h0) hecE (le_refl B)
    · rw [h]; exact cfgRank_lt_code E B k ec _ n B (sndSub_lt ec (by omega)) hecE (le_refl B)
  · rcases hr with h | h
    · rw [h]; exact cfgRank_lt_code E B k ec _ n n (fstSub_lt ec (by omega)) hecE hnB
    · rw [h]; exact cfgRank_lt_fuel E B k (k - 1) ec ec n B (Nat.sub_one_lt h0) hecE (le_refl B)

/-- **The concrete interpreter's flat DP runs in polynomial read-cost** — fully discharged (no assumed
read-structure hypothesis): `≤ 3·P²` with `P = (B+1)²(E+1)+1`. -/
theorem interp_flat_dp_poly (E B K ec n : ℕ) (hK : K ≤ B) (hec : ec ≤ E) (hn : n ≤ B) :
    buildReadCost (interpReads E B) (cfgRank E B K ec n + 1)
      ≤ 3 * ((B + 1) * (B + 1) * (E + 1) + 1) * ((B + 1) * (B + 1) * (E + 1) + 1) := by
  set P := (B + 1) * (B + 1) * (E + 1) + 1 with hP
  have hreads : ∀ M, M < cfgRank E B K ec n + 1 →
      (∀ r ∈ interpReads E B M, r < cfgRank E B K ec n + 1) ∧ (interpReads E B M).length ≤ 3 := by
    intro M hM
    exact ⟨fun r hr => lt_trans (interp_reads_lt_self E B M r hr) hM, interp_reads_len E B M⟩
  have hbase := buildReadCost_le (interpReads E B) 3 (cfgRank E B K ec n + 1) hreads
  have hcells : cfgRank E B K ec n + 1 ≤ P := by
    have := cfgRank_le_poly E B K ec n hK hec hn; omega
  calc buildReadCost (interpReads E B) (cfgRank E B K ec n + 1)
        ≤ 3 * (cfgRank E B K ec n + 1) * (cfgRank E B K ec n + 1) := hbase
    _ ≤ 3 * P * P := Nat.mul_le_mul (by omega) hcells

end PallLean.Paper93.DeepMath.PathB.BitCost

#print axioms PallLean.Paper93.DeepMath.PathB.BitCost.interp_flat_dp_poly
