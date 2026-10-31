import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyAny
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneTableBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvaln
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecodeU

/-! # Kleene interpreter project — interpreter correctness (PROVED) — THE CULMINATION

The explicit memoised DP `buildTableCtx interpBody`, run to rank `cfgRank E B K c0.enc n0 + 1`, produces a
table whose top cell is `encodeOpt (Code.evaln K c0.toCode n0)` — the (encoded) Kleene universal simulation
of any `Code` for `K ≤ B` fuel.  This ties the whole arc together: per-cell correctness (`hbody_dispatch`),
table fill (`buildTableCtx_correct_bounded`), the rank bound (`cfgRank_fuel`), and the `UCode`↔`Code` bridge
(`decode_enc`, `UCode.evaln_eq`).

  `cfgRank_fuel` — decode-fuel of a rank is the fuel.
  `spec_top` — the top cell value `= encodeOpt (Code.evaln K c0.toCode n0)`.
  `universal_interp_table` — `buildTableCtx interpBody` builds the correct table at the diagonal target.

This is an EXPLICIT universal interpreter (vs the opaque `exists_code`).  The remaining work is the head
extraction (one lookup) and the polynomial runtime bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

theorem cfgRank_fuel (E B K ec n : ℕ) (hec : ec < E+1) (hn : n < B+1) :
    cfgRank E B K ec n / (B+1) / (E+1) = K := by
  unfold cfgRank
  rw [Nat.mul_comm (K*(E+1)+ec) (B+1), Nat.mul_add_div (by omega : 0 < B+1), Nat.div_eq_of_lt hn, Nat.add_zero,
      Nat.mul_comm K (E+1), Nat.mul_add_div (by omega : 0 < E+1), Nat.div_eq_of_lt hec, Nat.add_zero]

theorem spec_top (E B K n0 : ℕ) (c0 : UCode) (hcE : c0.enc < E+1) (hn0 : n0 < B+1) :
    specOf E B (cfgRank E B K c0.enc n0) = encodeOpt (Code.evaln K c0.toCode n0) := by
  rw [spec_cfgRank E B K c0.enc n0 hcE hn0, decode_enc, UCode.evaln_eq]

-- the interpreter table at T_top+1 is correctly built
theorem universal_interp_table (E B K n0 : ℕ) (c0 : UCode) (hKB : K ≤ B) (hcE : c0.enc < E+1) (hn0 : n0 < B+1) :
    (buildTableCtx interpBody).eval (Nat.pair (Nat.pair E B) (cfgRank E B K c0.enc n0 + 1))
      = Part.some (encodeList (tableList (specOf E B) (cfgRank E B K c0.enc n0 + 1))) := by
  apply buildTableCtx_correct_bounded interpBody (Nat.pair E B) (specOf E B)
  intro M hM
  apply hbody_any
  -- M ≤ cfgRank E B K c0.enc n0 → M/(B+1)/(E+1) ≤ K ≤ B
  have hle : M ≤ cfgRank E B K c0.enc n0 := by omega
  calc M / (B+1) / (E+1) ≤ cfgRank E B K c0.enc n0 / (B+1) / (E+1) :=
        Nat.div_le_div_right (Nat.div_le_div_right hle)
    _ = K := cfgRank_fuel E B K c0.enc n0 hcE hn0
    _ ≤ B := hKB

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.universal_interp_table
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.spec_top
