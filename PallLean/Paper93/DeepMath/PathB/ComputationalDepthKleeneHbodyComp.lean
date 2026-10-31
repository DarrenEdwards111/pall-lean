import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCompHandlerGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSpec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvalnEqs
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeComp

/-! # Kleene interpreter project — `hbody` comp case (PROVED, with fuel bound)

The `comp` constructor`s per-cell correctness.  Unlike `pair`, `comp` reads its second result at the
data-dependent input `vb` (b`s output), which can exceed `B`; so the handler is `B`-guarded and matches
`specOf` only when the value bound `hB : vb > B → UCode.evaln (k`+1) uA vb = none` holds — discharged from
the fuel bound `k` ≤ B` via `uevaln_none_of_gt` (`vb > B ≥ k` ⇒ guard fails).  `encode_comp_step` then
matches the handler`s multiplicative form to `encodeOpt (UCode.evaln (k`+1) (comp uA uB) n) = specOf`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

theorem decodeU_tag5 (ec : ℕ) (htag : (Nat.unpair ec).1 = 5) :
    decodeU ec = UCode.comp (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) := by
  conv_lhs => rw [decodeU, htag]

theorem hbody_comp_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 5) (hec : ec ≤ E) (hn : n ≤ B) (hkB : k' ≤ B) :
    compHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  have hnB : n < B + 1 := by omega
  have hsbE : (Nat.unpair (Nat.unpair ec).2).2 < E + 1 := lt_of_lt_of_le (sndSub_lt ec (by omega)) (by omega)
  have hsaE : (Nat.unpair (Nat.unpair ec).2).1 < E + 1 := lt_of_lt_of_le (fstSub_lt ec (by omega)) (by omega)
  have hB : ∀ vb, B < vb → UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).1) vb = Option.none :=
    fun vb hvb => uevaln_none_of_gt k' vb (decodeU (Nat.unpair (Nat.unpair ec).2).1) (by omega)
  rw [eval_compHandler_gen E B (cfgRank E B (k'+1) ec n) (k'+1) n ec (specOf E B) (by omega) hec hn rfl]
  rw [spec_cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).2 n hsbE hnB]
  rw [spec_cfgRank E B (k'+1) ec n (by omega) hnB, decodeU_tag5 ec htag, uevaln_comp k' n,
      encode_comp_step k' n B (UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) n) (fun x => UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).1) x) hB]
  simp only [Nat.add_sub_cancel]
  by_cases hc : encodeOpt (UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) n) - 1 ≤ B
  · rw [if_pos hc, if_pos hc, one_mul, spec_cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).1 (encodeOpt (UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) n) - 1) hsaE (by omega)]
  · rw [if_neg hc, if_neg hc, zero_mul]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_comp_case
