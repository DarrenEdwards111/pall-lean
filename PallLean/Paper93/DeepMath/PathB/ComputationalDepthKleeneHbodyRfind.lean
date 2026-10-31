import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRfindHandlerGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSpec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvalnEqs
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodePrecRfind

/-! # Kleene interpreter project — `hbody` rfind' case (PROVED, fuel bound)

The `rfind'` constructor`s per-cell correctness.  Its `a`-call is at `n` (= `pair (unpair n).1 (unpair
n).2`, via `Nat.pair_unpair`); the recursive call is at lower fuel `k'` and input `pair n1 (m+1)` (guarded
`[· ≤ B]`).  The value bound (`uevaln_none_of_le`, covering fuel `0`) discharges the out-of-range branch
from `k' ≤ B`.  `encode_rfind_step` matches the form to `specOf`.  `uevaln_none_of_le`, `decodeU_tag7`,
`hbody_rfind_case`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

theorem uevaln_none_of_le (kk input : ℕ) (c : UCode) (h : kk ≤ input) : UCode.evaln kk c input = Option.none := by
  cases kk with
  | zero => cases c <;> simp [UCode.evaln]
  | succ k'' => exact uevaln_none_of_gt k'' input c (by omega)

theorem decodeU_tag7 (ec : ℕ) (htag : (Nat.unpair ec).1 = 7) :
    decodeU ec = UCode.rfind' (decodeU (Nat.unpair ec).2) := by
  conv_lhs => rw [decodeU, htag]

theorem hbody_rfind_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 7) (hec : ec ≤ E) (hn : n ≤ B) (hkB : k' ≤ B) :
    rfindHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  have hnB : n < B + 1 := by omega
  have haE : (Nat.unpair ec).2 < E + 1 := lt_of_lt_of_le (rfindSub_lt ec (by omega)) (by omega)
  have hself : (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B then specOf E B (cfgRank E B k' ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) else 0)
      = encodeOpt (UCode.evaln k' (UCode.rfind' (decodeU (Nat.unpair ec).2)) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1))) := by
    by_cases hc : Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1) ≤ B
    · rw [if_pos hc, spec_cfgRank E B k' ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) (by omega) (by omega), decodeU_tag7 ec htag]
    · rw [if_neg hc, uevaln_none_of_le k' (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)) (UCode.rfind' (decodeU (Nat.unpair ec).2)) (by omega)]; simp [encodeOpt]
  rw [eval_rfindHandler_gen E B (cfgRank E B (k'+1) ec n) (k'+1) n ec (specOf E B) (by omega) hec hn rfl (by omega)]
  rw [spec_cfgRank E B (k'+1) (Nat.unpair ec).2 n haE hnB]
  simp only [Nat.add_sub_cancel]
  rw [hself]
  rw [spec_cfgRank E B (k'+1) ec n (by omega) hnB, decodeU_tag7 ec htag, uevaln_rfind k' n, Nat.pair_unpair,
      encode_rfind_step k' n (Nat.unpair n).2 (UCode.evaln (k'+1) (decodeU (Nat.unpair ec).2) n) (UCode.evaln k' (UCode.rfind' (decodeU (Nat.unpair ec).2)) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 + 1)))]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_rfind_case
