import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyBase

/-! # Kleene interpreter project — tag-≥8 default hbody case (PROVED)

For `ec` with tag `≥ 8` (malformed), `decodeU ec = zero` (the `_` branch) and the dispatch routes to the
padding `baseAdapt zeroHandler` — which computes `specOf` (`= encodeOpt (UCode.evaln (k+1) zero n)`).
`decodeU_default`, `hbody_default_case`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

theorem decodeU_default (ec : ℕ) (htag : 8 ≤ (Nat.unpair ec).1) : decodeU ec = UCode.zero := by
  conv_lhs => rw [decodeU]
  split <;> first | rfl | omega

theorem hbody_default_case (E B k' n ec : ℕ) (htag : 8 ≤ (Nat.unpair ec).1) (hec : ec ≤ E) (hn : n ≤ B) :
    (baseAdapt zeroHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  rw [eval_baseAdapt zeroHandler E B (cfgRank E B (k'+1) ec n) k' n ec (specOf E B), eval_zeroHandler,
      spec_cfgRank E B (k'+1) ec n (by omega) (by omega), decodeU_default ec htag, uevaln_zero]
  by_cases h : n ≤ k' <;> simp [h, encodeOpt]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_default_case
