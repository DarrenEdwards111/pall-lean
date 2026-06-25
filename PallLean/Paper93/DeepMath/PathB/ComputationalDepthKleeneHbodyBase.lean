import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneInterpBody
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSpec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvalnEqs
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodeOpt

/-!
# Kleene interpreter project — `hbody` base cases (PROVED)

The four leaf constructors (`zero`/`succ`/`left`/`right`).  Each is dispatched to `baseAdapt h` (which feeds
the leaf handler `pair (k-1) n` — the guard convention), and the handler's encoded value matches `specOf`
(`= encodeOpt (UCode.evaln (k'+1) (decodeU ec) n)`) directly, with no sub-ranks or value bounds.

  `eval_baseAdapt` — `(baseAdapt h).eval bundle = h.eval (pair k' n)`.
  `decodeU_tag0..3`, `hbody_zero/succ/left/right_case`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- A base handler wrapped by `baseAdapt`, on the bundle, evaluates the leaf handler at `pair k' n`. -/
theorem eval_baseAdapt (h : Code) (E B N k' n ec : ℕ) (spec : ℕ → ℕ) :
    (baseAdapt h).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = h.eval (Nat.pair k' n) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair (k'+1) (Nat.pair ec n)) with hX
  have hk : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some k' := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.right).eval X = Part.some (k'+1) from by rw [hX]; simp [Code.eval, Nat.unpair_pair]), eval_predCode]; simp
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  show (Code.comp h (Code.pair _ _)).eval X = _
  rw [comp_eval _ _ _ _ (pair_eval _ _ _ _ _ hk hn2)]

theorem decodeU_tag0 (ec : ℕ) (htag : (Nat.unpair ec).1 = 0) : decodeU ec = UCode.zero := by
  conv_lhs => rw [decodeU, htag]
theorem decodeU_tag1 (ec : ℕ) (htag : (Nat.unpair ec).1 = 1) : decodeU ec = UCode.succ := by
  conv_lhs => rw [decodeU, htag]
theorem decodeU_tag2 (ec : ℕ) (htag : (Nat.unpair ec).1 = 2) : decodeU ec = UCode.left := by
  conv_lhs => rw [decodeU, htag]
theorem decodeU_tag3 (ec : ℕ) (htag : (Nat.unpair ec).1 = 3) : decodeU ec = UCode.right := by
  conv_lhs => rw [decodeU, htag]

theorem hbody_zero_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 0) (hec : ec ≤ E) (hn : n ≤ B) :
    (baseAdapt zeroHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  rw [eval_baseAdapt zeroHandler E B (cfgRank E B (k'+1) ec n) k' n ec (specOf E B), eval_zeroHandler,
      spec_cfgRank E B (k'+1) ec n (by omega) (by omega), decodeU_tag0 ec htag, uevaln_zero]
  by_cases h : n ≤ k' <;> simp [h, encodeOpt]

theorem hbody_succ_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 1) (hec : ec ≤ E) (hn : n ≤ B) :
    (baseAdapt succHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  rw [eval_baseAdapt succHandler E B (cfgRank E B (k'+1) ec n) k' n ec (specOf E B), eval_succHandler,
      spec_cfgRank E B (k'+1) ec n (by omega) (by omega), decodeU_tag1 ec htag, uevaln_succ]
  by_cases h : n ≤ k' <;> simp [h, encodeOpt]

theorem hbody_left_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 2) (hec : ec ≤ E) (hn : n ≤ B) :
    (baseAdapt leftHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  rw [eval_baseAdapt leftHandler E B (cfgRank E B (k'+1) ec n) k' n ec (specOf E B), eval_leftHandler,
      spec_cfgRank E B (k'+1) ec n (by omega) (by omega), decodeU_tag2 ec htag, uevaln_left]
  by_cases h : n ≤ k' <;> simp [h, encodeOpt]

theorem hbody_right_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 3) (hec : ec ≤ E) (hn : n ≤ B) :
    (baseAdapt rightHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  rw [eval_baseAdapt rightHandler E B (cfgRank E B (k'+1) ec n) k' n ec (specOf E B), eval_rightHandler,
      spec_cfgRank E B (k'+1) ec n (by omega) (by omega), decodeU_tag3 ec htag, uevaln_right]
  by_cases h : n ≤ k' <;> simp [h, encodeOpt]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_zero_case
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_right_case
