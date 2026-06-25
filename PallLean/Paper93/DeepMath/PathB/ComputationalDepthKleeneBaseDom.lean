import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneInterpBody
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneBaseHandlers

/-! # Kleene interpreter project — base handler totality (.Dom) (PROVED)

The four `baseAdapt`-wrapped base handlers are total (a base handler is total, and `baseAdapt` feeds
it `pair (k-1) n`).  `baseAdapt_eval_any`, `baseAdapt_zero/succ/left/right_dom`.  With the 4 recursive
doms this completes the `.Dom` hypothesis `mkDispatch` needs.  Nothing here is `NEXP ⊄ ACC⁰`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

theorem baseAdapt_eval_any (h : Code) (E B N k n ec : ℕ) (L : List ℕ) :
    (baseAdapt h).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))
      = h.eval (Nat.pair (k - 1) n) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)) with hX
  have hkp : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.right).eval X = Part.some k from by rw [hX]; simp [Code.eval, Nat.unpair_pair]), eval_predCode, Nat.pred_eq_sub_one]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  show (Code.comp h (Code.pair _ _)).eval X = _
  rw [comp_eval _ _ _ _ (pair_eval _ _ _ _ _ hkp hn2)]

theorem baseAdapt_zero_dom (E B N k n ec : ℕ) (L : List ℕ) : ((baseAdapt zeroHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by rw [baseAdapt_eval_any, eval_zeroHandler]; trivial
theorem baseAdapt_succ_dom (E B N k n ec : ℕ) (L : List ℕ) : ((baseAdapt succHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by rw [baseAdapt_eval_any, eval_succHandler]; trivial
theorem baseAdapt_left_dom (E B N k n ec : ℕ) (L : List ℕ) : ((baseAdapt leftHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by rw [baseAdapt_eval_any, eval_leftHandler]; trivial
theorem baseAdapt_right_dom (E B N k n ec : ℕ) (L : List ℕ) : ((baseAdapt rightHandler).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by rw [baseAdapt_eval_any, eval_rightHandler]; trivial

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.baseAdapt_zero_dom
