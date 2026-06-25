import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePairHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGenSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract

/-! # Kleene interpreter project — pair reader/handler totality (PROVED)

`mkDispatch` requires every handler to be `.Dom` on the bundle (it is total — readers via `readerGen_some`
+ total arithmetic).  These are the totality lemmas for the pair reader/handler; the other recursive
handlers follow the same pattern.  `eaCode_some`, `ebCode_some`, `pairHandler_dom`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

theorem eaCode_some (E B N k n ec : ℕ) (L : List ℕ) :
    ∃ v, eaCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n))) = Part.some v := by
  have hk : (Code.comp Code.left Code.right).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n))) = Part.some k := by simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n))) = Part.some n := by simp [Code.eval, Nat.unpair_pair]
  exact ⟨_, readerGen_some fstSubCode (Code.comp Code.left Code.right) (Code.comp Code.right (Code.comp Code.right Code.right)) (Nat.unpair (Nat.unpair ec).2).1 k n E B N k n ec L (eval_fstSub_gen ec) hk hn2⟩
theorem ebCode_some (E B N k n ec : ℕ) (L : List ℕ) :
    ∃ v, ebCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n))) = Part.some v := by
  have hk : (Code.comp Code.left Code.right).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n))) = Part.some k := by simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n))) = Part.some n := by simp [Code.eval, Nat.unpair_pair]
  exact ⟨_, readerGen_some sndSubCode (Code.comp Code.left Code.right) (Code.comp Code.right (Code.comp Code.right Code.right)) (Nat.unpair (Nat.unpair ec).2).2 k n E B N k n ec L (eval_sndSub_gen ec) hk hn2⟩

theorem pairHandler_dom (E B N k n ec : ℕ) (L : List ℕ) :
    (pairHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)) with hX
  obtain ⟨va, hva⟩ := eaCode_some E B N k n ec L
  obtain ⟨vb, hvb⟩ := ebCode_some E B N k n ec L
  rw [← hX] at hva hvb
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hkp : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k-1) := by rw [comp_eval _ _ _ _ hk, eval_predCode, Nat.pred_eq_sub_one]
  have hleq : (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right)) (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by rw [comp_pair_eval _ _ _ _ _ _ hn2 hkp, eval_leqIndicatorCode]
  have hpa : (Code.comp isPosCode eaCode).eval X = Part.some (if va = 0 then 0 else 1) := by rw [comp_eval _ _ _ _ hva, eval_isPosCode]
  have hpb : (Code.comp isPosCode ebCode).eval X = Part.some (if vb = 0 then 0 else 1) := by rw [comp_eval _ _ _ _ hvb, eval_isPosCode]
  have hpf : (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))).eval X = Part.some (Nat.pair (va - 1) (vb - 1) + 1) := by
    rw [comp_eval _ _ _ _ (pair_eval _ _ _ _ _ (by rw [comp_eval _ _ _ _ hva, eval_predCode, Nat.pred_eq_sub_one]) (by rw [comp_eval _ _ _ _ hvb, eval_predCode, Nat.pred_eq_sub_one]))]; simp [Code.eval]
  have hm3 : (Code.comp mulCode (Code.pair (Code.comp isPosCode ebCode) (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))))).eval X = Part.some ((if vb = 0 then 0 else 1) * (Nat.pair (va - 1) (vb - 1) + 1)) := by rw [comp_pair_eval _ _ _ _ _ _ hpb hpf, eval_mulCode]
  have hm2 : (Code.comp mulCode (Code.pair (Code.comp isPosCode eaCode) (Code.comp mulCode (Code.pair (Code.comp isPosCode ebCode) (Code.comp Code.succ (Code.pair (Code.comp predCode eaCode) (Code.comp predCode ebCode))))))).eval X = Part.some ((if va = 0 then 0 else 1) * ((if vb = 0 then 0 else 1) * (Nat.pair (va - 1) (vb - 1) + 1))) := by rw [comp_pair_eval _ _ _ _ _ _ hpa hm3, eval_mulCode]
  show ((Code.comp mulCode (Code.pair _ _)).eval X).Dom
  rw [comp_pair_eval _ _ _ _ _ _ hleq hm2, eval_mulCode]; trivial

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.pairHandler_dom
