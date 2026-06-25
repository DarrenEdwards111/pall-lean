import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCompHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderGenSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract

/-! # Kleene interpreter project — comp handler totality (.Dom) (PROVED)

The `comp` handler is total on the bundle (data-dependent reader via `readerCodeAt_some`, self/eb via
`readerGen_some`, + total arithmetic).  `compHandler_dom`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

theorem compHandler_dom (E B N k n ec : ℕ) (L : List ℕ) :
    (compHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)) with hX
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hBv : (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = Part.some B := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hkp : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k-1) := by rw [comp_eval _ _ _ _ hk, eval_predCode, Nat.pred_eq_sub_one]
  obtain ⟨veb, heb⟩ : ∃ v, (readerCode sndSubCode).eval X = Part.some v :=
    ⟨_, by have h := readerGen_some sndSubCode (Code.comp Code.left Code.right) (Code.comp Code.right (Code.comp Code.right Code.right)) (Nat.unpair (Nat.unpair ec).2).2 k n E B N k n ec L (eval_sndSub_gen ec) (hX ▸ hk) (hX ▸ hn2); rw [← hX] at h; exact h⟩
  have hvb : (Code.comp predCode (readerCode sndSubCode)).eval X = Part.some (veb - 1) := by rw [comp_eval _ _ _ _ heb, eval_predCode, Nat.pred_eq_sub_one]
  obtain ⟨vea, hea⟩ : ∃ v, (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))).eval X = Part.some v :=
    ⟨_, by have h := readerCodeAt_some fstSubCode (Code.comp predCode (readerCode sndSubCode)) (Nat.unpair (Nat.unpair ec).2).1 (veb - 1) E B N k n ec L (eval_fstSub_gen ec) (hX ▸ hvb); rw [← hX] at h; exact h⟩
  have hleqN : (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right)) (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by rw [comp_pair_eval _ _ _ _ _ _ hn2 hkp, eval_leqIndicatorCode]
  have hisb : (Code.comp isPosCode (readerCode sndSubCode)).eval X = Part.some (if veb = 0 then 0 else 1) := by rw [comp_eval _ _ _ _ heb, eval_isPosCode]
  have hleqVbB : (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))).eval X = Part.some (if veb - 1 ≤ B then 1 else 0) := by rw [comp_pair_eval _ _ _ _ _ _ hvb hBv, eval_leqIndicatorCode]
  have hinner : (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))) (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))))).eval X = Part.some ((if veb - 1 ≤ B then 1 else 0) * vea) := by rw [comp_pair_eval _ _ _ _ _ _ hleqVbB hea, eval_mulCode]
  have hmid : (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerCode sndSubCode)) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))) (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))))))).eval X = Part.some ((if veb = 0 then 0 else 1) * ((if veb - 1 ≤ B then 1 else 0) * vea)) := by rw [comp_pair_eval _ _ _ _ _ _ hisb hinner, eval_mulCode]
  show ((Code.comp mulCode (Code.pair _ _)).eval X).Dom
  rw [comp_pair_eval _ _ _ _ _ _ hleqN hmid, eval_mulCode]; trivial

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.compHandler_dom
