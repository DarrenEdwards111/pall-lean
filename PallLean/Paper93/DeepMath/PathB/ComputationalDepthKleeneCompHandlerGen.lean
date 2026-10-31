import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCompHandler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderAt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReader
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGenExtract

/-! # Kleene interpreter project — the generic `comp` handler (PROVED)

The `comp` handler for arbitrary `ec` (tag-5 path): same data-dependent + value-bound proof as
`eval_compHandler`, but the readers use the general extraction (`eval_sndSub_gen`+`sndSub_lt` for `eb`,
`eval_fstSub_gen`+`fstSub_lt` for the data-dependent `a`-lookup) instead of the valid-`ec` versions.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

theorem eval_compHandler_gen (E B N k n ec : ℕ) (spec : ℕ → ℕ)
    (htag : 1 ≤ (Nat.unpair ec).1) (hec : ec ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k ec n) :
    compHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair ec n)))
      = Part.some ((if n ≤ k - 1 then 1 else 0)
          * ((if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) = 0 then 0 else 1)
            * (if spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) - 1 ≤ B
                then spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).1 (spec (cfgRank E B k (Nat.unpair (Nat.unpair ec).2).2 n) - 1)) else 0))) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair ec n)) with hX
  set sb := (Nat.unpair (Nat.unpair ec).2).2 with hsb
  set sa := (Nat.unpair (Nat.unpair ec).2).1 with hsa
  have heb : (readerCode sndSubCode).eval X = Part.some (spec (cfgRank E B k sb n)) := by
    have := reader_correct sndSubCode sb E B N k n ec spec (eval_sndSub_gen ec) (sndSub_lt ec htag) hec hn hN
    rwa [← hX] at this
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hBv : (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = Part.some B := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hkp : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some (k - 1) := by
    rw [comp_eval _ _ _ _ hk, eval_predCode, Nat.pred_eq_sub_one]
  have hvb : (Code.comp predCode (readerCode sndSubCode)).eval X = Part.some (spec (cfgRank E B k sb n) - 1) := by
    rw [comp_eval _ _ _ _ heb, eval_predCode, Nat.pred_eq_sub_one]
  have hleqN : (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right)) (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k - 1 then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hn2 hkp, eval_leqIndicatorCode]
  have hisb : (Code.comp isPosCode (readerCode sndSubCode)).eval X = Part.some (if spec (cfgRank E B k sb n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ heb, eval_isPosCode]
  have hleqVbB : (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))).eval X = Part.some (if spec (cfgRank E B k sb n) - 1 ≤ B then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hvb hBv, eval_leqIndicatorCode]
  have hinner : (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))) (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))))).eval X = Part.some (if spec (cfgRank E B k sb n) - 1 ≤ B then spec (cfgRank E B k sa (spec (cfgRank E B k sb n) - 1)) else 0) := by
    by_cases hvbB : spec (cfgRank E B k sb n) - 1 ≤ B
    · have hea := reader_at_correct fstSubCode (Code.comp predCode (readerCode sndSubCode)) sa (spec (cfgRank E B k sb n) - 1) E B N k n ec spec (eval_fstSub_gen ec) (hX ▸ hvb) (fstSub_lt ec htag) hec hvbB hN
      rw [← hX] at hea
      rw [comp_pair_eval _ _ _ _ _ _ hleqVbB hea, eval_mulCode, if_pos hvbB, if_pos hvbB, one_mul]
    · have hea := readerCodeAt_some fstSubCode (Code.comp predCode (readerCode sndSubCode)) sa (spec (cfgRank E B k sb n) - 1) E B N k n ec (tableList spec N) (eval_fstSub_gen ec) (hX ▸ hvb)
      rw [← hX] at hea
      rw [comp_pair_eval _ _ _ _ _ _ hleqVbB hea, eval_mulCode, if_neg hvbB, if_neg hvbB, zero_mul]
  have hmid : (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerCode sndSubCode)) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))) (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))))))).eval X = Part.some ((if spec (cfgRank E B k sb n) = 0 then 0 else 1) * (if spec (cfgRank E B k sb n) - 1 ≤ B then spec (cfgRank E B k sa (spec (cfgRank E B k sb n) - 1)) else 0)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hisb hinner, eval_mulCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hleqN hmid, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_compHandler_gen
