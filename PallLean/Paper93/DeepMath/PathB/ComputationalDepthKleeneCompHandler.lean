import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderSome
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReaderAt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneReader
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneIndicators
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncMono

/-!
# Kleene interpreter project — the `comp` handler (PROVED)

The second recursive handler — and the hardest, because `comp` is data-dependent: it reads `eb = evaln b n`
(via `readerCode sndSubCode`), forms `vb = eb - 1` (`predCode`), then reads `evaln a vb` at the *computed*
input `vb`, guarded by `[vb ≤ B]` (since `vb` may exceed the table dimension).  The result is the cased
multiplicative form

  `[n≤k] · isPos(eb) · (if vb≤B then spec(rank a,vb) else 0)`.

The `vb≤B` branch uses the data-dependent reader `reader_at_correct` (= `spec(rank)`); the `vb>B` branch uses
the raw `readerCodeAt_some` zeroed by the guard.  By `encode_comp_step` (with the value-bound discharged) this
equals `encodeOpt (evalnStep … (comp a b) n) = spec N`.

* `comp_eb`, `comp_ea_le`, `compHandler`, `eval_compHandler`.

Honest scope: the `comp` handler (Code-level cased value).  `prec`/`rfind'`, the body, `spec`/`hbody`, the
interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- Read `evaln b n` for the `comp` bundle (`b` = second subcode, at the bundle's `n`). -/
theorem comp_eb (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.comp a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.comp a b).enc n) :
    (readerCode sndSubCode).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair (UCode.comp a b).enc n))) = Part.some (spec (cfgRank E B k b.enc n)) :=
  reader_correct sndSubCode b.enc E B N k n (UCode.comp a b).enc spec (eval_sndSub_comp a b)
    (enc_lt_comp_right a b) hec hn hN

/-- Read `evaln a vb` at the computed `vb`, when `vb ≤ B` (in table range). -/
theorem comp_ea_le (E B N k n vb : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.comp a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.comp a b).enc n)
    (hvbB : vb ≤ B)
    (hvb : (Code.comp predCode (readerCode sndSubCode)).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.comp a b).enc n))) = Part.some vb) :
    (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))).eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.comp a b).enc n)))
      = Part.some (spec (cfgRank E B k a.enc vb)) :=
  reader_at_correct fstSubCode (Code.comp predCode (readerCode sndSubCode)) a.enc vb E B N k n (UCode.comp a b).enc spec (eval_fstSub_comp a b) hvb (enc_lt_comp_left a b) hec hvbB hN

/-- The `comp` handler: data-dependent branch-free computation of the encoded `comp`-result. -/
def compHandler : Code :=
  Code.comp mulCode (Code.pair
    (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right)) (Code.comp Code.left Code.right)))
    (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerCode sndSubCode))
      (Code.comp mulCode (Code.pair
        (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left))))
        (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))))))))

theorem eval_compHandler (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.comp a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.comp a b).enc n) :
    compHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair (UCode.comp a b).enc n)))
      = Part.some ((if n ≤ k then 1 else 0) * ((if spec (cfgRank E B k b.enc n) = 0 then 0 else 1)
          * (if spec (cfgRank E B k b.enc n) - 1 ≤ B
              then spec (cfgRank E B k a.enc (spec (cfgRank E B k b.enc n) - 1)) else 0))) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) (Nat.pair k (Nat.pair (UCode.comp a b).enc n)) with hX
  have heb := comp_eb E B N k n a b spec hec hn hN
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hBv : (Code.comp Code.right (Code.comp Code.left Code.left)).eval X = Part.some B := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hvb : (Code.comp predCode (readerCode sndSubCode)).eval X = Part.some (spec (cfgRank E B k b.enc n) - 1) := by
    rw [comp_eval _ _ _ _ heb, eval_predCode, Nat.pred_eq_sub_one]
  have hleqN : (Code.comp leqIndicatorCode (Code.pair (Code.comp Code.right (Code.comp Code.right Code.right)) (Code.comp Code.left Code.right))).eval X = Part.some (if n ≤ k then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hn2 hk, eval_leqIndicatorCode]
  have hisb : (Code.comp isPosCode (readerCode sndSubCode)).eval X = Part.some (if spec (cfgRank E B k b.enc n) = 0 then 0 else 1) := by
    rw [comp_eval _ _ _ _ heb, eval_isPosCode]
  have hleqVbB : (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))).eval X = Part.some (if spec (cfgRank E B k b.enc n) - 1 ≤ B then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hvb hBv, eval_leqIndicatorCode]
  have hinner : (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))) (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))))).eval X = Part.some (if spec (cfgRank E B k b.enc n) - 1 ≤ B then spec (cfgRank E B k a.enc (spec (cfgRank E B k b.enc n) - 1)) else 0) := by
    by_cases hvbB : spec (cfgRank E B k b.enc n) - 1 ≤ B
    · have hea := comp_ea_le E B N k n (spec (cfgRank E B k b.enc n) - 1) a b spec hec hn hN hvbB hvb
      rw [comp_pair_eval _ _ _ _ _ _ hleqVbB hea, eval_mulCode, if_pos hvbB, if_pos hvbB, one_mul]
    · have hea := readerCodeAt_some fstSubCode (Code.comp predCode (readerCode sndSubCode)) a.enc (spec (cfgRank E B k b.enc n) - 1) E B N k n (UCode.comp a b).enc (tableList spec N) (eval_fstSub_comp a b) hvb
      rw [comp_pair_eval _ _ _ _ _ _ hleqVbB hea, eval_mulCode, if_neg hvbB, if_neg hvbB, zero_mul]
  have hmid : (Code.comp mulCode (Code.pair (Code.comp isPosCode (readerCode sndSubCode)) (Code.comp mulCode (Code.pair (Code.comp leqIndicatorCode (Code.pair (Code.comp predCode (readerCode sndSubCode)) (Code.comp Code.right (Code.comp Code.left Code.left)))) (readerCodeAt fstSubCode (Code.comp predCode (readerCode sndSubCode))))))).eval X = Part.some ((if spec (cfgRank E B k b.enc n) = 0 then 0 else 1) * (if spec (cfgRank E B k b.enc n) - 1 ≤ B then spec (cfgRank E B k a.enc (spec (cfgRank E B k b.enc n) - 1)) else 0)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hisb hinner, eval_mulCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hleqN hmid, eval_mulCode]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_compHandler
