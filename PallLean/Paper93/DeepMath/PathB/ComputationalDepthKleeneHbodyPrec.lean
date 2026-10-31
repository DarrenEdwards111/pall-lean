import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecHandlerGen
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSpec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneUEvalnEqs
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEncodePrecRfind
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyRfind

/-! # Kleene interpreter project — `hbody` prec case (PROVED) — the hardest case

The `prec` constructor`s per-cell correctness, completing all nine cases.  `prec` is a `casesOn` on `n2`
whose step is a nested `comp`-like (`evaln k' prec … >>= evaln (k'+1) b …`) with TWO value bounds (self
at fuel `k'`, b-call at fuel `k'+1`), both from `k' ≤ B`.  `encodeOpt_bind` + `prec_step_conn` connect the
step to `encodeOpt`; `casesOn_eq_if` + `encode_prec_step` handle the selector.  Nothing here is `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank cfgRank_lt_code)

theorem encodeOpt_bind (ob : Option ℕ) (oaf : ℕ → Option ℕ) :
    encodeOpt (ob >>= oaf) = (if encodeOpt ob = 0 then 0 else 1) * encodeOpt (oaf (encodeOpt ob - 1)) := by
  cases ob with
  | none => simp [encodeOpt]
  | some vb => have hb : (some vb : Option ℕ) >>= oaf = oaf vb := rfl
               rw [hb]; simp only [show encodeOpt (some vb) = vb + 1 from rfl, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero vb), one_mul]

theorem casesOn_eq_if {α : Sort _} (n2 : ℕ) (a : α) (g : ℕ → α) :
    n2.casesOn a g = if n2 = 0 then a else g (n2 - 1) := by
  cases n2 with
  | zero => simp
  | succ m => simp

theorem decodeU_tag6 (ec : ℕ) (htag : (Nat.unpair ec).1 = 6) :
    decodeU ec = UCode.prec (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) := by
  conv_lhs => rw [decodeU, htag]

-- the step connection: stepval = encodeOpt os
theorem prec_step_conn (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 6) (hec : ec ≤ E) (hn : n ≤ B) (hkB : k' ≤ B)
    (ev cmp : ℕ)
    (hev : ev = (if Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B then specOf E B (cfgRank E B k' ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) else 0))
    (hcmp : cmp = Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1))) :
    (if ev = 0 then 0 else 1) * (if cmp ≤ B then specOf E B (cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0)
      = encodeOpt (UCode.evaln k' (UCode.prec (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2)) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))
          >>= fun i => UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) (Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) i))) := by
  have hsbE : (Nat.unpair (Nat.unpair ec).2).2 < E + 1 := lt_of_lt_of_le (sndSub_lt ec (by omega)) (by omega)
  rw [encodeOpt_bind]
  -- ev = encodeOpt ob
  have hevob : ev = encodeOpt (UCode.evaln k' (UCode.prec (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2)) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1))) := by
    rw [hev]; by_cases hpm : Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1) ≤ B
    · rw [if_pos hpm, spec_cfgRank E B k' ec (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) (by omega) (by omega), decodeU_tag6 ec htag]
    · rw [if_neg hpm, uevaln_none_of_le k' (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) _ (by omega)]; simp [encodeOpt]
  rw [← hevob, hcmp]
  -- b-part
  by_cases hcB : Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1)) ≤ B
  · rw [if_pos hcB, spec_cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).2 (Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1))) hsbE (by omega)]
  · rw [if_neg hcB, uevaln_none_of_gt k' (Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) (ev - 1))) _ (by omega)]; simp [encodeOpt]
#print axioms prec_step_conn

theorem hbody_prec_case (E B k' n ec : ℕ) (htag : (Nat.unpair ec).1 = 6) (hec : ec ≤ E) (hn : n ≤ B) (hkB : k' ≤ B) :
    precHandler.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)))
      = Part.some (specOf E B (cfgRank E B (k'+1) ec n)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B (k'+1) ec n) (encodeList (tableList (specOf E B) (cfgRank E B (k'+1) ec n))))) (Nat.pair (k'+1) (Nat.pair ec n)) with hX
  have hnB : n < B + 1 := by omega
  have hsaE : (Nat.unpair (Nat.unpair ec).2).1 < E + 1 := lt_of_lt_of_le (fstSub_lt ec (by omega)) (by omega)
  obtain ⟨ev, cmp, hev, hcmp, hstep⟩ := eval_precStep_gen E B (cfgRank E B (k'+1) ec n) (k'+1) n ec (specOf E B) (by omega) hec hn rfl (by omega)
  rw [← hX] at hstep
  have hnExt : nExtract.eval X = Part.some n := by show (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = _; rw [hX]; simp [nExtract, Code.eval, Nat.unpair_pair]
  have hn2v : n2Src.eval X = Part.some (Nat.unpair n).2 := by show (Code.comp Code.right nExtract).eval X = _; rw [comp_eval _ _ _ _ hnExt]; simp [Code.eval]
  have hn1v : n1Src.eval X = Part.some (Nat.unpair n).1 := by show (Code.comp Code.left nExtract).eval X = _; rw [comp_eval _ _ _ _ hnExt]; simp [Code.eval]
  have hkpv : (Code.comp predCode (Code.comp Code.left Code.right)).eval X = Part.some k' := by
    rw [comp_eval _ _ _ _ (show (Code.comp Code.left Code.right).eval X = Part.some (k'+1) from by rw [hX]; simp [Code.eval, Nat.unpair_pair]), eval_predCode]; simp
  have hk : (Code.comp Code.left Code.right).eval X = Part.some (k'+1) := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hguard : (Code.comp leqIndicatorCode (Code.pair nExtract (Code.comp predCode (Code.comp Code.left Code.right)))).eval X = Part.some (if n ≤ k' then 1 else 0) := by
    rw [comp_pair_eval _ _ _ _ _ _ hnExt hkpv, eval_leqIndicatorCode]
  have hbase : (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src).eval X = Part.some (specOf E B (cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1)) := by
    have := reader_gen_correct fstSubCode (Code.comp Code.left Code.right) n1Src (Nat.unpair (Nat.unpair ec).2).1 (k'+1) (Nat.unpair n).1 E B (cfgRank E B (k'+1) ec n) (k'+1) n ec (specOf E B) (eval_fstSub_gen ec) hk hn1v (cfgRank_lt_code E B (k'+1) ec (Nat.unpair (Nat.unpair ec).2).1 n (Nat.unpair n).1 (fstSub_lt ec (by omega)) hec (le_trans (Nat.unpair_left_le n) hn))
    rwa [← hX] at this
  have hizN2 : (Code.comp isZeroCode n2Src).eval X = Part.some (if (Nat.unpair n).2 = 0 then 1 else 0) := by rw [comp_eval _ _ _ _ hn2v, eval_isZeroCode]
  have hipN2 : (Code.comp isPosCode n2Src).eval X = Part.some (if (Nat.unpair n).2 = 0 then 0 else 1) := by rw [comp_eval _ _ _ _ hn2v, eval_isPosCode]
  have ht1 : (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 1 else 0) * specOf E B (cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1)) := by
    rw [comp_pair_eval _ _ _ _ _ _ hizN2 hbase, eval_mulCode]
  have ht2 : (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 0 else 1) * ((if ev = 0 then 0 else 1) * (if cmp ≤ B then specOf E B (cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ hipN2 hstep, eval_mulCode]
  have hsel : (Code.comp addCode (Code.pair (Code.comp mulCode (Code.pair (Code.comp isZeroCode n2Src) (readerGen fstSubCode (Code.comp Code.left Code.right) n1Src))) (Code.comp mulCode (Code.pair (Code.comp isPosCode n2Src) precStepCode)))).eval X = Part.some ((if (Nat.unpair n).2 = 0 then 1 else 0) * specOf E B (cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1) + (if (Nat.unpair n).2 = 0 then 0 else 1) * ((if ev = 0 then 0 else 1) * (if cmp ≤ B then specOf E B (cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).2 cmp) else 0))) := by
    rw [comp_pair_eval _ _ _ _ _ _ ht1 ht2, eval_addCode]
  show (Code.comp mulCode (Code.pair _ _)).eval X = _
  rw [comp_pair_eval _ _ _ _ _ _ hguard hsel, eval_mulCode]
  -- connection: selector = specOf N
  rw [spec_cfgRank E B (k'+1) (Nat.unpair (Nat.unpair ec).2).1 (Nat.unpair n).1 hsaE (lt_of_le_of_lt (Nat.unpair_left_le n) hnB)]
  rw [prec_step_conn E B k' n ec htag hec hn hkB ev cmp hev hcmp]
  rw [spec_cfgRank E B (k'+1) ec n (by omega) hnB, decodeU_tag6 ec htag, uevaln_prec k' n, casesOn_eq_if,
      encode_prec_step k' n (Nat.unpair n).2 (UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).1) (Nat.unpair n).1) (UCode.evaln k' (UCode.prec (decodeU (Nat.unpair (Nat.unpair ec).2).1) (decodeU (Nat.unpair (Nat.unpair ec).2).2)) (Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2 - 1)) >>= fun i => UCode.evaln (k'+1) (decodeU (Nat.unpair (Nat.unpair ec).2).2) (Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2 - 1) i)))]
#print axioms hbody_prec_case

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_prec_case
