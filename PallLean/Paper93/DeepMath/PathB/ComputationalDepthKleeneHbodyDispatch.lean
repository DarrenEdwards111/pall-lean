import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispCodes
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyPair
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyComp
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyPrec
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyRfind
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyBase
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneHbodyDefault
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch8

/-! # Kleene interpreter project — the dispatch hbody (PROVED) — the keystone

`interpBody` computes `specOf E B (cfgRank E B k ec n)` for every config (given `k ≤ B`): decode the rank,
zero out fuel-0 (`isPos k`), then `mkDispatch` over the 9 totality-verified handlers selects the right one
(`capCode` clamps the tag), and each per-cell case (`hbody_pair_case`, …, the tag-≥8 default) closes it.
This is the per-cell correctness `buildTableCtx_correct` needs.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

set_option maxHeartbeats 1000000 in
theorem hbody_dispatch (E B k ec n : ℕ) (hec : ec ≤ E) (hn : n ≤ B) (hkB : k ≤ B) :
    interpBody.eval (Nat.pair (Nat.pair E B) (Nat.pair (cfgRank E B k ec n) (encodeList (tableList (specOf E B) (cfgRank E B k ec n)))))
      = Part.some (specOf E B (cfgRank E B k ec n)) := by
  set N := cfgRank E B k ec n with hNdef
  set INPUT := Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList (specOf E B) N))) with hI
  set BUNDLE := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList (specOf E B) N)))) (Nat.pair k (Nat.pair ec n)) with hBU
  have hdec : decodedSrc.eval INPUT = Part.some (Nat.pair k (Nat.pair ec n)) := by
    show (Code.comp decodeRankCode (Code.pair Code.left (Code.comp Code.left Code.right))).eval INPUT = _
    have hctx : (Code.left : Code).eval INPUT = Part.some (Nat.pair E B) := by rw [hI]; simp [Code.eval, Nat.unpair_pair]
    have hNe : (Code.comp Code.left Code.right).eval INPUT = Part.some N := by rw [hI]; simp [Code.eval, Nat.unpair_pair]
    rw [comp_eval _ _ _ _ (pair_eval _ _ _ _ _ hctx hNe), hNdef, eval_decodeRankCode E B k ec n (by omega) (by omega)]
  have hk : kSrcBody.eval INPUT = Part.some k := by show (Code.comp Code.left decodedSrc).eval INPUT = _; rw [comp_eval _ _ _ _ hdec]; simp [Code.eval, Nat.unpair_pair]
  have hbun : bundleSrc.eval INPUT = Part.some BUNDLE := by show (Code.pair idCode decodedSrc).eval INPUT = _; rw [hBU]; exact pair_eval _ _ _ _ _ (eval_idCode INPUT) hdec
  have hrd : (Code.comp Code.right decodedSrc).eval INPUT = Part.some (Nat.pair ec n) := by rw [comp_eval _ _ _ _ hdec]; simp [Code.eval, Nat.unpair_pair]
  have hecs : (Code.comp Code.left (Code.comp Code.right decodedSrc)).eval INPUT = Part.some ec := by rw [comp_eval _ _ _ _ hrd]; simp [Code.eval, Nat.unpair_pair]
  have htag : tagSrc.eval INPUT = Part.some (Nat.unpair ec).1 := by show (Code.comp Code.left (Code.comp Code.left (Code.comp Code.right decodedSrc))).eval INPUT = _; rw [comp_eval _ _ _ _ hecs]; simp [Code.eval]
  have hcap : (Code.comp capCode tagSrc).eval INPUT = Part.some (min (Nat.unpair ec).1 8) := by rw [comp_eval _ _ _ _ htag, eval_capCode]
  have hpair2 : (Code.pair bundleSrc (Code.comp capCode tagSrc)).eval INPUT = Part.some (Nat.pair BUNDLE (min (Nat.unpair ec).1 8)) := pair_eval _ _ _ _ _ hbun hcap
  have hdisp : (Code.comp (mkDispatch dispCodes) (Code.pair bundleSrc (Code.comp capCode tagSrc))).eval INPUT = (dispCodes.getD (min (Nat.unpair ec).1 8) Code.zero).eval BUNDLE := by
    rw [comp_eval _ _ _ _ hpair2, eval_mkDispatch BUNDLE dispCodes (dispCodes_dom E B N k n ec (tableList (specOf E B) N)) (min (Nat.unpair ec).1 8) (by simp only [dispCodes, List.length_cons, List.length_nil]; omega)]
  have hA : (Code.comp isPosCode kSrcBody).eval INPUT = Part.some (if k = 0 then 0 else 1) := by rw [comp_eval _ _ _ _ hk, eval_isPosCode]
  show (Code.comp mulCode (Code.pair (Code.comp isPosCode kSrcBody) (Code.comp (mkDispatch dispCodes) (Code.pair bundleSrc (Code.comp capCode tagSrc))))).eval INPUT = _
  have hspec0 : k = 0 → specOf E B N = 0 := by
    intro h; subst h; rw [hNdef, spec_cfgRank E B 0 ec n (by omega) (by omega), UCode.evaln, encodeOpt]
  have perTag : ∀ (H : Code), dispCodes.getD (min (Nat.unpair ec).1 8) Code.zero = H →
      (H.eval BUNDLE).Dom → (k ≠ 0 → H.eval BUNDLE = Part.some (specOf E B N)) →
      (Code.comp mulCode (Code.pair (Code.comp isPosCode kSrcBody) (Code.comp (mkDispatch dispCodes) (Code.pair bundleSrc (Code.comp capCode tagSrc))))).eval INPUT = Part.some (specOf E B N) := by
    intro H hHeq hdom hval
    have hDH : (Code.comp (mkDispatch dispCodes) (Code.pair bundleSrc (Code.comp capCode tagSrc))).eval INPUT = H.eval BUNDLE := by rw [hdisp, hHeq]
    by_cases hk0 : k = 0
    · have hd : H.eval BUNDLE = Part.some (H.eval BUNDLE |>.get hdom) := Part.eq_some_iff.mpr (Part.get_mem hdom)
      rw [comp_pair_eval _ _ _ _ _ _ hA (hDH.trans hd), eval_mulCode, if_pos hk0, Nat.zero_mul, hspec0 hk0]
    · rw [comp_pair_eval _ _ _ _ _ _ hA (hDH.trans (hval hk0)), eval_mulCode, if_neg hk0, Nat.one_mul]
  show (Code.comp mulCode (Code.pair (Code.comp isPosCode kSrcBody) (Code.comp (mkDispatch dispCodes) (Code.pair bundleSrc (Code.comp capCode tagSrc))))).eval INPUT = _
  rcases Nat.lt_or_ge ((Nat.unpair ec).1) 8 with htlt | htge
  · interval_cases htt : (Nat.unpair ec).1
    · exact perTag (baseAdapt zeroHandler) (by rfl) (by rw [hBU]; exact baseAdapt_zero_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_zero_case E B k' n ec htt (by omega) (by omega))
    · exact perTag (baseAdapt succHandler) (by rfl) (by rw [hBU]; exact baseAdapt_succ_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_succ_case E B k' n ec htt (by omega) (by omega))
    · exact perTag (baseAdapt leftHandler) (by rfl) (by rw [hBU]; exact baseAdapt_left_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_left_case E B k' n ec htt (by omega) (by omega))
    · exact perTag (baseAdapt rightHandler) (by rfl) (by rw [hBU]; exact baseAdapt_right_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_right_case E B k' n ec htt (by omega) (by omega))
    · exact perTag pairHandler (by rfl) (by rw [hBU]; exact pairHandler_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_pair_case E B k' n ec htt (by omega) (by omega))
    · exact perTag compHandler (by rfl) (by rw [hBU]; exact compHandler_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_comp_case E B k' n ec htt (by omega) (by omega) (by omega))
    · exact perTag precHandler (by rfl) (by rw [hBU]; exact precHandler_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_prec_case E B k' n ec htt (by omega) (by omega) (by omega))
    · exact perTag rfindHandler (by rfl) (by rw [hBU]; exact rfindHandler_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_rfind_case E B k' n ec htt (by omega) (by omega) (by omega))
  · exact perTag (baseAdapt zeroHandler) (by rw [show min (Nat.unpair ec).1 8 = 8 from by omega]; rfl) (by rw [hBU]; exact baseAdapt_zero_dom E B N k n ec _) (fun hk0 => by obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩; rw [hBU, hNdef]; exact hbody_default_case E B k' n ec htge (by omega) (by omega))

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.hbody_dispatch
