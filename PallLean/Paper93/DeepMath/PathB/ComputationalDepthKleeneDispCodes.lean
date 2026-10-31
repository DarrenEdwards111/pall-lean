import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneInterpBody
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePairDom
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCompDom
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePrecDom
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneRfindDom
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneBaseDom

/-! # Kleene interpreter project — the 9 dispatch codes + their totality (PROVED)

The handler list `interpBody` dispatches over, and the proof that every entry is `.Dom` on any bundle
(the hypothesis `eval_mkDispatch` needs).  `dispCodes`, `dispCodes_dom`.  Not `NEXP ⊄ ACC⁰` or `P ≠ NP`. -/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

noncomputable def dispCodes : List Code :=
  [baseAdapt zeroHandler, baseAdapt succHandler, baseAdapt leftHandler, baseAdapt rightHandler,
   pairHandler, compHandler, precHandler, rfindHandler, baseAdapt zeroHandler]

theorem dispCodes_dom (E B N k n ec : ℕ) (L : List ℕ) :
    ∀ c ∈ dispCodes, (c.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList L))) (Nat.pair k (Nat.pair ec n)))).Dom := by
  intro c hc
  fin_cases hc
  · exact baseAdapt_zero_dom E B N k n ec L
  · exact baseAdapt_succ_dom E B N k n ec L
  · exact baseAdapt_left_dom E B N k n ec L
  · exact baseAdapt_right_dom E B N k n ec L
  · exact pairHandler_dom E B N k n ec L
  · exact compHandler_dom E B N k n ec L
  · exact precHandler_dom E B N k n ec L
  · exact rfindHandler_dom E B N k n ec L
  · exact baseAdapt_zero_dom E B N k n ec L

end PallLean.Paper93.DeepMath.PathB.KleeneUCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.dispCodes_dom
