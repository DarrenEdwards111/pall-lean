import PallLean.Paper93.DeepMath.PathC.PiPlusOneOneWindowUpgrade
import PallLean.Paper93.DeepMath.PathC.PiPlusPaperScaleRestParityClassifier

/-!
# One-one local-factor payload for paper-scale rest constraints

The global P-side target has now been widened to `(1,1)`.  This file packages
what the parity classifier supplies in exactly the local-factor shape needed by
the next allocation/product assembly step: every paper-scale Cook--Levin rest
constraint has a certified local factor, with odd-left factors using the old
cross-block certificate and even-left factors using the same-block `(1,1)` span.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- The paper-scale `(1,1)` local certificate for a single rest constraint.

This is intentionally factor-local: it does not assert the full Leibniz product
assembly.  It records the exact parity split needed by that later assembly.
Odd-left adjacent factors are cross-block signed atoms; even-left adjacent
factors are same-block signed atoms covered by the `(1,1)` span certificate. -/
inductive PaperScaleRestConstraintOneOneLocalFactorCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (lc : LocalConstraint (2 ^ 804)) : Prop
  | cross
      (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
      (hfactor : (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
          c i ⟨i.val + 1, hi⟩)
      (hodd : i.val % 2 = 1)
      (hcert : PiPlusBooleanProjectedSignedCrossAtomRowCertificate
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c i ⟨i.val + 1, hi⟩) :
      PaperScaleRestConstraintOneOneLocalFactorCertificate M htb hns lc
  | same
      (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804)
      (hfactor : (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedSameBlockAtom M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
          c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1)
      (heven : i.val % 2 = 0)
      (hcert : PiPlusBooleanProjectedSignedSameBlockAtomOneOneSpanCertificate
        M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
        c ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1) :
      PaperScaleRestConstraintOneOneLocalFactorCertificate M htb hns lc

/-- Every paper-scale rest-list constraint has the local `(1,1)` factor
certificate needed by the next product/allocation stage. -/
theorem paperScale_restConstraintOneOneLocalFactorCertificate_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (lc : LocalConstraint (2 ^ 804))
    (hlc : lc ∈ adjConstraintList (2 ^ 804) ++
      transSkelConstraintList M (2 ^ 804)) :
    PaperScaleRestConstraintOneOneLocalFactorCertificate M htb hns lc := by
  rcases paperScale_restConstraint_parityClassifier M htb hns lc hlc with hcross | hsame
  · rcases hcross with ⟨c, i, hi, hfactor, hodd, hcert⟩
    exact PaperScaleRestConstraintOneOneLocalFactorCertificate.cross
      c i hi hfactor hodd hcert
  · rcases hsame with ⟨c, i, hi, hfactor, heven, hcert⟩
    exact PaperScaleRestConstraintOneOneLocalFactorCertificate.same
      c i hi hfactor heven hcert

/-- List-level payload: all rest constraints in the Cook--Levin rest list have
paper-scale `(1,1)` local factor certificates. -/
def PaperScaleRestConstraintOneOneLocalFactorPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  ∀ lc : LocalConstraint (2 ^ 804),
    lc ∈ adjConstraintList (2 ^ 804) ++ transSkelConstraintList M (2 ^ 804) →
      PaperScaleRestConstraintOneOneLocalFactorCertificate M htb hns lc

/-- The paper-scale rest local-factor payload is unconditional. -/
theorem paperScale_restConstraintOneOneLocalFactorPayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleRestConstraintOneOneLocalFactorPayload M htb hns := by
  intro lc hlc
  exact paperScale_restConstraintOneOneLocalFactorCertificate_unconditional
    M htb hns lc hlc

/-- Route-C local-factor payload at the widened `(1,1)` surface.

The Booleanity/mixed/cross-atom pieces were already discharged separately; the
new content here is the rest-list parity certificate, now packaged as the input
the allocation/product step can consume. -/
structure PaperScalePiPlusBooleanProjectedOneOneLocalFactorPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  requested_route_c_discharges : RequestedRouteCUnconditionalDischarges
  rest_one_one_payload : PaperScaleRestConstraintOneOneLocalFactorPayload M htb hns

/-- The widened local-factor payload is now fully available unconditionally. -/
theorem paperScalePiPlusBooleanProjectedOneOneLocalFactorPayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorPayload M htb hns where
  requested_route_c_discharges := requestedRouteCUnconditionalDischarges
  rest_one_one_payload :=
    paperScale_restConstraintOneOneLocalFactorPayload_unconditional M htb hns

/-! ## Axiom audit anchors -/

#print axioms paperScale_restConstraintOneOneLocalFactorCertificate_unconditional
#print axioms paperScale_restConstraintOneOneLocalFactorPayload_unconditional
#print axioms paperScalePiPlusBooleanProjectedOneOneLocalFactorPayload_unconditional

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
