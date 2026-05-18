import PallLean.Paper93.DeepMath.PathC.PiPlusNPWindowRowCertificate

/-!
# NP-window closeout from the exact compiled-polynomial invariant

The NP-side row certificate is completely discharged if the Boolean-projected
`Pi+` action fixes the Cook--Levin compiled polynomial.  In that case every
source NP-window row is literally the same generator row in the target SPDP
subspace, with the same derivative window and multiplier.

This isolates the exact remaining NP transport invariant in a small form:
`piPlusBooleanProjectedGauge ... compiledPoly = compiledPoly`.
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

/-- The sharp polynomial invariant that immediately closes the NP-window rows. -/
def PiPlusBooleanProjectedFixesCompiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  piPlusBooleanProjectedGauge M n hn2 htb hns piP
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
    compiledPoly (cook_levin_compilation M n hn2 htb hns)

/-- If the Boolean-projected action fixes the compiled polynomial, the NP row
certificate is obtained by taking the exact same row on the target side. -/
theorem npWindowRowCertificate_of_fixesCompiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hfix : PiPlusBooleanProjectedFixesCompiledPoly M n hn2 htb hns piP) :
    PiPlusBooleanProjectedNPWindowRowCertificate M n hn2 htb hns piP := by
  intro S m hSlen hmdeg hmvars hadm
  refine ⟨S, m, hSlen, hmdeg, hmvars, hadm, ?_⟩
  rw [hfix]

/-- Polynomial-fixing invariant gives the NP row inclusion directly. -/
theorem npWindowRowInclusion_of_fixesCompiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hfix : PiPlusBooleanProjectedFixesCompiledPoly M n hn2 htb hns piP) :
    PiPlusBooleanProjectedNPWindowRowInclusion M n hn2 htb hns piP :=
  npWindowRowInclusion_of_rowCertificate M n hn2 htb hns piP
    (npWindowRowCertificate_of_fixesCompiledPoly M n hn2 htb hns piP hfix)

/-- Paper-scale compiled-polynomial fixing invariant. -/
abbrev PaperScalePiPlusBooleanProjectedFixesCompiledPoly
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedFixesCompiledPoly
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale NP row certificate from the compiled-polynomial invariant. -/
theorem paperScale_npWindowRowCertificate_of_fixesCompiledPoly
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfix : PaperScalePiPlusBooleanProjectedFixesCompiledPoly M htb hns) :
    PaperScalePiPlusBooleanProjectedNPWindowRowCertificate M htb hns :=
  npWindowRowCertificate_of_fixesCompiledPoly
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hfix

/-- Paper-scale NP row inclusion from the compiled-polynomial invariant. -/
theorem paperScale_npWindowRowInclusion_of_fixesCompiledPoly
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfix : PaperScalePiPlusBooleanProjectedFixesCompiledPoly M htb hns) :
    PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns :=
  paperScale_npWindowRowInclusion_of_rowCertificate M htb hns
    (paperScale_npWindowRowCertificate_of_fixesCompiledPoly M htb hns hfix)

/-- Paper-scale NP rank nondecrease from the compiled-polynomial invariant. -/
theorem paperScale_npWindowRankNondecreasing_of_fixesCompiledPoly
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfix : PaperScalePiPlusBooleanProjectedFixesCompiledPoly M htb hns) :
    PaperScalePiPlusBooleanProjectedNPWindowRankNondecreasing M htb hns :=
  paperScale_npWindowRankNondecreasing_of_rowCertificate M htb hns
    (paperScale_npWindowRowCertificate_of_fixesCompiledPoly M htb hns hfix)

/-! ## Axiom audit anchors -/

#print axioms npWindowRowCertificate_of_fixesCompiledPoly
#print axioms npWindowRowInclusion_of_fixesCompiledPoly
#print axioms paperScale_npWindowRowCertificate_of_fixesCompiledPoly
#print axioms paperScale_npWindowRowInclusion_of_fixesCompiledPoly
#print axioms paperScale_npWindowRankNondecreasing_of_fixesCompiledPoly

end PallLean.Paper93.DeepMath.PathC
