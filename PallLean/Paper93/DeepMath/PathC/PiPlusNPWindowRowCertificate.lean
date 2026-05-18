import PallLean.Paper93.DeepMath.PathC.PiPlusPayloadCloseout

/-!
# NP-window row-certificate form

The remaining NP-side Route-C obligation is the row inclusion
`PiPlusBooleanProjectedNPWindowRowInclusion`: every source NP-window SPDP row for
`compiledPoly` lies in the Boolean-projected target SPDP subspace.

This file sharpens that obligation to an explicit row-certificate form.  For
each source row, exhibit an actual target generator row whose polynomial is
identical.  This is the concrete local transport theorem still required for the
NP side.
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

/-- Explicit row-certificate version of the NP-window inclusion.  Each source
NP-window row is identified with a concrete target SPDP row for the
Boolean-projected compiled polynomial. -/
def PiPlusBooleanProjectedNPWindowRowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∃ (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
        (m' : SATDeciderGaugeSpace M n hn2 htb hns),
        S'.length = Nat.log 2 n ∧
          m'.totalDegree ≤ Nat.log 2 n ∧
            m'.vars ⊆ S'.toFinset ∧
              isBlockAdmissible
                (cook_levin_compilation M n hn2 htb hns).partition S' ∧
                mlProj (m * iterDerivList S
                  (compiledPoly (cook_levin_compilation M n hn2 htb hns))) =
                  mlProj (m' * iterDerivList S'
                    (piPlusBooleanProjectedGauge M n hn2 htb hns piP
                      (compiledPoly (cook_levin_compilation M n hn2 htb hns))))

/-- Row certificates imply the NP-window row inclusion by inserting the
exhibited target row into the target SPDP generator span. -/
theorem npWindowRowInclusion_of_rowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hcert : PiPlusBooleanProjectedNPWindowRowCertificate M n hn2 htb hns piP) :
    PiPlusBooleanProjectedNPWindowRowInclusion M n hn2 htb hns piP := by
  intro S m hSlen hmdeg hmvars hadm
  rcases hcert S m hSlen hmdeg hmvars hadm with
    ⟨S', m', hSlen', hmdeg', hmvars', hadm', hrow⟩
  rw [hrow]
  exact Submodule.subset_span
    ⟨S', m', hSlen', hmdeg', hmvars', hadm', rfl⟩

/-- Paper-scale NP row-certificate obligation. -/
abbrev PaperScalePiPlusBooleanProjectedNPWindowRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNPWindowRowCertificate
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale NP row inclusion from explicit row certificates. -/
theorem paperScale_npWindowRowInclusion_of_rowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScalePiPlusBooleanProjectedNPWindowRowCertificate M htb hns) :
    PaperScalePiPlusBooleanProjectedNPWindowRowInclusion M htb hns :=
  npWindowRowInclusion_of_rowCertificate
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hcert

/-- Paper-scale NP rank nondecrease from explicit row certificates. -/
theorem paperScale_npWindowRankNondecreasing_of_rowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcert : PaperScalePiPlusBooleanProjectedNPWindowRowCertificate M htb hns) :
    PaperScalePiPlusBooleanProjectedNPWindowRankNondecreasing M htb hns :=
  paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
    M htb hns
    (paperScale_npWindowSubspaceInclusion_of_npWindowRowInclusion
      M htb hns
      (paperScale_npWindowRowInclusion_of_rowCertificate M htb hns hcert))

/-! ## Axiom audit anchors -/

#print axioms npWindowRowInclusion_of_rowCertificate
#print axioms paperScale_npWindowRowInclusion_of_rowCertificate
#print axioms paperScale_npWindowRankNondecreasing_of_rowCertificate

end PallLean.Paper93.DeepMath.PathC
