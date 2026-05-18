import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedBlockLocalRows

/-!
# Compiled-row certificate bridge for Boolean-projected Pi+

`PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership` is the current
P-side Route-C socket: every final-window generator of the Boolean-projected
compiled Cook--Levin polynomial has raw `Pi+` pullback in the one-window enlarged
source SPDP subspace.

After the block-local calculation, the next useful global target is an explicit
compiled-row certificate, not the older all-polynomial/all-window row certificate.
This file defines that final-window-only certificate and proves that it implies
the existing compiled membership socket.  The certificate is exactly what a
Cook--Levin row assembly proof should now construct: for each final P-side row,
produce an enlarged source row `(S',m')` and the raw-pullback equality.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Final-window compiled-row certificate for Boolean-projected `Pi+`.

This is the compiled-only analogue of
`PiPlusBooleanProjectedWindowedRawPullbackRowCertificate`: it quantifies only over
SPDP generators of the final Cook--Levin P-side polynomial at
`(κ,ℓ) = (log₂ n, log₂ n)`.  For each target row it asks for one enlarged source
row witnessing the raw inverse pullback.
-/
def PiPlusBooleanProjectedWindowedCompiledRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = Nat.log 2 n →
      m.totalDegree ≤ Nat.log 2 n →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∃ (κ' ℓ' : Nat)
        (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
        (m' : SATDeciderGaugeSpace M n hn2 htb hns),
        κ' ≤ Nat.log 2 n + extraK ∧
          ℓ' ≤ Nat.log 2 n + extraL ∧
            S'.length = κ' ∧
              m'.totalDegree ≤ ℓ' ∧
                m'.vars ⊆ S'.toFinset ∧
                  isBlockAdmissible
                    (cook_levin_compilation M n hn2 htb hns).partition S' ∧
                    piP.equiv.symm
                      (mlProj (m * iterDerivList S
                        (piPlusBooleanProjectedGauge M n hn2 htb hns piP
                          (compiledPoly
                            (cook_levin_compilation M n hn2 htb hns))))) =
                      mlProj (m' * iterDerivList S'
                        (compiledPoly
                          (cook_levin_compilation M n hn2 htb hns)))

/-- Paper-scale compiled-row certificate abbreviation. -/
abbrev PaperScalePiPlusBooleanProjectedWindowedCompiledRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedWindowedCompiledRowCertificate extraK extraL
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- The older all-polynomial/all-window row certificate implies this sharper
compiled-only row certificate. -/
theorem compiledRowCertificate_of_windowedRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedWindowedCompiledRowCertificate
      extraK extraL M n hn2 htb hns piP := by
  intro S m hSlen hmdeg hmvars hadm
  exact hrow (Nat.log 2 n) (Nat.log 2 n)
    (compiledPoly (cook_levin_compilation M n hn2 htb hns))
    S m hSlen hmdeg hmvars hadm

/-- A compiled-row certificate implies the existing compiled P-side raw-pullback
membership socket. -/
theorem compiledRawPullbackMembership_of_compiledRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedWindowedCompiledRowCertificate
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M n hn2 htb hns piP := by
  intro S m hSlen hmdeg hmvars hadm
  rcases hrow S m hSlen hmdeg hmvars hadm with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hroweq⟩
  rw [hroweq]
  exact Submodule.subset_span
    ⟨S', m', by rwa [hSlen'], le_trans hmdeg' hℓ', hmvars', hadm', rfl⟩

/-- Paper-scale specialization of the compiled-row-certificate bridge. -/
theorem paperScale_compiledRawPullbackMembership_of_compiledRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedWindowedCompiledRowCertificate
      extraK extraL M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembership
      extraK extraL M htb hns :=
  compiledRawPullbackMembership_of_compiledRowCertificate
    extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hrow

/-- One-window paper-scale specialization: this is the explicit compiled-row
certificate target for the honest Boolean-projected Route-C P-side theorem. -/
abbrev PaperScalePiPlusBooleanProjectedCompiledRowCertificateOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedWindowedCompiledRowCertificate 1 0 M htb hns

/-- One-window compiled-row certificates discharge the named P-side socket. -/
theorem paperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero_of_compiledRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedCompiledRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns :=
  paperScale_compiledRawPullbackMembership_of_compiledRowCertificate
    1 0 M htb hns hrow

/-- One-window compiled-row certificates therefore supply the sharp compiled
P-subspace inclusion used by final Route-C closure. -/
theorem paperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero_of_compiledRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedCompiledRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero
      M htb hns :=
  paperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero_of_windowedCompiledRawPullbackMembership
    M htb hns
    (paperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero_of_compiledRowCertificate
      M htb hns hrow)

/-! ## Axiom audit anchors -/

#print axioms compiledRowCertificate_of_windowedRowCertificate
#print axioms compiledRawPullbackMembership_of_compiledRowCertificate
#print axioms paperScale_compiledRawPullbackMembership_of_compiledRowCertificate
#print axioms paperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero_of_compiledRowCertificate
#print axioms paperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneZero_of_compiledRowCertificate

end PallLean.Paper93.DeepMath.PathC
