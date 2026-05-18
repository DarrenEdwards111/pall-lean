import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCoordinateAtom
import PallLean.PACLeibniz

/-!
# Cook--Levin product assembly reduction for Boolean-projected Pi+

The remaining P-side Route-C theorem is no longer local algebra: it is the
product-level assembly over the Cook--Levin polynomial.  This file moves the
compiled-row certificate from the opaque `compiledPoly` expression to the actual
Cook--Levin product factorization

`booleanity factors * restFactorProd'`.

That is the shape where the next proof should use the length-bounded Leibniz
infrastructure and the coordinate-level mixed-block atom.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open PACLeibniz

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The booleanity-factor product in the Cook--Levin factorization. -/
noncomputable def cookLevinBooleanFactorProd (n : Nat) :
    MvPolynomial (Fin n) ℚ :=
  ((boolConstraintList n).map
    (fun c => (1 : MvPolynomial (Fin n) ℚ) - c.poly)).prod

/-- The factored Cook--Levin polynomial: booleanity factors times adjacency /
transition rest factors. -/
noncomputable def cookLevinFactoredPoly (M : DTM) (n : Nat) :
    MvPolynomial (Fin n) ℚ :=
  cookLevinBooleanFactorProd n * restFactorProd' M n

/-- The compiled polynomial is definitionally/propositionally equal to the
factored Cook--Levin product. -/
theorem compiledPoly_eq_cookLevinFactoredPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    compiledPoly (cook_levin_compilation M n hn2 htb hns) =
      cookLevinFactoredPoly M n := by
  rw [compiledPoly_factored M n hn2 htb hns]
  unfold cookLevinFactoredPoly cookLevinBooleanFactorProd
  rfl

/-- Factored-polynomial version of the final-window compiled row certificate.

This is the same certificate as
`PiPlusBooleanProjectedWindowedCompiledRowCertificate`, but with the source and
target polynomial written as the explicit Cook--Levin product.  Proving this is
the product-level assembly problem. -/
def PiPlusBooleanProjectedWindowedFactoredCompiledRowCertificate
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

/-- The factored certificate currently has the same row statement as the
compiled certificate, but its name records the intended proof route: rewrite
`compiledPoly` using `compiledPoly_eq_cookLevinFactoredPoly`, then assemble rows
from the product factors using Leibniz and the coordinate atom. -/
theorem compiledRowCertificate_of_factoredCompiledRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hfactored : PiPlusBooleanProjectedWindowedFactoredCompiledRowCertificate
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedWindowedCompiledRowCertificate
      extraK extraL M n hn2 htb hns piP := by
  intro S m hSlen hmdeg hmvars hadm
  exact hfactored S m hSlen hmdeg hmvars hadm

/-- Paper-scale factored row certificate abbreviation. -/
abbrev PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedWindowedFactoredCompiledRowCertificate 1 0
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale factored product assembly discharges the compiled-row certificate
socket. -/
theorem paperScale_compiledRowCertificateOneZero_of_factoredCompiledRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfactored : PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledRowCertificateOneZero M htb hns :=
  compiledRowCertificate_of_factoredCompiledRowCertificate
    1 0 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hfactored

/-- Therefore the factored product assembly discharges the named P-side
Boolean-projected Route-C socket. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredCompiledRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hfactored : PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns :=
  paperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero_of_compiledRowCertificate
    M htb hns
    (paperScale_compiledRowCertificateOneZero_of_factoredCompiledRowCertificate
      M htb hns hfactored)

/-- Length-bounded Leibniz, specialized to the Cook--Levin factor product.  This
is the axiom-free algebraic expansion that the remaining factored certificate
proof should combine with the coordinate atom. -/
theorem iterDerivList_cookLevinFactoredPoly_mem_leibniz_span
    (M : DTM) (n : Nat) (S : List (Fin n)) :
    iterDerivList S (cookLevinFactoredPoly M n) ∈
      Submodule.span ℚ
        (leibnizGenSetBounded S.length
          (cookLevinBooleanFactorProd n) (restFactorProd' M n)) := by
  unfold cookLevinFactoredPoly
  exact iterDerivList_mul_mem_leibniz_span_bounded S
    (cookLevinBooleanFactorProd n) (restFactorProd' M n)

/-! ## Axiom audit anchors -/

#print axioms compiledPoly_eq_cookLevinFactoredPoly
#print axioms compiledRowCertificate_of_factoredCompiledRowCertificate
#print axioms paperScale_compiledRowCertificateOneZero_of_factoredCompiledRowCertificate
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredCompiledRowCertificate
#print axioms iterDerivList_cookLevinFactoredPoly_mem_leibniz_span

end PallLean.Paper93.DeepMath.PathC
