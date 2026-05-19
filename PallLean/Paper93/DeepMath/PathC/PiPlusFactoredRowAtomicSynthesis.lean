import PallLean.Paper93.DeepMath.PathC.PiPlusSignedConcreteDirectRows
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedFactoredFinalRoute

/-!
# Atomic-row synthesis frontier for the factored Cook--Levin certificate

The Boolean route now has unconditional row certificates for the atomic local
factors used in the Cook--Levin factorization:

* Booleanity/mixed block atoms (`52ae1750` lineage),
* adjacency factors via direct signed-cross conjugation, and
* transition-left/skeleton factors via direct signed-cross conjugation.

This file packages those atomic facts as the closed input surface for the full
factored row certificate.  It also names the remaining product theorem honestly:
turning atomic local rows into the whole `cookLevinFactoredPoly` row certificate
is precisely the Leibniz/product assembly step.  No product-level theorem is
asserted for free here.
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

/-- The atomic Route-C factor rows needed before product assembly. -/
structure CookLevinAtomicRouteCRowPayload
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop where
  /-- Booleanity/mixed block atoms are closed unconditionally. -/
  booleanity : ∀ i : D.blockIndex,
    CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
      ((X (satBlockFalse M n hn2 htb hns D i)) *
        (X (satBlockTrue M n hn2 htb hns D i)))
  /-- Concrete adjacency factors are closed whenever their endpoints are in
distinct `Pi+` blocks. -/
  adjacency : ∀ (i : Fin n) (hi : i.val + 1 < n),
    (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 →
      CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
        ((1 : MvPolynomial (Fin n) ℚ) - (adjLC n i hi).poly)
  /-- Concrete transition-left/skeleton factors are closed whenever their
endpoints are in distinct `Pi+` blocks. -/
  transition : ∀ (q : Fin M.numStates) (i : Fin n) (hi : i.val + 1 < n),
    (D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 →
      CookLevinAtomicFactorRowCertificate M n hn2 htb hns D
        ((1 : MvPolynomial (Fin n) ℚ) - (transSkelLC M n q i hi).poly)
  /-- Arbitrary rest-list constraints expose signed SAT atoms; this is the
case-split surface used by the rest-product side of assembly. -/
  rest_signed : ∀ lc : LocalConstraint n,
    lc ∈ adjConstraintList n ++ transSkelConstraintList M n →
      ∃ (c : ℚ) (i : Fin n) (hi : i.val + 1 < n),
        (1 : MvPolynomial (Fin n) ℚ) - lc.poly =
          satSignedCrossAtom M n hn2 htb hns c i ⟨i.val + 1, hi⟩ ∧
        ((D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 →
          PiPlusBooleanProjectedSignedCrossAtomRowCertificate
            M n hn2 htb hns D c i ⟨i.val + 1, hi⟩)

/-- The atomic Route-C row payload is fully discharged unconditionally. -/
theorem cookLevinAtomicRouteCRowPayload_unconditional
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) :
    CookLevinAtomicRouteCRowPayload M n hn2 htb hns D where
  booleanity := by
    intro i
    exact cookLevinAtomicBooleanityRowCertificate_unconditional
      M n hn2 htb hns D i
  adjacency := by
    intro i hi hab
    exact cookLevinAtomicAdjacencyRowCertificate_unconditional
      M n hn2 htb hns D i hi hab
  transition := by
    intro q i hi hab
    exact cookLevinAtomicTransitionRowCertificate_unconditional
      M n hn2 htb hns D q i hi hab
  rest_signed := by
    intro lc hlc
    exact cookLevinRestAtomicSignedRowCertificate_of_mem
      M n hn2 htb hns D lc hlc

/-- Paper-scale atomic Route-C row payload. -/
abbrev PaperScaleCookLevinAtomicRouteCRowPayload
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinAtomicRouteCRowPayload M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale atomic Route-C rows are closed unconditionally. -/
theorem paperScaleCookLevinAtomicRouteCRowPayload_unconditional
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinAtomicRouteCRowPayload M htb hns :=
  cookLevinAtomicRouteCRowPayload_unconditional
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- The remaining synthesis theorem: atomic rows imply the full paper-scale
factored compiled-row certificate.

This is the exact Leibniz/product assembly socket.  It is intentionally a
reduction structure, not an axiom or a fake theorem. -/
structure PaperScaleCookLevinFactoredRowCertificateAtomicAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  assemble : PaperScaleCookLevinAtomicRouteCRowPayload M htb hns →
    PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns

/-- Since the atomic payload is unconditional, the assembly reduction alone gives
the full paper-scale factored row certificate. -/
theorem paperScale_factoredCompiledRowCertificate_of_atomicAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScaleCookLevinFactoredRowCertificateAtomicAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredCompiledRowCertificateOneZero
      M htb hns :=
  hred.assemble
    (paperScaleCookLevinAtomicRouteCRowPayload_unconditional M htb hns)

/-- The assembly reduction closes the paper-scale P-side raw-pullback membership
through the existing factored certificate route. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneZero_of_atomicAssemblyReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScaleCookLevinFactoredRowCertificateAtomicAssemblyReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneZero
      M htb hns :=
  paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredRowCertificate
    M htb hns
    (paperScale_factoredCompiledRowCertificate_of_atomicAssemblyReduction
      M htb hns hred)

/-- Final closeout from the atomic assembly reduction, NP-window inclusion,
and the existing Route-B one-window blockers. -/
theorem no_decidesSAT_at_paperScale_of_atomicAssemblyReduction_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScaleCookLevinFactoredRowCertificateAtomicAssemblyReduction
      M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns)
    (W : SymmetricPowerBound.ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (W_finite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (W_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (zero_common_span :
      CookLevinOneWindowZeroHistogramShiftCommonSpan
        M (2 ^ 804) paperScale_ge_two htb hns)
    (per_type_spanning :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_factoredRowCertificate_npInclusion
    M htb hns
    (paperScale_factoredCompiledRowCertificate_of_atomicAssemblyReduction
      M htb hns hred)
    hnp W W_finite W_dim zero_common_span per_type_spanning

/-! ## Axiom audit anchors -/

#print axioms cookLevinAtomicRouteCRowPayload_unconditional
#print axioms paperScaleCookLevinAtomicRouteCRowPayload_unconditional
#print axioms paperScale_factoredCompiledRowCertificate_of_atomicAssemblyReduction
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneZero_of_atomicAssemblyReduction
#print axioms no_decidesSAT_at_paperScale_of_atomicAssemblyReduction_npInclusion

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
