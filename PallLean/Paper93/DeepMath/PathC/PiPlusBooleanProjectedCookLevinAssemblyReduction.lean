import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCoordinateAtom
import PallLean.PACLeibniz
import PallLean.SymmetricPower

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
                          (cookLevinFactoredPoly M n)))) =
                      mlProj (m' * iterDerivList S'
                        (cookLevinFactoredPoly M n))

/-- A certificate proved over the explicit Cook--Levin factor product gives the
compiled certificate by rewriting both source and target occurrences of
`compiledPoly`. -/
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
  rcases hfactored S m hSlen hmdeg hmvars hadm with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hrow⟩
  refine ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', ?_⟩
  simpa [compiledPoly_eq_cookLevinFactoredPoly M n hn2 htb hns] using hrow

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

/-- SPDP-row version of the factored Leibniz reduction: after multiplying by the
row multiplier and applying `mlProj`, the row lies in the span of the projected
length-bounded Leibniz summands.  This is the exact linear-algebra surface left
for the Cook--Levin factor classifier. -/
theorem mlProj_mul_iterDerivList_cookLevinFactoredPoly_mem_leibniz_image_span
    (M : DTM) (n : Nat) (S : List (Fin n))
    (m : MvPolynomial (Fin n) ℚ) :
    mlProj (m * iterDerivList S (cookLevinFactoredPoly M n)) ∈
      Submodule.span ℚ
        ((fun q => mlProj (m * q)) ''
          leibnizGenSetBounded S.length
            (cookLevinBooleanFactorProd n) (restFactorProd' M n)) := by
  exact SymmetricPower.mlProj_mul_mem_span_image m
    (leibnizGenSetBounded S.length
      (cookLevinBooleanFactorProd n) (restFactorProd' M n))
    (iterDerivList S (cookLevinFactoredPoly M n))
    (iterDerivList_cookLevinFactoredPoly_mem_leibniz_span M n S)

/-- Generic linear-algebra bridge: if a target row lies in the span of a set
whose raw `Pi+` pullbacks are already in a source subspace, then the raw pullback
of the target row is in that source subspace. -/
theorem piPlusRawPullback_mem_of_mem_span
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (G : Set (SATDeciderGaugeSpace M n hn2 htb hns))
    (W : Submodule ℚ (SATDeciderGaugeSpace M n hn2 htb hns))
    (row : SATDeciderGaugeSpace M n hn2 htb hns)
    (hrow : row ∈ Submodule.span ℚ G)
    (hG : ∀ q ∈ G, piP.equiv.symm q ∈ W) :
    piP.equiv.symm row ∈ W := by
  let L : SATDeciderGaugeSpace M n hn2 htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M n hn2 htb hns := piP.equiv.symm.toLinearMap
  change L row ∈ W
  refine Submodule.span_induction
    (p := fun x _ => L x ∈ W)
    (by intro q hq; exact hG q hq) ?hzero ?hadd ?hsmul hrow
  · simpa [L] using W.zero_mem
  · intro x y _hxmem _hymem hx hy
    simpa [L, map_add] using W.add_mem hx hy
  · intro a x _hxmem hx
    simpa [L, map_smul] using W.smul_mem a hx

/-- A row-span classifier for the factored Cook--Levin target.  It separates the
remaining product algebra into two explicit obligations:

1. a span expansion for each Boolean-projected target row, and
2. membership of the raw pullback of every generator in that expansion in the
   enlarged source SPDP subspace.

This is the precise form in which the Cook--Levin Leibniz summand classifier
should be proved. -/
def PiPlusBooleanProjectedFactoredRowSpanClassifier
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
      ∃ G : Set (SATDeciderGaugeSpace M n hn2 htb hns),
        mlProj (m * iterDerivList S
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP
            (cookLevinFactoredPoly M n))) ∈ Submodule.span ℚ G ∧
        ∀ q ∈ G,
          piP.equiv.symm q ∈
            mlBlockedSpdpSubspaceInc
              (cook_levin_compilation M n hn2 htb hns).partition
              (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
              (cookLevinFactoredPoly M n)

/-- The row-span classifier discharges direct factored raw-pullback membership.
This is weaker and more natural than a single-row equality certificate, and is
exactly what span-valued Leibniz expansions provide. -/
theorem factoredRawPullbackMembership_of_rowSpanClassifier
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hclass : PiPlusBooleanProjectedFactoredRowSpanClassifier
      extraK extraL M n hn2 htb hns piP) :
    ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : SATDeciderGaugeSpace M n hn2 htb hns),
        S.length = Nat.log 2 n →
        m.totalDegree ≤ Nat.log 2 n →
        m.vars ⊆ S.toFinset →
        isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
        piP.equiv.symm
          (mlProj (m * iterDerivList S
            (piPlusBooleanProjectedGauge M n hn2 htb hns piP
              (cookLevinFactoredPoly M n)))) ∈
          mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
            (cookLevinFactoredPoly M n) := by
  intro S m hSlen hmdeg hmvars hadm
  rcases hclass S m hSlen hmdeg hmvars hadm with ⟨G, hspan, hG⟩
  exact piPlusRawPullback_mem_of_mem_span M n hn2 htb hns piP G
    (mlBlockedSpdpSubspaceInc
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
      (cookLevinFactoredPoly M n))
    (mlProj (m * iterDerivList S
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP
        (cookLevinFactoredPoly M n)))) hspan hG

/-! ## Axiom audit anchors -/

#print axioms compiledPoly_eq_cookLevinFactoredPoly
#print axioms compiledRowCertificate_of_factoredCompiledRowCertificate
#print axioms paperScale_compiledRowCertificateOneZero_of_factoredCompiledRowCertificate
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneZero_of_factoredCompiledRowCertificate
#print axioms iterDerivList_cookLevinFactoredPoly_mem_leibniz_span
#print axioms mlProj_mul_iterDerivList_cookLevinFactoredPoly_mem_leibniz_image_span
#print axioms piPlusRawPullback_mem_of_mem_span
#print axioms factoredRawPullbackMembership_of_rowSpanClassifier

end PallLean.Paper93.DeepMath.PathC
