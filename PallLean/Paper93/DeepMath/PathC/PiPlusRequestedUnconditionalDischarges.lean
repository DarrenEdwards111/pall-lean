import PallLean.Paper93.DeepMath.PathC.PiPlusPaperRemark21MultilinearizeRank
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedSignedConcreteFactors

/-!
# Requested Route-C unconditional discharge package

This file records, in one top-level theorem, the unconditional discharges that
were identified as the high-impact Route-C targets:

* paper Remark 21 multilinearization rank monotonicity;
* mixed Booleanity atom;
* adjacency atom;
* transition / signed cross-block atom;
* SAT-coordinate signed atoms;
* concrete Cook--Levin rest factors classified as signed atoms.

The remaining product-level theorem (`cookLevinFactoredRowCertificate_*`) is not
asserted here for free: it still requires the Leibniz/product assembly.  This
package is the clean input surface for that next synthesis step.
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

/-- Top-level bundle of the currently discharged Route-C atomic/rank facts. -/
structure RequestedRouteCUnconditionalDischarges : Prop where
  /-- Paper Remark 21 / Lemma 157: multilinearization does not increase rank. -/
  rank_multilinearize :
    ∀ {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ)
      (p : MvPolynomial (Fin n) ℚ),
      rkSPDP_multilinearized B κ ℓ p ≤ rkSPDP B κ ℓ p
  /-- Mixed Booleanity atom, SAT-coordinate surface. -/
  mixed_atom :
    ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
      (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
      (i : D.blockIndex),
      PiPlusBooleanProjectedMixedAtomRowCertificate M n hn2 htb hns D i
  /-- Block-local adjacency atom. -/
  adjacency_atom :
    ∀ {ι : Type*} [DecidableEq ι] (i j : ι) (_hij : i ≠ j),
      BlockPiPlusBooleanProjectedAdjacencyAtomRowCertificate
        (blockAdjacencyAtomFF i j)
  /-- Block-local coefficient-weighted transition atom. -/
  transition_atom :
    ∀ {ι : Type*} [DecidableEq ι] (c : ℚ) (i j : ι) (_hij : i ≠ j),
      BlockPiPlusBooleanProjectedTransitionAtomRowCertificate
        (blockTransitionAtomFF c i j)
  /-- SAT-coordinate signed cross-block atom. -/
  signed_sat_atom :
    ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
      (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
      (c : ℚ)
      (a b : Fin (cook_levin_compilation M n hn2 htb hns).numVars),
      (D.coord a).1 ≠ (D.coord b).1 →
        PiPlusBooleanProjectedSignedCrossAtomRowCertificate
          M n hn2 htb hns D c a b
  /-- Concrete Cook--Levin rest constraints are signed SAT-coordinate atoms; the
  corresponding row certificate follows from the exact distinct-block endpoint
  hypothesis. -/
  rest_constraint :
    ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
      (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
      (lc : LocalConstraint n),
      lc ∈ adjConstraintList n ++ transSkelConstraintList M n →
        ∃ (c : ℚ) (i : Fin n) (hi : i.val + 1 < n),
          (1 : MvPolynomial (Fin n) ℚ) - lc.poly =
            satSignedCrossAtom M n hn2 htb hns c i ⟨i.val + 1, hi⟩ ∧
          ((D.coord i).1 ≠ (D.coord ⟨i.val + 1, hi⟩).1 →
            PiPlusBooleanProjectedSignedCrossAtomRowCertificate
              M n hn2 htb hns D c i ⟨i.val + 1, hi⟩)

/-- All requested unconditional atomic/rank Route-C discharges currently landed
in the codebase, packaged as one theorem for downstream synthesis. -/
theorem requestedRouteCUnconditionalDischarges :
    RequestedRouteCUnconditionalDischarges := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n B κ ℓ p
    exact multilinearize_rank_le B κ ℓ p
  · intro M n hn2 htb hns D i
    exact piPlusBooleanProjectedMixedAtomRowCertificate_unconditional
      M n hn2 htb hns D i
  · intro ι _inst i j hij
    exact blockPiPlusBooleanProjectedAdjacencyAtomRowCertificate_unconditional
      (i := i) (j := j) hij
  · intro ι _inst c i j hij
    exact blockPiPlusBooleanProjectedTransitionAtomRowCertificate_unconditional
      (c := c) (i := i) (j := j) hij
  · intro M n hn2 htb hns D c a b hab
    exact piPlusBooleanProjectedSignedCrossAtomRowCertificate_unconditional
      M n hn2 htb hns D c a b hab
  · intro M n hn2 htb hns D lc hlc
    exact restConstraint_signedCrossAtomRowCertificate_of_mem
      M n hn2 htb hns D lc hlc

/-- Paper-scale specialization of the concrete rest-constraint part of the
requested discharge package. -/
theorem paperScaleRequestedRestConstraintDischarge
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (lc : LocalConstraint (2 ^ 804))
    (hlc : lc ∈ adjConstraintList (2 ^ 804) ++
      transSkelConstraintList M (2 ^ 804)) :
    ∃ (c : ℚ) (i : Fin (2 ^ 804)) (hi : i.val + 1 < 2 ^ 804),
      (1 : MvPolynomial (Fin (2 ^ 804)) ℚ) - lc.poly =
        satSignedCrossAtom M (2 ^ 804) paperScale_ge_two htb hns
          c i ⟨i.val + 1, hi⟩ ∧
      (((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord i).1 ≠
        ((cookLevinPiPlusBlockCoordinateData_paperScale M htb hns).coord
          ⟨i.val + 1, hi⟩).1 →
        PiPlusBooleanProjectedSignedCrossAtomRowCertificate
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
          c i ⟨i.val + 1, hi⟩) :=
  paperScale_restConstraint_signedCrossAtomRowCertificate_of_mem
    M htb hns lc hlc

/-! ## Axiom audit anchors -/

#print axioms requestedRouteCUnconditionalDischarges
#print axioms paperScaleRequestedRestConstraintDischarge

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
