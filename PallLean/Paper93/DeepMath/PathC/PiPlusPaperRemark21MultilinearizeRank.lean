import PallLean.Paper93.DeepMath.PathC.PiPlusMultilinearizationRank

/-!
# Paper Remark 21 / Lemma 157: multilinearization rank monotonicity

This file gives the paper-facing API for the rank fact already exposed by the
Boolean raw-image row space: multilinearization / Boolean normalization does not
increase SPDP rank.

The formal statement keeps the repository's explicit block partition parameter
`B`; apart from that, it is the paper statement

`rkSPDP κ ℓ (multilinearize p) ≤ rkSPDP κ ℓ p`.
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

namespace BoolPoly

/-- Paper-facing raw SPDP rank notation, with the block partition explicit. -/
noncomputable abbrev rkSPDP {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) : ℕ :=
  rawBlockedSpdpRank B κ ℓ p

/-- Paper-facing multilinearized SPDP rank notation.  This is the rank of the
Boolean-normal row image associated to `multilinearize p`. -/
noncomputable abbrev rkSPDP_multilinearized {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) : ℕ :=
  multilinearizedBlockedSpdpRank B κ ℓ p

/-- Remark 21 / Lemma 157, paper-facing name: multilinearization does not
increase SPDP rank.  Internally, the multilinearized row space is the image of
the raw row space under `liftToBoolLinearMap`, so this is `finrank_map_le`. -/
theorem multilinearize_rank_le {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    rkSPDP_multilinearized B κ ℓ p ≤ rkSPDP B κ ℓ p :=
  multilinearizedBlockedSpdpRank_le_rawBlockedSpdpRank B κ ℓ p

/-- Expanded equivalent of `multilinearize_rank_le`, spelling out the actual
Boolean representative `multilinearize p`. -/
theorem multilinearize_rank_le_expanded {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    boolRawImageBlockedSpdpRank B κ ℓ p ≤ rawBlockedSpdpRank B κ ℓ p :=
  boolRawImageBlockedSpdpRank_le_rawBlockedSpdpRank B κ ℓ p

/-- Paper-scale consequence: any raw rank budget for a polynomial immediately
bounds the rank of its multilinearized representative. -/
theorem multilinearize_rank_bound_of_raw_bound {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : MvPolynomial (Fin n) ℚ}
    (hraw : rkSPDP B κ ℓ p ≤ C) :
    rkSPDP_multilinearized B κ ℓ p ≤ C :=
  le_trans (multilinearize_rank_le B κ ℓ p) hraw

/-- Post-`Pi+` paper-scale version, matching the `piPlus_bool_normalized :=
multilinearize ∘ Pi+` route. -/
theorem paperScaleCookLevinPiPlus_bool_normalized_rank_bound_of_rawPostGaugeBound'
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (κ ℓ C : ℕ)
    (hraw : rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) ≤ C) :
    rkSPDP_multilinearized
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) ≤ C :=
  multilinearize_rank_bound_of_raw_bound hraw

/-! ## Axiom audit anchors -/

#print axioms multilinearize_rank_le
#print axioms multilinearize_rank_le_expanded
#print axioms multilinearize_rank_bound_of_raw_bound
#print axioms paperScaleCookLevinPiPlus_bool_normalized_rank_bound_of_rawPostGaugeBound'

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
