import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRawImageRank
import PallLean.Paper93.DeepMath.PathC.PiPlusConcreteTransformLemmas

/-!
# Paper-faithful multilinearization rank seam

Remark 21 / Lemma 157 in the paper use the Boolean multilinear representative:
compute the transformed polynomial in the raw ring, then replace every
`xᵢ^r`, `r ≥ 1`, by `xᵢ`.  Rank is then measured on that Boolean-normal
representative, and this operation does not increase the SPDP rank.

In the current Lean refactor this operation is exactly `BoolPoly.liftToBool`,
whose raw representative is `zeroProfileBooleanNormalize`.  The corrected rank
surface is the raw derivative-row image in the Boolean ambient; its dimension is
bounded by the raw source-row dimension by `Submodule.finrank_map_le`.

This file gives those paper names explicitly so downstream Route-C statements
can cite the paper-faithful lemma rather than the older raw fixedness sockets.
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

/-- Paper-faithful multilinearization: replace `xᵢ^r` by `xᵢ` for `r ≥ 1`,
returned as a Boolean-normal polynomial. -/
noncomputable abbrev multilinearize {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) : BoolPoly n :=
  liftToBool p

@[simp] theorem coe_multilinearize {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) :
    (multilinearize p : MvPolynomial (Fin n) ℚ) =
      zeroProfileBooleanNormalize p := rfl

/-- Rank of the multilinearized representative in the corrected Boolean raw-image
SPDP surface.  This is the formal counterpart of the paper's `rk_SPDP(f_ml)`. -/
noncomputable def multilinearizedBlockedSpdpRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) : ℕ :=
  boolRawImageBlockedSpdpRank B κ ℓ p

/-- Paper Lemma 157 / Remark 21 surface: multilinearization does not increase
SPDP rank.  Formally, the Boolean-normal row space is the image of the raw row
space under the quotient/multilinearization map, so its dimension is at most the
raw dimension. -/
theorem multilinearizedBlockedSpdpRank_le_rawBlockedSpdpRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    multilinearizedBlockedSpdpRank B κ ℓ p ≤ rawBlockedSpdpRank B κ ℓ p := by
  exact boolRawImageBlockedSpdpRank_le_rawBlockedSpdpRank B κ ℓ p

/-- The same non-increase lemma in expanded image-rank form. -/
theorem boolRawImageRank_is_multilinearizedRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    boolRawImageBlockedSpdpRank B κ ℓ p =
      multilinearizedBlockedSpdpRank B κ ℓ p := rfl

/-- Boolean-normalized `Pi+` gauge: raw `Pi+` followed by paper
multilinearization.  This is the operation the paper uses for rank, not raw
fixedness of `Pi+` in the full polynomial ring. -/
noncomputable def piPlusMultilinearizedGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars :=
  multilinearize (piP.gauge p)

@[simp] theorem coe_piPlusMultilinearizedGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    (piPlusMultilinearizedGauge M n hn2 htb hns piP p :
        SATDeciderGaugeSpace M n hn2 htb hns) =
      zeroProfileBooleanNormalize (piP.gauge p) := rfl

/-- Applying raw `Pi+` and then paper multilinearization cannot increase rank
relative to the raw post-gauge row rank. -/
theorem piPlusMultilinearizedGauge_rank_le_rawPostGaugeRank
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : ℕ)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    multilinearizedBlockedSpdpRank B κ ℓ (piP.gauge p) ≤
      rawBlockedSpdpRank B κ ℓ (piP.gauge p) := by
  exact multilinearizedBlockedSpdpRank_le_rawBlockedSpdpRank B κ ℓ (piP.gauge p)

/-- Paper-scale post-`Pi+` multilinearization rank non-increase for the concrete
Cook--Levin transform. -/
theorem paperScaleCookLevinPiPlusPostGauge_multilinearizedRank_le_rawPostGaugeRank
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (κ ℓ : ℕ) :
    multilinearizedBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) ≤
      rawBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) := by
  exact multilinearizedBlockedSpdpRank_le_rawBlockedSpdpRank
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
    ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)))

/-- If the raw post-gauge SPDP rank is bounded, then the paper-faithful
multilinearized post-gauge rank is bounded. -/
theorem paperScaleCookLevinPiPlusPostGauge_multilinearizedRank_bound_of_rawPostGaugeBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (κ ℓ C : ℕ)
    (hraw : rawBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) ≤ C) :
    multilinearizedBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))) ≤ C :=
  le_trans
    (paperScaleCookLevinPiPlusPostGauge_multilinearizedRank_le_rawPostGaugeRank
      M htb hns κ ℓ)
    hraw

/-! ## Axiom audit anchors -/

#print axioms multilinearizedBlockedSpdpRank_le_rawBlockedSpdpRank
#print axioms piPlusMultilinearizedGauge_rank_le_rawPostGaugeRank
#print axioms paperScaleCookLevinPiPlusPostGauge_multilinearizedRank_le_rawPostGaugeRank
#print axioms paperScaleCookLevinPiPlusPostGauge_multilinearizedRank_bound_of_rawPostGaugeBound

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
