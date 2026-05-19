import PallLean.Paper93.DeepMath.PathC.PiPlusMultilinearizationRank

/-!
# Boolean-normalized Pi+ gauge

The paper's actual `Pi+` gauge for rank arguments is not raw `Pi+` in the full
polynomial ring.  It is raw `Pi+` followed by Boolean multilinearization:

`piPlus_bool_normalized = multilinearize ∘ Pi+`.

The rank proof factors accordingly:

1. the block-local `Pi+` step supplies a raw-rank monotonicity/invariance
   obligation, and
2. the multilinearization step is kernel-clean and rank non-increasing by
   `multilinearizedBlockedSpdpRank_le_rawBlockedSpdpRank`.

This file names that composition and gives the clean bridge theorem.  The
remaining mathematical payload is the paper's block-local raw-rank monotonicity
for `Pi+` and the Boolean/identity-minor preservation payload.
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

/-- The paper-faithful Boolean-normalized `Pi+` operator:
raw `Pi+` followed by multilinearization/Boolean normalization. -/
noncomputable def piPlus_bool_normalized
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars →
      BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars :=
  fun p => multilinearize (piP.gauge
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))

@[simp] theorem coe_piPlus_bool_normalized
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
    (piPlus_bool_normalized piP p :
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ) =
      zeroProfileBooleanNormalize (piP.gauge
        (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)) := rfl

/-- The previously defined Boolean `Pi+` map is exactly the paper's normalized
composition.  This theorem pins the naming to the paper terminology. -/
theorem piPlus_bool_normalized_eq_piPlusBool
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
    piPlus_bool_normalized piP p = piPlusBool piP p := rfl

/-- Linear-map packaging of the paper's Boolean-normalized `Pi+` operator. -/
noncomputable def piPlusBoolNormalizedLinearMap
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) :
    BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars →ₗ[ℚ]
      BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars :=
  piPlusBoolLinearMap piP

@[simp] theorem piPlusBoolNormalizedLinearMap_apply
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
    piPlusBoolNormalizedLinearMap piP p = piPlus_bool_normalized piP p := by
  rw [piPlus_bool_normalized_eq_piPlusBool]
  rfl

/-- Raw-rank monotonicity for the block-local `Pi+` step, stated on the raw row
surface that feeds the paper's multilinearization lemma.  This is the §37.1
payload, separated from the already-proved multilinearization non-increase. -/
def PiPlusRawRankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : ℕ) (p : SATDeciderGaugeSpace M n hn2 htb hns),
    rawBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piP.gauge p) ≤
      rawBlockedSpdpRank (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ p

/-- Kernel-clean composition theorem: raw block-local `Pi+` rank monotonicity plus
multilinearization non-increase gives rank monotonicity for the paper's
Boolean-normalized `Pi+` gauge. -/
theorem piPlus_bool_normalized_rank_le_of_rawRankMonotone
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hraw : PiPlusRawRankMonotonicity M n hn2 htb hns piP)
    (κ ℓ : ℕ)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars) :
    multilinearizedBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (piP.gauge (p : SATDeciderGaugeSpace M n hn2 htb hns)) ≤
      rawBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (p : SATDeciderGaugeSpace M n hn2 htb hns) :=
  le_trans
    (multilinearizedBlockedSpdpRank_le_rawBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
      (piP.gauge (p : SATDeciderGaugeSpace M n hn2 htb hns)))
    (hraw κ ℓ (p : SATDeciderGaugeSpace M n hn2 htb hns))

/-- Budget version: a raw source rank budget transfers through the paper's
Boolean-normalized `Pi+` gauge. -/
theorem piPlus_bool_normalized_rank_bound_of_rawRankMonotone_of_rawBudget
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hraw : PiPlusRawRankMonotonicity M n hn2 htb hns piP)
    (κ ℓ C : ℕ)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars)
    (hbudget : rawBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (p : SATDeciderGaugeSpace M n hn2 htb hns) ≤ C) :
    multilinearizedBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (piP.gauge (p : SATDeciderGaugeSpace M n hn2 htb hns)) ≤ C :=
  le_trans
    (piPlus_bool_normalized_rank_le_of_rawRankMonotone
      M n hn2 htb hns piP hraw κ ℓ p)
    hbudget

/-- Paper-scale version of the raw-rank monotonicity socket for the concrete
Cook--Levin `Pi+`. -/
abbrev PaperScaleCookLevinPiPlusRawRankMonotonicity
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusRawRankMonotonicity M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale composition theorem for the concrete Cook--Levin `Pi+`: once the
block-local raw-rank monotonicity payload is proved, the paper's
Boolean-normalized post-gauge rank is bounded by the raw source rank. -/
theorem paperScaleCookLevinPiPlus_bool_normalized_rank_le_of_rawRankMonotone
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hraw : PaperScaleCookLevinPiPlusRawRankMonotonicity M htb hns)
    (κ ℓ : ℕ)
    (p : BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) :
    multilinearizedBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge
          (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns)) ≤
      rawBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :=
  piPlus_bool_normalized_rank_le_of_rawRankMonotone
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hraw κ ℓ p

/-! ## Axiom audit anchors -/

#print axioms piPlus_bool_normalized_eq_piPlusBool
#print axioms piPlusBoolNormalizedLinearMap
#print axioms piPlus_bool_normalized_rank_le_of_rawRankMonotone
#print axioms piPlus_bool_normalized_rank_bound_of_rawRankMonotone_of_rawBudget
#print axioms paperScaleCookLevinPiPlus_bool_normalized_rank_le_of_rawRankMonotone

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
