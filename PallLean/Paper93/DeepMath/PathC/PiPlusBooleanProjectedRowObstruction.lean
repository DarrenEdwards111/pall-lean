import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedRawPullbackCriterion

/-!
# Local obstruction to same-window Pi+ row pullback

The previous row-certificate criterion is useful as a sufficient condition, but
it is too strong as a theorem target: the Boolean-projected `Pi+` action can turn
a `κ = 0` target row into the raw pullback of a `κ = 1` source row.

This file records the local obstruction and defines the corrected next target:
a *windowed* raw-pullback certificate where the source derivative list may be
larger than the target list.  That is the shape compatible with the local
Hadamard calculation.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PallLean.Paper93.NFrame
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- The inverse half-Hadamard matrix for the local two-variable `Pi+` block. -/
noncomputable def piPlusHadamard2InvMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 / 2 : ℚ), (1 / 2 : ℚ); (1 / 2 : ℚ), (-1 / 2 : ℚ)]

/-- The inverse local polynomial substitution. -/
noncomputable def piPlusHadamard2InvGauge :
    MvPolynomial (Fin 2) ℚ →ₗ[ℚ] MvPolynomial (Fin 2) ℚ :=
  rationalMatrixSubstGauge piPlusHadamard2InvMatrix

/-- The inverse half-Hadamard sends `X₀ - X₁` to `X₁`. -/
theorem piPlusHadamard2InvGauge_sub_X_zero_X_one :
    piPlusHadamard2InvGauge
      ((X (0 : Fin 2) - X (1 : Fin 2)) : MvPolynomial (Fin 2) ℚ) =
      X (1 : Fin 2) := by
  unfold piPlusHadamard2InvGauge piPlusHadamard2InvMatrix
  simp [rationalMatrixSubstGauge_X, rationalMatrixLinearForm,
    Fin.sum_univ_two, sub_eq_add_neg]
  module

/-- Local obstruction witness: the Boolean-projected image of `X₀X₁`, pulled
back through raw inverse `Pi+`, is `X₁`. -/
theorem piPlusHadamard2InvGauge_booleanProjected_pair :
    piPlusHadamard2InvGauge
      (zeroProfileBooleanNormalize
        (piPlusHadamard2Gauge
          ((X (0 : Fin 2)) * (X (1 : Fin 2)) : MvPolynomial (Fin 2) ℚ))) =
      X (1 : Fin 2) := by
  rw [zeroProfileBooleanNormalize_piPlusHadamard2Gauge_mul_pair]
  exact piPlusHadamard2InvGauge_sub_X_zero_X_one

/-- No constant multiple of `X₀X₁` can equal `X₁`.  Evaluating at
`X₀ = 0, X₁ = 1` separates them. -/
theorem not_exists_constant_mul_pair_eq_X_one :
    ¬ ∃ c : ℚ,
      ((C c) * ((X (0 : Fin 2)) * (X (1 : Fin 2))) : MvPolynomial (Fin 2) ℚ) =
        X (1 : Fin 2) := by
  rintro ⟨c, h⟩
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (0 : ℚ) else 1)) h
  simp at heval

/-- The local obstruction in words: same-window `κ = 0` pullback cannot be
represented by a degree-zero/source-empty row for `X₀X₁`; the pulled-back row is
`X₁`, which requires differentiating in the `X₀` direction. -/
theorem local_same_window_constant_row_obstruction :
    ¬ ∃ c : ℚ,
      ((C c) * ((X (0 : Fin 2)) * (X (1 : Fin 2))) : MvPolynomial (Fin 2) ℚ) =
        piPlusHadamard2InvGauge
          (zeroProfileBooleanNormalize
            (piPlusHadamard2Gauge
              ((X (0 : Fin 2)) * (X (1 : Fin 2)) : MvPolynomial (Fin 2) ℚ))) := by
  rw [piPlusHadamard2InvGauge_booleanProjected_pair]
  exact not_exists_constant_mul_pair_eq_X_one

/-- Positive local replacement: the same obstructing row is recovered by a
one-derivative source row.  This is the kernel-checked reason the corrected
criterion must be windowed rather than same-window. -/
theorem local_window_one_row_realization :
    piPlusHadamard2InvGauge
      (zeroProfileBooleanNormalize
        (piPlusHadamard2Gauge
          ((X (0 : Fin 2)) * (X (1 : Fin 2)) : MvPolynomial (Fin 2) ℚ))) =
      mlProj
        ((1 : MvPolynomial (Fin 2) ℚ) *
          iterDerivList [(0 : Fin 2)]
            (((X (0 : Fin 2)) * (X (1 : Fin 2))) : MvPolynomial (Fin 2) ℚ)) := by
  rw [piPlusHadamard2InvGauge_booleanProjected_pair]
  simp [iterDerivList]
  symm
  change mlProj (MvPolynomial.monomial (Finsupp.single (1 : Fin 2) 1) (1 : ℚ)) =
    MvPolynomial.monomial (Finsupp.single (1 : Fin 2) 1) (1 : ℚ)
  rw [mlProj_monomial]
  simp [Finsupp.IsMultilinear]

/-! ## Corrected windowed row certificate -/

/-- Corrected windowed raw-pullback certificate.

Compared with `PiPlusBooleanProjectedRawPullbackRowCertificate`, this allows the
source derivative list `S'` to differ from the target list `S`, with explicit
budget bounds `κ' ≤ κ + extraK` and `ℓ' ≤ ℓ + extraL`.  The local obstruction
above shows why this extra window is necessary. -/
def PiPlusBooleanProjectedWindowedRawPullbackRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∃ (κ' ℓ' : Nat)
        (S' : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
        (m' : SATDeciderGaugeSpace M n hn2 htb hns),
        κ' ≤ κ + extraK ∧
          ℓ' ≤ ℓ + extraL ∧
            S'.length = κ' ∧
              m'.totalDegree ≤ ℓ' ∧
                m'.vars ⊆ S'.toFinset ∧
                  isBlockAdmissible
                    (cook_levin_compilation M n hn2 htb hns).partition S' ∧
                    piP.equiv.symm
                      (mlProj (m * iterDerivList S
                        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))) =
                      mlProj (m' * iterDerivList S' p)

/-- Paper-scale corrected windowed row certificate. -/
abbrev PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedWindowedRawPullbackRowCertificate extraK extraL
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-! ## Axiom audit anchors -/

#print axioms piPlusHadamard2InvGauge_sub_X_zero_X_one
#print axioms piPlusHadamard2InvGauge_booleanProjected_pair
#print axioms not_exists_constant_mul_pair_eq_X_one
#print axioms local_same_window_constant_row_obstruction
#print axioms local_window_one_row_realization

end PallLean.Paper93.DeepMath.PathC
