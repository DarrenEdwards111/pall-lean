import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanRespectReduction

/-!
# Reducing normalized-input compatibility to killing Boolean residuals

For a linear `Pi+` gauge, normalized-input compatibility follows if the gauge
sends every Boolean-normalization residual `p - normalize p` to zero in the
Boolean ambient.  This is the algebraic ideal-style payload behind quotient
respect: the map descends once it kills the kernel of the Boolean projection.
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

/-- A linear full-ring map kills Boolean-normalization residuals if every
`p - normalize p` maps to zero in the Boolean ambient. -/
def KillsBooleanNormalizationResidual {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ p : MvPolynomial (Fin n) ℚ,
    F (p - zeroProfileBooleanNormalize p) ≈ᵦ 0

/-- Killing Boolean-normalization residuals implies normalized-input
compatibility. -/
theorem normalizedInputCompatible_of_killsBooleanNormalizationResidual {n : ℕ}
    (F : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hkill : KillsBooleanNormalizationResidual F) :
    NormalizedInputCompatible (fun p => F p) := by
  intro p
  have hzero := hkill p
  unfold BooleanAmbientEq at hzero ⊢
  have hlin : F (p - zeroProfileBooleanNormalize p) = F p - F (zeroProfileBooleanNormalize p) := by
    simp
  rw [hlin] at hzero
  have hneg : zeroProfileBooleanNormalize (F p - F (zeroProfileBooleanNormalize p)) = 0 := by
    simpa using hzero
  rw [zeroProfileBooleanNormalize_sub] at hneg
  exact (sub_eq_zero.mp hneg).symm

/-- A `Pi+` transform kills Boolean-normalization residuals if its raw linear
`gauge` kills them. -/
def PiPlusKillsBooleanNormalizationResidual
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  KillsBooleanNormalizationResidual
    (n := (cook_levin_compilation M n hn2 htb hns).numVars) piP.gauge

/-- Killing Boolean residuals discharges normalized-input compatibility for
`Pi+`. -/
theorem piPlusNormalizedInputCompatible_of_killsBooleanNormalizationResidual
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hkill : PiPlusKillsBooleanNormalizationResidual piP) :
    PiPlusNormalizedInputCompatible piP :=
  normalizedInputCompatible_of_killsBooleanNormalizationResidual piP.gauge hkill

/-- Paper-scale residual-killing payload for the concrete Cook--Levin `Pi+`
gauge. -/
def PaperScaleCookLevinPiPlusKillsBooleanNormalizationResidual
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusKillsBooleanNormalizationResidual
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale residual-killing discharges normalized-input compatibility. -/
theorem paperScaleCookLevinPiPlusNormalizedInputCompatible_of_killsBooleanNormalizationResidual
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hkill : PaperScaleCookLevinPiPlusKillsBooleanNormalizationResidual M htb hns) :
    PaperScaleCookLevinPiPlusNormalizedInputCompatible M htb hns :=
  piPlusNormalizedInputCompatible_of_killsBooleanNormalizationResidual
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hkill

/-- Identity-minor bridge consuming residual-killing instead of normalized-input
compatibility. -/
theorem paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_killsBooleanResidual_of_rawCompiledAgreement
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : DecidesSAT M → PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hkill : DecidesSAT M → PaperScaleCookLevinPiPlusKillsBooleanNormalizationResidual M htb hns)
    (hraw : DecidesSAT M → PaperScaleCookLevinPiPlusRawCompiledBooleanAmbientAgreement M htb hns) :
    PaperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation M htb hns :=
  paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_normalizedInputCompatible_of_rawCompiledAgreement
    M htb hns hsource
    (fun hdec => paperScaleCookLevinPiPlusNormalizedInputCompatible_of_killsBooleanNormalizationResidual
      M htb hns (hkill hdec))
    hraw

/-! ## Axiom audit anchors -/

#print axioms normalizedInputCompatible_of_killsBooleanNormalizationResidual
#print axioms piPlusNormalizedInputCompatible_of_killsBooleanNormalizationResidual
#print axioms paperScaleCookLevinPiPlusNormalizedInputCompatible_of_killsBooleanNormalizationResidual
#print axioms paperScaleCookLevinPiPlusBoolNormalizedNPIdentityMinorPreservation_of_sourceLower_of_killsBooleanResidual_of_rawCompiledAgreement

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
