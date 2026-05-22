import PallLean.Paper93.DeepMath.PathC.PiPlusBoundaryQuotient
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedAction

/-!
# Concrete Route-W boundary projection candidates

`PiPlusBoundaryQuotient` introduced the abstract projection socket needed for
Route W.  This file makes the next structural choice explicit.

There are two nearby maps:

* `cookLevinPiPlusForwardThenBoundaryProject_paperScale` is the already-existing
  Boolean-projected `Pi+` action, `booleanNormalize ∘ Pi+`.  This is the right
  *factor transport* map, but it is not automatically a projection; idempotence
  is recorded below as a genuine obligation rather than assumed.

* `cookLevinBoundaryQuotientProject_paperScale` is the actual boundary quotient
  projection, `booleanNormalize`.  It is idempotent kernel-cleanly and is the map
  that can fill the `project` field of a `BoundaryQuotientCompressionCertificate`
  once the transformed factor family has already been transported into the
  `Pi+ᵦ` coordinates.

This separation avoids the fake step `booleanNormalize ∘ Pi+` being treated as a
quotient projection merely because it ends in normal form.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Generic Route-W boundary quotient projection: Boolean normal-form reduction.
This is the paper-ambient quotient map identifying boundary representatives
modulo `Xᵢ^k = Xᵢ` for positive powers. -/
noncomputable abbrev booleanBoundaryQuotientProject (N : ℕ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ :=
  zeroProfileBooleanNormalizeLinearMap (n := N)

@[simp] theorem booleanBoundaryQuotientProject_apply {N : ℕ}
    (p : MvPolynomial (Fin N) ℚ) :
    booleanBoundaryQuotientProject N p = zeroProfileBooleanNormalize p := rfl

/-- The Boolean boundary quotient is genuinely idempotent. -/
theorem booleanBoundaryQuotientProject_idempotent (N : ℕ) :
    (booleanBoundaryQuotientProject N).comp (booleanBoundaryQuotientProject N) =
      booleanBoundaryQuotientProject N := by
  exact zeroProfileBooleanNormalizeLinearMap_idempotent (n := N)

/-- Paper-scale Route-W boundary quotient projection for the Cook--Levin SAT
ambient.  This is intentionally just the quotient projection, not the preceding
invertible `Pi+` transport. -/
noncomputable abbrev cookLevinBoundaryQuotientProject_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns :=
  booleanBoundaryQuotientProject
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars

@[simp] theorem cookLevinBoundaryQuotientProject_paperScale_apply
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    cookLevinBoundaryQuotientProject_paperScale M htb hns p =
      zeroProfileBooleanNormalize p := rfl

/-- Paper-scale idempotence for the concrete boundary quotient projection. -/
theorem cookLevinBoundaryQuotientProject_paperScale_idempotent
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    (cookLevinBoundaryQuotientProject_paperScale M htb hns).comp
        (cookLevinBoundaryQuotientProject_paperScale M htb hns) =
      cookLevinBoundaryQuotientProject_paperScale M htb hns := by
  exact booleanBoundaryQuotientProject_idempotent
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars

/-- The tempting natural composite `booleanNormalize ∘ Pi+` at paper scale.
This is useful for transporting factors, but it is not by itself known to be an
idempotent quotient projection. -/
noncomputable abbrev cookLevinPiPlusForwardThenBoundaryProject_paperScale
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns :=
  cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns

@[simp] theorem cookLevinPiPlusForwardThenBoundaryProject_paperScale_apply
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    cookLevinPiPlusForwardThenBoundaryProject_paperScale M htb hns p =
      zeroProfileBooleanNormalize
        ((cookLevinPiPlusSATTransform_paperScale M htb hns).gauge p) := by
  rfl

/-- Honest idempotence obligation for the forward-then-boundary candidate.
Route W should not silently use this map as the certificate projection unless
this proposition is proved (or the map is replaced by the normal-form projection
above after transporting the factor family). -/
def CookLevinPiPlusForwardThenBoundaryProjectIdempotent
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  (cookLevinPiPlusForwardThenBoundaryProject_paperScale M htb hns).comp
      (cookLevinPiPlusForwardThenBoundaryProject_paperScale M htb hns) =
    cookLevinPiPlusForwardThenBoundaryProject_paperScale M htb hns

/-- If the forward-then-boundary map is later proved idempotent, it can be used
as a `BoundaryQuotientCompressionCertificate.project`.  This theorem is only a
named handoff; it does not assert the obligation. -/
theorem cookLevinPiPlusForwardThenBoundaryProject_paperScale_idempotent_of_obligation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hidem : CookLevinPiPlusForwardThenBoundaryProjectIdempotent M htb hns) :
    (cookLevinPiPlusForwardThenBoundaryProject_paperScale M htb hns).comp
        (cookLevinPiPlusForwardThenBoundaryProject_paperScale M htb hns) =
      cookLevinPiPlusForwardThenBoundaryProject_paperScale M htb hns :=
  hidem

/-! ## Axiom audit anchors -/

#print axioms booleanBoundaryQuotientProject_idempotent
#print axioms cookLevinBoundaryQuotientProject_paperScale_idempotent
#print axioms cookLevinPiPlusForwardThenBoundaryProject_paperScale_apply
#print axioms cookLevinPiPlusForwardThenBoundaryProject_paperScale_idempotent_of_obligation

end PallLean.Paper93.DeepMath.PathC
