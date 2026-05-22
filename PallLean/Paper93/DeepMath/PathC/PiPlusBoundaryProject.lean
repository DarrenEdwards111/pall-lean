import PallLean.Paper93.DeepMath.PathC.PiPlusBoundaryQuotient
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedAction

/-!
# Boolean boundary projection candidates

`PiPlusBoundaryQuotient` introduced an abstract linear projection socket on the
coefficient-space post-row polynomials.  At this coefficient level, the
paper-licensed quotient is Boolean/multilinear normal form, i.e.
`Xᵢ^k = Xᵢ` (paper Remark 21), implemented by `zeroProfileBooleanNormalize`.

Level separation:

* operational `Π+` is invertible and block-local; it is transport, not a
  projection;
* `can(·)` is the paper's window-level quotient (Definition 20), used upstream
  to choose canonical row indices;
* `booleanNormalize` is the coefficient-level quotient used here to compare
  post-row polynomials modulo the Boolean ideal.

Thus the actual Route-W certificate projection below is `booleanNormalize`.  The
final map below still separates the tempting `booleanNormalize ∘ Π+` composite
and records its idempotence as an obligation rather than assuming it.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Boolean normal-form reduction: the coefficient-level quotient
`Xᵢ^k = Xᵢ` used by the Route-W boundary certificate. -/
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

/-- Paper-scale Boolean normal-form projection for the Cook--Levin SAT ambient.
This is intentionally just Boolean normalization, not the preceding invertible
`Pi+` transport. -/
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
