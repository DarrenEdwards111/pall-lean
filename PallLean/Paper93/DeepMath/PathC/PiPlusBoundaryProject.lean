import PallLean.Paper93.DeepMath.PathC.PiPlusBoundaryQuotient
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedAction
import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanityProjectedRowObstruction

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
open SPDP
open SymmetricPowerBound
open PallLean.Paper93
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


/-! ## Booleanity one-coordinate collapse projects

The previous Booleanity analysis produced a paper-faithful one-coordinate
collapse for the asymmetric `Π+` residues.  There are two natural coefficient
maps:

* the raw candidate requested first, `rename collapse ∘ booleanNormalize`;
* the genuine quotient-shaped candidate, `booleanNormalize ∘ rename collapse ∘
  booleanNormalize`, which re-normalizes after the non-injective rename has
  identified coordinates.

The second form is the one that can serve Route W: the final Boolean reduction
is essential because a non-injective rename can turn a multilinear monomial such
as `X_false * X_true` into `X₀^2`.
-/

/-- Raw candidate: collapse after Boolean normalization.  This is useful for
calculation, but because the collapse rename is non-injective it need not land in
Boolean normal form and should not be used directly as the Route-W projection. -/
noncomputable def booleanityCollapseAfterNormalizeProject
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  (MvPolynomial.rename
      (BoolPoly.booleanityOneCoordinateCollapseMap M n hn2 htb hns D v)).toLinearMap.comp
    (zeroProfileBooleanNormalizeLinearMap
      (n := (cook_levin_compilation M n hn2 htb hns).numVars))

@[simp] theorem booleanityCollapseAfterNormalizeProject_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    booleanityCollapseAfterNormalizeProject M n hn2 htb hns D v p =
      MvPolynomial.rename
        (BoolPoly.booleanityOneCoordinateCollapseMap M n hn2 htb hns D v)
        (zeroProfileBooleanNormalize p) := rfl

/-- Route-W Booleanity project: normalize, collapse the two local `Π+` residues
to the paper's one Boolean coordinate, then normalize again. -/
noncomputable def booleanityOneCoordinateBoundaryProject
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    SATDeciderGaugeSpace M n hn2 htb hns →ₗ[ℚ]
      SATDeciderGaugeSpace M n hn2 htb hns :=
  (zeroProfileBooleanNormalizeLinearMap
      (n := (cook_levin_compilation M n hn2 htb hns).numVars)).comp
    (booleanityCollapseAfterNormalizeProject M n hn2 htb hns D v)

@[simp] theorem booleanityOneCoordinateBoundaryProject_apply
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v p =
      zeroProfileBooleanNormalize
        (MvPolynomial.rename
          (BoolPoly.booleanityOneCoordinateCollapseMap M n hn2 htb hns D v)
          (zeroProfileBooleanNormalize p)) := rfl

/-- Idempotence obligation for the Route-W one-coordinate Booleanity project.
This is the right map to try to prove idempotent; the raw
`rename ∘ booleanNormalize` candidate is deliberately not used as the
certificate projection. -/
def BooleanityOneCoordinateBoundaryProjectIdempotent
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) : Prop :=
  (booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v).comp
      (booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v) =
    booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v

/-- Handoff from the idempotence obligation to the exact certificate field. -/
theorem booleanityOneCoordinateBoundaryProject_idempotent_of_obligation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (hidem : BooleanityOneCoordinateBoundaryProjectIdempotent
      M n hn2 htb hns D v) :
    (booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v).comp
        (booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v) =
      booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v :=
  hidem


/-- The one-coordinate Route-W project sends the actual Booleanity post-row into
`W_booleanity`.  This is the Booleanity-slot profile-containment atom: after
normalization and collapse, the asymmetric true residue has become the constant
compiled-basis row. -/
theorem booleanityOneCoordinateBoundaryProject_cookLevinBooleanityPostRow_mem_interfaceSpace
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars) :
    booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v
        (BoolPoly.cookLevinBooleanityPostRow M n hn2 htb hns D v) ∈
      interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity := by
  rw [booleanityOneCoordinateBoundaryProject_apply]
  have hnorm : zeroProfileBooleanNormalize
      (BoolPoly.cookLevinBooleanityPostRow M n hn2 htb hns D v) =
        BoolPoly.cookLevinBooleanityPostRow M n hn2 htb hns D v := by
    unfold BoolPoly.cookLevinBooleanityPostRow
    exact zeroProfileBooleanNormalize_mlProj _
  rw [hnorm]
  rw [BoolPoly.rename_booleanityOneCoordinateCollapseMap_cookLevinBooleanityPostRow_eq_one]
  simp
  exact one_mem_interfaceSpace_compiledBasis_of_not_transitionRight B κ ℓ
    ConstraintType.booleanity (by simp)

/-- Rank direction for the collapse projection: the image rank is bounded by the
source rank.  This is the safe direction supplied by `Submodule.finrank_map_le`;
it does **not** by itself recover a polynomial bound on the original uncollapsed
row space from a bound on the collapsed/projected row space. -/
theorem booleanityOneCoordinateBoundaryProject_finrank_image_le
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (v : Fin (cook_levin_compilation M n hn2 htb hns).numVars)
    (W : Submodule ℚ (SATDeciderGaugeSpace M n hn2 htb hns))
    [Module.Finite ℚ W] :
    Module.finrank ℚ
        (Submodule.map
          (booleanityOneCoordinateBoundaryProject M n hn2 htb hns D v) W) ≤
      Module.finrank ℚ W := by
  exact Submodule.finrank_map_le _ _

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

#print axioms booleanityCollapseAfterNormalizeProject_apply
#print axioms booleanityOneCoordinateBoundaryProject_apply
#print axioms booleanityOneCoordinateBoundaryProject_idempotent_of_obligation
#print axioms booleanityOneCoordinateBoundaryProject_cookLevinBooleanityPostRow_mem_interfaceSpace
#print axioms booleanityOneCoordinateBoundaryProject_finrank_image_le
#print axioms booleanBoundaryQuotientProject_idempotent
#print axioms cookLevinBoundaryQuotientProject_paperScale_idempotent
#print axioms cookLevinPiPlusForwardThenBoundaryProject_paperScale_apply
#print axioms cookLevinPiPlusForwardThenBoundaryProject_paperScale_idempotent_of_obligation

end PallLean.Paper93.DeepMath.PathC
