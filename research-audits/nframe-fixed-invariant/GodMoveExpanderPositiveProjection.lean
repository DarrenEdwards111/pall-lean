import GodMoveExpanderScreen
import GodMovePositiveBoundaryMap
import GodMoveSATUnitExtraction

/-!
# Expander-protected positive boundary coordinates for the actual SAT minor

The input labels are the k-subsets indexing the existing coefficient identity
minor of the extracted unit-query SAT source. Actual graph expansion makes
their retained parity screens distinct after a bounded edge erasure. A finite
encoding of those screens selects distinct rows of a positive Vandermonde
external matrix. The coefficient boundary map sends the actual derivative
rows to precisely those external rows, so their independence is derived.

This is a linear map on coefficient rows, not a substitution of polynomial
variables. Its finite enumerations are noncomputable; it is not an efficient
SAT algorithm. Preserving the minor requires at least choose(m,k) boundary
coordinates. No SAT runtime bound or rank amplification is asserted.
-/

namespace GodMoveExpanderPositiveProjection

open MvPolynomial SPDP MultilinearSPDP Matrix
open GodMoveMonomialMinor GodMoveExpanderScreen GodMovePositiveBoundaryMap
open GodMoveSATUnitExtraction GodMoveMachineSourceMinor GodMoveUnitCharacteristic
open GodMoveMachineFaceExtraction
open PallLean.Paper93.DeepMath.PathB ComposableMachine SeparationTarget
open scoped BigOperators

variable {m k : ℕ} {Edge : Type*} [Fintype Edge] [DecidableEq Edge]

/-- All retained binary edge screens, including screens not realized by labels. -/
abbrev Screen (erased : Finset Edge) := {e : Edge // e ∉ erased} → ZMod 2

/-- A finite code for the actual retained screen; no efficient enumeration claim. -/
noncomputable def screenLabel (G : TseitinGraph (Fin m) Edge)
    (erased : Finset Edge) (S : KSubset m k) : Fin (Fintype.card (Screen erased)) :=
  Fintype.equivFin (Screen erased) (screen G erased S.val)

theorem screenLabel_injective (G : TseitinGraph (Fin m) Edge) {c : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset Edge) (herased : erased.card < 2 * c) :
    Function.Injective (screenLabel (k := k) G erased) := by
  intro S T heq
  apply Subtype.ext
  exact screen_injective_on_card G hexp (by simpa using hwindow) erased herased
    (kSubset_size S) (kSubset_size T) ((Fintype.equivFin _).injective heq)

/-- The retained screen type has enough rows for the nonvacuous positive
external matrix with exactly choose(m,k) columns. -/
theorem minor_le_screen_card (G : TseitinGraph (Fin m) Edge) {c : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset Edge) (herased : erased.card < 2 * c) :
    Nat.choose m k ≤ Fintype.card (Screen erased) := by
  simpa only [kSubset_card, Fintype.card_fin] using
    Fintype.card_le_of_injective _ (screenLabel_injective G hexp hwindow erased herased)

/-- The boundary reads the actual selected coefficients and mixes them using
the positive external matrix. The sum has choose(m,k) terms. -/
noncomputable def coefficientBoundary (G : TseitinGraph (Fin m) Edge)
    (erased : Finset Edge) (q : ℕ) : Poly m →ₗ[ℚ] (Fin q → ℚ) where
  toFun p j := ∑ S : KSubset m k, coeff (complementaryColumn S.val) p *
    boundaryMatrix (Fintype.card (Screen erased)) q (screenLabel G erased S) j
  map_add' p p' := by
    ext j
    simp only [coeff_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  map_smul' a p := by
    ext j
    simp only [coeff_smul, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc,
      RingHom.id_apply]

/-- The actual coefficient identity minor becomes the selected moment rows. -/
theorem coefficientBoundary_derivativeRow (G : TseitinGraph (Fin m) Edge)
    (erased : Finset Edge) (q : ℕ) (T : KSubset m k) :
    coefficientBoundary (k := k) G erased q (derivativeRow T.val) =
      boundaryMatrix (Fintype.card (Screen erased)) q (screenLabel G erased T) := by
  classical
  ext j
  simp [coefficientBoundary, coefficient_identity]

/-- Expansion plus positive external data preserves the entire existing minor
when the boundary has at least its dimension. -/
theorem boundary_derivativeRows_linearIndependent
    (G : TseitinGraph (Fin m) Edge) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q) :
    LinearIndependent ℚ (fun T : KSubset m k =>
      coefficientBoundary (k := k) G erased q (derivativeRow T.val)) := by
  classical
  let e := Fintype.equivFin (KSubset m k)
  have hi := (screenLabel_injective G hexp hwindow erased herased).comp e.symm.injective
  have hli := selected_rows_linearIndependent
    (fun i => screenLabel G erased (e.symm i)) hi
    (by simpa only [kSubset_card] using hcapacity)
  simpa only [coefficientBoundary_derivativeRow, Function.comp_def, e.symm_apply_apply]
    using hli.comp e e.injective

/-- Faithful SAT correctness supplies the rows. No label or minor preservation
condition is added to the SAT-decider hypothesis. -/
theorem sat_boundary_rows_linearIndependent
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (G : TseitinGraph (Fin m) Edge) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Nat.choose m k ≤ q) :
    LinearIndependent ℚ (fun S : KSubset m k =>
      coefficientBoundary (k := k) G erased q
        (iterDerivList S.val.toList
          (unitExtraction m (machineSource M T (unitFormula m) m)))) := by
  rw [unitExtraction_of_decides M T hD m]
  exact boundary_derivativeRows_linearIndependent G hexp hwindow erased herased hcapacity

/-- Encode and decode every linear combination of the actual derivative
minor. The decoder recovers its signed coordinates in the displayed finite
enumeration; it does not recover arbitrary source polynomials. -/
theorem decode_minor_combination (G : TseitinGraph (Fin m) Edge) {c q : ℕ}
    (hexp : G.HasExpansion c) (hwindow : 4 * k ≤ m)
    (erased : Finset Edge) (herased : erased.card < 2 * c)
    (hcapacity : Fintype.card (KSubset m k) ≤ q)
    (a : Fin (Fintype.card (KSubset m k)) → ℚ) :
    let e := Fintype.equivFin (KSubset m k)
    let f := fun i => screenLabel G erased (e.symm i)
    (coefficientBoundary (k := k) G erased q
      (∑ i, a i • derivativeRow (e.symm i).val)) ᵥ* selectedDecoder f hcapacity = a := by
  classical
  dsimp only
  let e := Fintype.equivFin (KSubset m k)
  let f := fun i => screenLabel G erased (e.symm i)
  have hencode : coefficientBoundary (k := k) G erased q
      (∑ i, a i • derivativeRow (e.symm i).val) =
      a ᵥ* (boundaryMatrix (Fintype.card (Screen erased)) q).submatrix f id := by
    ext j
    simp [map_sum, coefficientBoundary_derivativeRow, Matrix.vecMul, dotProduct, f]
  rw [hencode]
  exact selected_decode_encode f
    ((screenLabel_injective G hexp hwindow erased herased).comp e.symm.injective)
    hcapacity a

/-- For any linear boundary, preserving these independent rows costs at least
the size of their actual identity minor. -/
theorem faithful_boundary_dimension {q : ℕ} (B : Poly m →ₗ[ℚ] (Fin q → ℚ))
    (hB : LinearIndependent ℚ (fun S : KSubset m k => B (derivativeRow S.val))) :
    Nat.choose m k ≤ q := by
  simpa only [kSubset_card, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hB.fintype_card_le_finrank

/-- The boundary size itself is superpolynomial at the logarithmic window;
the geometric map does not compress this minor into polynomial dimension. -/
theorem polynomial_dimension_insufficient (d q : ℕ)
    (hm : 2 ^ (max 20 (4 * (d + 1))) ≤ m) (hq : q ≤ m ^ d)
    (B : Poly m →ₗ[ℚ] (Fin q → ℚ)) :
    ¬ LinearIndependent ℚ (fun S : KSubset m (Nat.log 2 m) => B (derivativeRow S.val)) := by
  intro hB
  exact (not_le_of_gt (npow_lt_choose_log m d hm))
    ((faithful_boundary_dimension B hB).trans hq)

end GodMoveExpanderPositiveProjection

#print axioms GodMoveExpanderPositiveProjection.screenLabel_injective
#print axioms GodMoveExpanderPositiveProjection.minor_le_screen_card
#print axioms GodMoveExpanderPositiveProjection.coefficientBoundary_derivativeRow
#print axioms GodMoveExpanderPositiveProjection.boundary_derivativeRows_linearIndependent
#print axioms GodMoveExpanderPositiveProjection.sat_boundary_rows_linearIndependent
#print axioms GodMoveExpanderPositiveProjection.decode_minor_combination
#print axioms GodMoveExpanderPositiveProjection.faithful_boundary_dimension
#print axioms GodMoveExpanderPositiveProjection.polynomial_dimension_insufficient
