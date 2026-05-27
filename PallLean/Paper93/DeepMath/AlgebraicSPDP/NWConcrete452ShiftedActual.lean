import PallLean.Paper93.DeepMath.AlgebraicSPDP.NWConcrete452Shifted

/-!
# Concrete NW(4,5,2) Shifted Rows in the Actual SPDP Subspace

`NWConcrete452Shifted` proves the finite shifted-leading count `1550` and
packages the strong lower bound behind an abstract rank-containment premise.
This file removes that artificial premise for the actual shifted candidate
rows.

For every concrete candidate row `(D,a,shift)`, the polynomial

`shiftPolynomial shift * ∂_D(NW_{4,5,2})`

is an actual generator of `SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)`.
Consequently, coefficient projections of any selected shifted candidate
subfamily have row rank bounded by the real `SPDP.spdpRank 2 1` of the
concrete NW polynomial.

The remaining strong-bound payload is now exactly the leading-monomial
selection theorem: choose one candidate per `ShiftedLeadShape` and prove the
triangular leading conditions.  The containment in the actual SPDP object is
proved here.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

open scoped BigOperators

namespace NW452

/-- Full exponent vectors for monomials in the `20` concrete variables. -/
abbrev Exponent20 := Fin 20 →₀ Nat

/-- The degree-`≤ 1` shift polynomial attached to a shifted candidate. -/
noncomputable def shiftPolynomial : ShiftLE1 -> MvPolynomial (Fin 20) ℚ
  | none => 1
  | some v => MvPolynomial.X v

/-- The selected shift polynomial has total degree at most `1`. -/
theorem shiftPolynomial_totalDegree_le_one (s : ShiftLE1) :
    (shiftPolynomial s).totalDegree <= 1 := by
  cases s with
  | none =>
      simp [shiftPolynomial]
  | some v =>
      simp [shiftPolynomial, MvPolynomial.totalDegree_X]

/-- Every explicit two-point window has cardinality `2`. -/
theorem window2_toFinset_card (D : Window2) :
    D.toFinset.card = 2 := by
  cases D <;> decide

/-- The actual shifted partial polynomial represented by a concrete shifted
candidate. -/
noncomputable def shiftedCandidatePolynomial (c : ShiftedCandidate) :
    MvPolynomial (Fin 20) ℚ :=
  shiftPolynomial c.shift *
    SPDP.iterDerivList (nwDerivativeWindowList enc code c.D.toFinset c.a)
      (nwMvPolynomial enc code)

/-- Every shifted candidate polynomial is a genuine row-generator in the
actual shifted-partial-derivative subspace at `(κ,ℓ)=(2,1)`. -/
theorem shiftedCandidatePolynomial_mem_spdpSubspace (c : ShiftedCandidate) :
    shiftedCandidatePolynomial c ∈
      SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code) := by
  apply Submodule.subset_span
  refine ⟨nwDerivativeWindowList enc code c.D.toFinset c.a,
    shiftPolynomial c.shift, ?_, ?_, ?_⟩
  · rw [nwDerivativeWindowList_length, window2_toFinset_card]
  · exact shiftPolynomial_totalDegree_le_one c.shift
  · rfl

/-- Coefficient projection to the full exponent-vector row model. -/
noncomputable def shiftedCoeffProjection :
    MvPolynomial (Fin 20) ℚ →ₗ[ℚ] (Exponent20 -> ℚ) where
  toFun p := fun e => MvPolynomial.coeff e p
  map_add' p q := by
    ext e
    simp [MvPolynomial.coeff_add]
  map_smul' c p := by
    ext e
    simp [MvPolynomial.coeff_smul]

/-- The full coefficient row of a shifted candidate. -/
noncomputable def shiftedCandidateRows (c : ShiftedCandidate) :
    Exponent20 -> ℚ :=
  shiftedCoeffProjection (shiftedCandidatePolynomial c)

/-- Each shifted candidate row is the coefficient projection of an actual
element of the concrete SPDP subspace. -/
theorem shiftedCandidateRows_mem_actual_spdp_image (c : ShiftedCandidate) :
    shiftedCandidateRows c ∈
      Submodule.map shiftedCoeffProjection
        (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)) := by
  refine ⟨shiftedCandidatePolynomial c,
    shiftedCandidatePolynomial_mem_spdpSubspace c, ?_⟩
  rfl

/-- Any selected subfamily of shifted candidate rows has rank bounded by the
actual concrete shifted-partial rank. -/
theorem shiftedShapeRows_finrank_le_actual_spdpRank
    (select : ShiftedLeadShape -> ShiftedCandidate) :
    (Set.range (fun s : ShiftedLeadShape => shiftedCandidateRows (select s))).finrank ℚ <=
      SPDP.spdpRank 2 1 (nwMvPolynomial enc code) := by
  classical
  let W : Submodule ℚ (Exponent20 -> ℚ) :=
    Submodule.map shiftedCoeffProjection
      (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code))
  have hspan :
      Submodule.span ℚ
          (Set.range (fun s : ShiftedLeadShape =>
            shiftedCandidateRows (select s))) ≤ W := by
    apply Submodule.span_le.mpr
    intro row hrow
    rcases hrow with ⟨s, rfl⟩
    exact shiftedCandidateRows_mem_actual_spdp_image (select s)
  have hmono :
      (Set.range (fun s : ShiftedLeadShape =>
        shiftedCandidateRows (select s))).finrank ℚ <= Module.finrank ℚ W := by
    simpa using Submodule.finrank_mono hspan
  have hmap :
      Module.finrank ℚ W <=
        Module.finrank ℚ (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)) := by
    simpa [W] using
      (Submodule.finrank_map_le shiftedCoeffProjection
        (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)))
  exact le_trans hmono hmap

/-- Coefficient projection to a user-chosen `Nat` code for exponent vectors.

This avoids putting an arbitrary linear order on raw `Finsupp` exponent
vectors.  The shifted-leading argument can choose a concrete decoder and then
use the standard order on `Nat` for the triangular leading-monomial engine. -/
noncomputable def shiftedCoeffProjectionByCode
    (decode : Nat -> Exponent20) :
    MvPolynomial (Fin 20) ℚ →ₗ[ℚ] (Nat -> ℚ) where
  toFun p := fun n => MvPolynomial.coeff (decode n) p
  map_add' p q := by
    ext n
    simp [MvPolynomial.coeff_add]
  map_smul' c p := by
    ext n
    simp [MvPolynomial.coeff_smul]

/-- The coefficient row of a shifted candidate in a chosen `Nat`-coded
monomial coordinate system. -/
noncomputable def shiftedCandidateRowsByCode
    (decode : Nat -> Exponent20) (c : ShiftedCandidate) :
    Nat -> ℚ :=
  shiftedCoeffProjectionByCode decode (shiftedCandidatePolynomial c)

/-- Any selected subfamily of `Nat`-coded shifted candidate rows has rank
bounded by the actual concrete shifted-partial rank. -/
theorem shiftedShapeRowsByCode_finrank_le_actual_spdpRank
    (decode : Nat -> Exponent20)
    (select : ShiftedLeadShape -> ShiftedCandidate) :
    (Set.range (fun s : ShiftedLeadShape =>
      shiftedCandidateRowsByCode decode (select s))).finrank ℚ <=
      SPDP.spdpRank 2 1 (nwMvPolynomial enc code) := by
  classical
  let W : Submodule ℚ (Nat -> ℚ) :=
    Submodule.map (shiftedCoeffProjectionByCode decode)
      (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code))
  have hspan :
      Submodule.span ℚ
          (Set.range (fun s : ShiftedLeadShape =>
            shiftedCandidateRowsByCode decode (select s))) ≤ W := by
    apply Submodule.span_le.mpr
    intro row hrow
    rcases hrow with ⟨s, rfl⟩
    refine ⟨shiftedCandidatePolynomial (select s),
      shiftedCandidatePolynomial_mem_spdpSubspace (select s), ?_⟩
    rfl
  have hmono :
      (Set.range (fun s : ShiftedLeadShape =>
        shiftedCandidateRowsByCode decode (select s))).finrank ℚ <=
          Module.finrank ℚ W := by
    simpa using Submodule.finrank_mono hspan
  have hmap :
      Module.finrank ℚ W <=
        Module.finrank ℚ (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)) := by
    simpa [W] using
      (Submodule.finrank_map_le (shiftedCoeffProjectionByCode decode)
        (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)))
  exact le_trans hmono hmap

/-- Strong shifted-leading lower bound with the SPDP containment now supplied
by actual shifted candidate rows in a concrete `Nat`-coded monomial order.

The remaining hypotheses are the real NW shifted-leading payload:

* choose one concrete shifted candidate for each of the `1550` lead shapes;
* choose a coefficient decoder from `Nat` codes to exponent vectors;
* assign its leading exponent;
* prove the triangular leading-row conditions.
-/
theorem spdpRank_nw452_ge_1550_of_shiftedShapeSelectionByCode
    (decode : Nat -> Exponent20)
    (select : ShiftedLeadShape -> ShiftedCandidate)
    (lead : ShiftedLeadShape -> Nat)
    (hlead_ne_zero :
      ∀ i, shiftedCandidateRowsByCode decode (select i) (lead i) ≠ 0)
    (hlead_max :
      ∀ i m, lead i < m ->
        shiftedCandidateRowsByCode decode (select i) m = 0)
    (hlead_inj : Function.Injective lead) :
    1550 <= SPDP.spdpRank 2 1 (nwMvPolynomial enc code) := by
  exact spdpRank_nw452_ge_1550_of_distinctLeadingRows
    (rows := fun s : ShiftedLeadShape => shiftedCandidateRowsByCode decode (select s))
    (lead := lead)
    hlead_ne_zero
    hlead_max
    hlead_inj
    (shiftedShapeRowsByCode_finrank_le_actual_spdpRank decode select)

/-! ## Axiom audit -/

#print axioms shiftedCandidatePolynomial_mem_spdpSubspace
#print axioms shiftedShapeRows_finrank_le_actual_spdpRank
#print axioms shiftedShapeRowsByCode_finrank_le_actual_spdpRank
#print axioms spdpRank_nw452_ge_1550_of_shiftedShapeSelectionByCode

end NW452

end PallLean.Paper93.DeepMath.AlgebraicSPDP
