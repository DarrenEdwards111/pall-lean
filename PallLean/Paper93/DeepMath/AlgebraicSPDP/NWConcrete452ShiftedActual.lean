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

/-! ## Canonical finite shape projection

The next layer fixes the concrete `NW_{4,5,2}` shifted-leading representatives
instead of accepting an arbitrary selection function.
-/

/-- First point of an explicit two-point window. -/
def Window2.leftPoint : Window2 -> Point
  | Window2.w01 => 0
  | Window2.w02 => 0
  | Window2.w03 => 0
  | Window2.w12 => 1
  | Window2.w13 => 1
  | Window2.w23 => 2

/-- Second point of an explicit two-point window. -/
def Window2.rightPoint : Window2 -> Point
  | Window2.w01 => 1
  | Window2.w02 => 2
  | Window2.w03 => 3
  | Window2.w12 => 2
  | Window2.w13 => 3
  | Window2.w23 => 3

/-- First point outside an explicit derivative window. -/
def Window2.outLeft : Window2 -> Point
  | Window2.w01 => 2
  | Window2.w02 => 1
  | Window2.w03 => 1
  | Window2.w12 => 0
  | Window2.w13 => 0
  | Window2.w23 => 0

/-- Second point outside an explicit derivative window. -/
def Window2.outRight : Window2 -> Point
  | Window2.w01 => 3
  | Window2.w02 => 3
  | Window2.w03 => 2
  | Window2.w12 => 3
  | Window2.w13 => 2
  | Window2.w23 => 1

/-- Complementary two-point window.  If `W` is read as a support pair, then
`W.complement` is the derivative window whose outside pair is `W`. -/
def Window2.complement : Window2 -> Window2
  | Window2.w01 => Window2.w23
  | Window2.w02 => Window2.w13
  | Window2.w03 => Window2.w12
  | Window2.w12 => Window2.w03
  | Window2.w13 => Window2.w02
  | Window2.w23 => Window2.w01

/-- The lower value in a concrete unordered two-value support. -/
def ValuePair2.leftValue : ValuePair2 -> Value
  | ValuePair2.v01 => 0
  | ValuePair2.v02 => 0
  | ValuePair2.v03 => 0
  | ValuePair2.v04 => 0
  | ValuePair2.v12 => 1
  | ValuePair2.v13 => 1
  | ValuePair2.v14 => 1
  | ValuePair2.v23 => 2
  | ValuePair2.v24 => 2
  | ValuePair2.v34 => 3

/-- The upper value in a concrete unordered two-value support. -/
def ValuePair2.rightValue : ValuePair2 -> Value
  | ValuePair2.v01 => 1
  | ValuePair2.v02 => 2
  | ValuePair2.v03 => 3
  | ValuePair2.v04 => 4
  | ValuePair2.v12 => 2
  | ValuePair2.v13 => 3
  | ValuePair2.v14 => 4
  | ValuePair2.v23 => 3
  | ValuePair2.v24 => 4
  | ValuePair2.v34 => 4

/-- The affine label through two point/value constraints. -/
def affineLabelThrough (x y : Point) (vx vy : Value) : Label :=
  let dx : Value := (y.val : Value) - (x.val : Value)
  let slope : Value := (vy - vx) * dx⁻¹
  (vx - slope * (x.val : Value), slope)

/-- Build a shifted candidate from residual values on the outside pair of a
derivative window. -/
def candidateFromResidual (D : Window2) (vLeft vRight : Value)
    (shift : ShiftLE1) : ShiftedCandidate where
  D := D
  a := affineLabelThrough D.outLeft D.outRight vLeft vRight
  shift := shift

/-- Canonical representative for each shifted-leading shape. -/
def shapeCandidate : ShiftedLeadShape -> ShiftedCandidate
  | Sum.inl (D, vLeft, vRight) =>
      candidateFromResidual D vLeft vRight none
  | Sum.inr (Sum.inl (D, vLeft, vRight, squareRight)) =>
      let shiftVar :=
        if squareRight then
          enc (D.outRight, vRight)
        else
          enc (D.outLeft, vLeft)
      candidateFromResidual D vLeft vRight (some shiftVar)
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit0, v1, v2, v3))) =>
      candidateFromResidual Window2.w03 v1 v2 (some (enc (3, v3)))
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit1, v0, v2, v3))) =>
      candidateFromResidual Window2.w13 v0 v2 (some (enc (3, v3)))
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit2, v0, v1, v3))) =>
      candidateFromResidual Window2.w23 v0 v1 (some (enc (3, v3)))
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit3, v0, v1, v2))) =>
      candidateFromResidual Window2.w23 v0 v1 (some (enc (2, v2)))
  | Sum.inr (Sum.inr (Sum.inr (W, pairAtRight, pair, singleValue))) =>
      let D := W.complement
      let pairLeft := pair.leftValue
      let pairRight := pair.rightValue
      if pairAtRight then
        candidateFromResidual D singleValue pairLeft
          (some (enc (W.rightPoint, pairRight)))
      else
        candidateFromResidual D pairLeft singleValue
          (some (enc (W.leftPoint, pairRight)))

/-- Exponent vector of a shifted candidate's displayed leading monomial. -/
noncomputable def candidateExponent (c : ShiftedCandidate) : Exponent20 :=
  Finsupp.equivFunOnFinite.symm (candidateExpAt c)

/-- Canonical exponent attached to a shifted-leading shape. -/
noncomputable def shapeExponent (s : ShiftedLeadShape) : Exponent20 :=
  candidateExponent (shapeCandidate s)

/-- Computable copy of the candidate residual support.  It is definitionally the
same finite set as `candidateResidual`, but avoids carrying the `noncomputable`
marker into finite checks. -/
def candidateResidualC (c : ShiftedCandidate) : Finset (Fin 20) :=
  (Finset.univ.filter fun x : Point => x ∉ c.D.toFinset).image fun x =>
    enc (x, code c.a x)

/-- Computable copy of `candidateExpAt`. -/
def candidateExpAtC (c : ShiftedCandidate) (v : Fin 20) : Nat :=
  (if v ∈ candidateResidualC c then 1 else 0) +
    (if c.shift = some v then 1 else 0)

/-- Computable copy of `candidateLeadCode`. -/
def candidateLeadCodeC (c : ShiftedCandidate) : Nat :=
  ∑ v : Fin 20, candidateExpAtC c v * 3 ^ v.val

/-- Base-3 code of a full exponent vector. -/
noncomputable def exponentCode (e : Exponent20) : Nat :=
  ∑ v : Fin 20, e v * 3 ^ v.val

/-- The computable copies above are definitionally aligned with the original
candidate exponent code. -/
theorem exponentCode_shapeExponent_eq_candidateLeadCodeC
    (s : ShiftedLeadShape) :
    exponentCode (shapeExponent s) = candidateLeadCodeC (shapeCandidate s) := by
  rfl

/-- Numeric code of one concrete encoded variable. -/
def encCodeN (x : Point) (v : Value) : Nat :=
  (enc (x, v)).val

/-- Fast closed-form base-3 code of the canonical shifted-leading shape. -/
def shapeLeadCodeFast : ShiftedLeadShape -> Nat
  | Sum.inl (D, vLeft, vRight) =>
      3 ^ encCodeN D.outLeft vLeft + 3 ^ encCodeN D.outRight vRight
  | Sum.inr (Sum.inl (D, vLeft, vRight, squareRight)) =>
      if squareRight then
        3 ^ encCodeN D.outLeft vLeft + 2 * 3 ^ encCodeN D.outRight vRight
      else
        2 * 3 ^ encCodeN D.outLeft vLeft + 3 ^ encCodeN D.outRight vRight
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit0, v1, v2, v3))) =>
      3 ^ encCodeN 1 v1 + 3 ^ encCodeN 2 v2 + 3 ^ encCodeN 3 v3
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit1, v0, v2, v3))) =>
      3 ^ encCodeN 0 v0 + 3 ^ encCodeN 2 v2 + 3 ^ encCodeN 3 v3
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit2, v0, v1, v3))) =>
      3 ^ encCodeN 0 v0 + 3 ^ encCodeN 1 v1 + 3 ^ encCodeN 3 v3
  | Sum.inr (Sum.inr (Sum.inl (Point3Support.omit3, v0, v1, v2))) =>
      3 ^ encCodeN 0 v0 + 3 ^ encCodeN 1 v1 + 3 ^ encCodeN 2 v2
  | Sum.inr (Sum.inr (Sum.inr (W, pairAtRight, pair, singleValue))) =>
      let l := pair.leftValue
      let r := pair.rightValue
      if pairAtRight then
        3 ^ encCodeN W.leftPoint singleValue +
          3 ^ encCodeN W.rightPoint l + 3 ^ encCodeN W.rightPoint r
      else
        3 ^ encCodeN W.leftPoint l + 3 ^ encCodeN W.leftPoint r +
          3 ^ encCodeN W.rightPoint singleValue

set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 2048 in
/-- The closed-form code matches the finite candidate exponent code. -/
theorem candidateLeadCodeC_shapeCandidate_eq_fast
    (s : ShiftedLeadShape) :
    candidateLeadCodeC (shapeCandidate s) = shapeLeadCodeFast s := by
  revert s
  native_decide

set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 2048 in
/-- The concrete shifted-leading shape code is injective. -/
theorem shapeLeadCodeFast_injective :
    Function.Injective shapeLeadCodeFast := by
  intro x y h
  revert x y
  native_decide

/-- The canonical exponent vector distinguishes all `1550` shifted-leading
shapes. -/
theorem shapeExponent_injective :
    Function.Injective shapeExponent := by
  intro x y h
  apply shapeLeadCodeFast_injective
  rw [← candidateLeadCodeC_shapeCandidate_eq_fast x,
    ← candidateLeadCodeC_shapeCandidate_eq_fast y,
    ← exponentCode_shapeExponent_eq_candidateLeadCodeC x,
    ← exponentCode_shapeExponent_eq_candidateLeadCodeC y,
    h]

/-- In the concrete affine `NW_{4,5,2}` instance, differentiating by any
two-point window leaves exactly the residual graph monomial of the selected
label.

The reason is the degree-`<2` design property: two point evaluations determine
the affine label, so every other summand is killed by at least one derivative
in the window. -/
theorem iterDerivList_nwMvPolynomial_window2_eq_residual_prod
    (D : Window2) (a : Label) :
    SPDP.iterDerivList (nwDerivativeWindowList enc code D.toFinset a)
        (nwMvPolynomial enc code) =
      (nwEncodedGraphOff enc code D.toFinset a).prod
        fun i => (MvPolynomial.X i : MvPolynomial (Fin 20) ℚ) := by
  classical
  rw [nwMvPolynomial, SPDP.iterDerivList_sum]
  change (∑ b : Label,
      SPDP.iterDerivList (nwDerivativeWindowList enc code D.toFinset a)
        (nwMvMonomial enc code b)) =
    (nwEncodedGraphOff enc code D.toFinset a).prod
      fun i => (MvPolynomial.X i : MvPolynomial (Fin 20) ℚ)
  calc
    (∑ b : Label,
        SPDP.iterDerivList (nwDerivativeWindowList enc code D.toFinset a)
          (nwMvMonomial enc code b)) =
        SPDP.iterDerivList (nwDerivativeWindowList enc code D.toFinset a)
          (nwMvMonomial enc code a) := by
      refine @Finset.sum_eq_single Label (MvPolynomial (Fin 20) ℚ) _
        Finset.univ
        (fun b : Label =>
          SPDP.iterDerivList (nwDerivativeWindowList enc code D.toFinset a)
            (nwMvMonomial enc code b))
        a ?_ ?_
      · intro b _ hb
        change SPDP.iterDerivList (nwDerivativeWindowList enc code D.toFinset a)
          (nwMvMonomial enc code b) = 0
        rw [nwMvMonomial_eq_encodedGraph_prod enc code b enc_injective]
        have hDlarge : 1 < D.toFinset.card := by
          rw [window2_toFinset_card]
          omega
        have hdis :
            ∃ x ∈ D.toFinset, code a x ≠ code b x :=
          exists_disagreement_in_large_window code D.toFinset 1
            hDlarge low_agreement hb.symm
        have hmiss :
            ¬ (nwDerivativeWindowList enc code D.toFinset a).toFinset ⊆
              nwEncodedGraphOn enc code Finset.univ b := by
          intro hsub
          rcases hdis with ⟨x, hxD, hneq⟩
          have hagrees :=
            agrees_of_nwDerivativeWindowList_subset_full
              enc code D.toFinset a b enc_injective hsub
          exact hneq (hagrees x hxD)
        exact iterDerivList_prod_X_eq_zero_of_not_subset
          (nwDerivativeWindowList enc code D.toFinset a)
          (nwEncodedGraphOn enc code Finset.univ b)
          hmiss
      · intro ha
        exact (ha (Finset.mem_univ a)).elim
    _ = (nwEncodedGraphOff enc code D.toFinset a).prod
        fun i => (MvPolynomial.X i : MvPolynomial (Fin 20) ℚ) := by
      rw [nwMvMonomial_eq_encodedGraph_prod enc code a enc_injective]
      have hagrees : ∀ x ∈ D.toFinset, code a x = code a x := by
        intro x hx
        rfl
      have hsub :=
        nwDerivativeWindowList_subset_full_of_agrees
          enc code D.toFinset a a hagrees
      have hnodup :=
        nwDerivativeWindowList_nodup enc code D.toFinset a enc_injective
      rw [iterDerivList_prod_X_of_list_subset
        (nwDerivativeWindowList enc code D.toFinset a)
        hnodup
        (nwEncodedGraphOn enc code Finset.univ a)
        hsub]
      rw [nwEncodedGraph_full_sdiff_window_of_agrees
        enc code D.toFinset a a enc_injective hagrees]

/-- Every concrete shifted candidate polynomial is a single shifted residual
monomial. -/
theorem shiftedCandidatePolynomial_eq_shifted_residual_prod
    (c : ShiftedCandidate) :
    shiftedCandidatePolynomial c =
      shiftPolynomial c.shift *
        ((candidateResidual c).prod fun i =>
          (MvPolynomial.X i : MvPolynomial (Fin 20) ℚ)) := by
  rw [shiftedCandidatePolynomial,
    iterDerivList_nwMvPolynomial_window2_eq_residual_prod]
  rfl

/-- The displayed exponent for an unshifted candidate is exactly its residual
squarefree exponent. -/
theorem candidateExponent_none_eq_finSupport (D : Window2) (a : Label) :
    candidateExponent ({ D := D, a := a, shift := none } : ShiftedCandidate) =
      finSupportMonomial
        (candidateResidual ({ D := D, a := a, shift := none } : ShiftedCandidate)) := by
  ext v
  rw [finSupportMonomial, SymmetricPower.tagMonomial_apply]
  simp [candidateExponent, candidateExpAt]

/-- The displayed exponent for a shifted candidate is its residual squarefree
exponent plus the selected shift variable. -/
theorem candidateExponent_some_eq_single_add_finSupport
    (D : Window2) (a : Label) (v : Fin 20) :
    candidateExponent ({ D := D, a := a, shift := some v } : ShiftedCandidate) =
      Finsupp.single v 1 +
        finSupportMonomial
          (candidateResidual ({ D := D, a := a, shift := some v } : ShiftedCandidate)) := by
  ext u
  by_cases huv : u = v
  · subst huv
    simp [candidateExponent, candidateExpAt, finSupportMonomial,
      SymmetricPower.tagMonomial_apply]
    omega
  · have hvu : v ≠ u := fun h => huv h.symm
    simp [candidateExponent, candidateExpAt, finSupportMonomial,
      SymmetricPower.tagMonomial_apply, hvu]

/-- A shifted residual product is the pure monomial with the candidate's
displayed exponent vector. -/
theorem shift_mul_residual_prod_eq_monomial_candidateExponent
    (c : ShiftedCandidate) :
    shiftPolynomial c.shift *
        ((candidateResidual c).prod fun i =>
          (MvPolynomial.X i : MvPolynomial (Fin 20) ℚ)) =
      MvPolynomial.monomial (candidateExponent c) (1 : ℚ) := by
  cases c with
  | mk D a shift =>
    cases shift with
    | none =>
        rw [prod_X_eq_monomial_finSupport]
        simp [shiftPolynomial]
        exact (candidateExponent_none_eq_finSupport D a).symm
    | some sh =>
        rw [prod_X_eq_monomial_finSupport]
        rw [shiftPolynomial, MvPolynomial.X, MvPolynomial.monomial_mul]
        simp only [one_mul]
        rw [candidateExponent_some_eq_single_add_finSupport D a sh]

/-- Every concrete shifted candidate polynomial is a pure monomial with its
displayed exponent vector. -/
theorem shiftedCandidatePolynomial_eq_monomial_candidateExponent
    (c : ShiftedCandidate) :
    shiftedCandidatePolynomial c =
      MvPolynomial.monomial (candidateExponent c) (1 : ℚ) := by
  rw [shiftedCandidatePolynomial_eq_shifted_residual_prod]
  exact shift_mul_residual_prod_eq_monomial_candidateExponent c

/-- Coefficient projection to the canonical `1550` shifted-leading shape
coordinates. -/
noncomputable def shiftedCoeffProjectionByShape :
    MvPolynomial (Fin 20) ℚ →ₗ[ℚ] (ShiftedLeadShape -> ℚ) where
  toFun p := fun s => MvPolynomial.coeff (shapeExponent s) p
  map_add' p q := by
    ext s
    simp [MvPolynomial.coeff_add]
  map_smul' c p := by
    ext s
    simp [MvPolynomial.coeff_smul]

/-- The canonical finite row family for the strong concrete shifted count. -/
noncomputable def shiftedShapeRows (s : ShiftedLeadShape) :
    ShiftedLeadShape -> ℚ :=
  shiftedCoeffProjectionByShape (shiftedCandidatePolynomial (shapeCandidate s))

/-- The canonical shifted-shape row family is Kronecker on the canonical
shape exponents. -/
theorem shiftedShapeRows_eq_indicator (j i : ShiftedLeadShape) :
    shiftedShapeRows j i =
      if shapeExponent j = shapeExponent i then (1 : ℚ) else 0 := by
  unfold shiftedShapeRows shiftedCoeffProjectionByShape
  change MvPolynomial.coeff (shapeExponent i)
      (shiftedCandidatePolynomial (shapeCandidate j)) =
    if shapeExponent j = shapeExponent i then (1 : ℚ) else 0
  rw [shiftedCandidatePolynomial_eq_monomial_candidateExponent]
  rw [MvPolynomial.coeff_monomial]
  simp [shapeExponent]

/-- Every canonical shifted row has a nonzero private diagonal coefficient. -/
theorem shiftedShapeRows_self_ne_zero :
    ∀ i, shiftedShapeRows i i ≠ 0 := by
  intro i
  rw [shiftedShapeRows_eq_indicator]
  simp

/-- Distinct canonical shifted rows vanish at each other's pivot coordinates. -/
theorem shiftedShapeRows_offdiag :
    ∀ i j, i ≠ j -> shiftedShapeRows j i = 0 := by
  intro i j hij
  rw [shiftedShapeRows_eq_indicator]
  have hne : shapeExponent j ≠ shapeExponent i := by
    intro h
    exact hij ((shapeExponent_injective h).symm)
  simp [hne]

/-- The canonical finite shape rows are projections of actual elements of the
concrete SPDP subspace. -/
theorem shiftedShapeRows_finrank_le_actual_spdpRank_canonical :
    (Set.range shiftedShapeRows).finrank ℚ <=
      SPDP.spdpRank 2 1 (nwMvPolynomial enc code) := by
  classical
  let W : Submodule ℚ (ShiftedLeadShape -> ℚ) :=
    Submodule.map shiftedCoeffProjectionByShape
      (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code))
  have hspan :
      Submodule.span ℚ (Set.range shiftedShapeRows) ≤ W := by
    apply Submodule.span_le.mpr
    intro row hrow
    rcases hrow with ⟨s, rfl⟩
    refine ⟨shiftedCandidatePolynomial (shapeCandidate s),
      shiftedCandidatePolynomial_mem_spdpSubspace (shapeCandidate s), ?_⟩
    rfl
  have hmono :
      (Set.range shiftedShapeRows).finrank ℚ <= Module.finrank ℚ W := by
    simpa using Submodule.finrank_mono hspan
  have hmap :
      Module.finrank ℚ W <=
        Module.finrank ℚ (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)) := by
    simpa [W] using
      (Submodule.finrank_map_le shiftedCoeffProjectionByShape
        (SPDP.spdpSubspace 2 1 (nwMvPolynomial enc code)))
  exact le_trans hmono hmap

/-- Private-pivot closure for the canonical finite shifted-shape rows.

This is now the exact remaining finite theorem needed for the unconditional
`1550` bound: show the canonical row has coefficient `1` at its own shape
coordinate and `0` at every other shape coordinate. -/
theorem spdpRank_nw452_ge_1550_of_shapePrivatePivots
    (hpivot_ne_zero : ∀ i, shiftedShapeRows i i ≠ 0)
    (hpivot_offdiag : ∀ i j, i ≠ j -> shiftedShapeRows j i = 0) :
    1550 <= SPDP.spdpRank 2 1 (nwMvPolynomial enc code) := by
  have hcard :
      Fintype.card ShiftedLeadShape <=
        SPDP.spdpRank 2 1 (nwMvPolynomial enc code) :=
    leadingSupport_card_le_spdpRank
      shiftedShapeRows
      (fun i : ShiftedLeadShape => i)
      hpivot_ne_zero
      hpivot_offdiag
      shiftedShapeRows_finrank_le_actual_spdpRank_canonical
  simpa [shiftedLeadShape_card] using hcard

/-- Unconditional strong shifted-leading lower bound for the concrete
`NW_{4,5,2}` polynomial at `(κ,ℓ)=(2,1)`. -/
theorem spdpRank_nw452_ge_1550 :
    1550 <= SPDP.spdpRank 2 1 (nwMvPolynomial enc code) :=
  spdpRank_nw452_ge_1550_of_shapePrivatePivots
    shiftedShapeRows_self_ne_zero
    shiftedShapeRows_offdiag

/-! ## Axiom audit -/

#print axioms shiftedCandidatePolynomial_mem_spdpSubspace
#print axioms shiftedShapeRows_finrank_le_actual_spdpRank
#print axioms shiftedShapeRowsByCode_finrank_le_actual_spdpRank
#print axioms spdpRank_nw452_ge_1550_of_shiftedShapeSelectionByCode
#print axioms shiftedShapeRows_finrank_le_actual_spdpRank_canonical
#print axioms spdpRank_nw452_ge_1550_of_shapePrivatePivots
#print axioms shapeExponent_injective
#print axioms shiftedShapeRows_self_ne_zero
#print axioms shiftedShapeRows_offdiag
#print axioms spdpRank_nw452_ge_1550

end NW452

end PallLean.Paper93.DeepMath.AlgebraicSPDP
