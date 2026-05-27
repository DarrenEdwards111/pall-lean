import PallLean.Paper93.DeepMath.AlgebraicSPDP.ArithmeticCircuitSPDPPivot
import PallLean.SPDPDefs
import Mathlib.Data.Finset.Image

/-!
# NW Support Independence

This file proves the first NW-specific combinatorial layer behind
`NWSPDPIndependenceCertificate`.

We model a Nisan-Wigderson design monomial by the graph of a codeword

`x ↦ (x, code a x)`.

Low agreement of distinct codewords gives the two facts needed by the
leading-support engine:

1. a derivative window larger than the agreement bound contains a point where
   two distinct codewords differ, so differentiating by the graph of one
   codeword kills the other monomial;
2. an outside window larger than the agreement bound gives injective residual
   graph supports, so the post-derivative leading monomial is private.

The remaining polynomial-calculus step is to identify these graph-support
rows with actual shifted partial derivative rows of the NW polynomial.  Once
that identification supplies `span_rank_le_spdp`, the certificate is
constructed here.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

open scoped BigOperators

section GraphDesign

variable {Label Point Value : Type*}
variable [Fintype Point] [DecidableEq Point] [DecidableEq Value]

/-- Points where two NW codewords agree. -/
def nwAgreementSet (code : Label -> Point -> Value) (a b : Label) :
    Finset Point :=
  Finset.univ.filter fun x => code a x = code b x

/-- The graph of a codeword restricted to a finite point window. -/
def nwGraphOn (code : Label -> Point -> Value) (D : Finset Point)
    (a : Label) : Finset (Point × Value) :=
  D.image fun x => (x, code a x)

/-- The residual graph after differentiating/removing the point window `D`. -/
def nwGraphOff (code : Label -> Point -> Value) (D : Finset Point)
    (a : Label) : Finset (Point × Value) :=
  (Finset.univ.filter fun x => x ∉ D).image fun x => (x, code a x)

omit [DecidableEq Point] in
/-- If two codewords agree on all of a window, that window is contained in the
agreement set. -/
theorem nw_window_subset_agreement_of_agrees
    (code : Label -> Point -> Value) (D : Finset Point) (a b : Label)
    (hagrees : ∀ x ∈ D, code a x = code b x) :
    D ⊆ nwAgreementSet code a b := by
  intro x hx
  simp [nwAgreementSet, hagrees x hx]

omit [DecidableEq Point] in
/-- Low agreement forces a disagreement inside every larger derivative
window.  This is the NW reason that differentiating by the graph of one
codeword kills every other codeword monomial. -/
theorem exists_disagreement_in_large_window
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound : Nat)
    (hD : overlapBound < D.card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    {a b : Label} (hne : a ≠ b) :
    ∃ x ∈ D, code a x ≠ code b x := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsubset : D ⊆ nwAgreementSet code a b :=
    nw_window_subset_agreement_of_agrees code D a b hnone
  have hcard : D.card <= (nwAgreementSet code a b).card :=
    Finset.card_le_card hsubset
  have : D.card <= overlapBound := le_trans hcard (hlow a b hne)
  omega

/-- If two residual graph supports are equal, then the two codewords agree at
every point outside the derivative window. -/
theorem agrees_off_window_of_nwGraphOff_eq
    (code : Label -> Point -> Value) (D : Finset Point)
    {a b : Label}
    (hgraph : nwGraphOff code D a = nwGraphOff code D b) :
    ∀ x, x ∉ D -> code a x = code b x := by
  classical
  intro x hxD
  have hxA : (x, code a x) ∈ nwGraphOff code D a := by
    simp [nwGraphOff, hxD]
  have hxB : (x, code a x) ∈ nwGraphOff code D b := by
    simpa [hgraph] using hxA
  have hxB' : x ∉ D ∧ code b x = code a x := by
    simpa [nwGraphOff] using hxB
  exact hxB'.2.symm

/-- Low agreement and a large outside window make the residual graph supports
injective.  These residual supports are the private leading monomials in the
NW shifted-partial argument. -/
theorem nwGraphOff_injective_of_lowAgreement
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound : Nat)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound) :
    Function.Injective (nwGraphOff code D) := by
  classical
  intro a b hgraph
  by_contra hne
  have hagreeOutside := agrees_off_window_of_nwGraphOff_eq code D hgraph
  have hsubset :
      (Finset.univ.filter fun x : Point => x ∉ D) ⊆ nwAgreementSet code a b := by
    intro x hx
    have hxD : x ∉ D := (Finset.mem_filter.mp hx).2
    simp [nwAgreementSet, hagreeOutside x hxD]
  have hcard :
      (Finset.univ.filter fun x : Point => x ∉ D).card <=
        (nwAgreementSet code a b).card :=
    Finset.card_le_card hsubset
  have : (Finset.univ.filter fun x : Point => x ∉ D).card <= overlapBound :=
    le_trans hcard (hlow a b hne)
  exact (not_lt_of_ge this) hOutside

/-- Indicator coefficient rows for private residual graph supports.

This is the coefficient-row model after the NW derivative-window argument has
shown that each selected derivative row has exactly one residual graph pivot.
-/
def nwResidualIndicatorRows
    [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point) :
    Label -> Finset (Point × Value) -> ℚ :=
  fun a m => if m = nwGraphOff code D a then 1 else 0

/-! ## Polynomial-calculus row model

For the NW polynomial

`NW_code = sum_a prod_x X_(x, code a x)`,

differentiating by the graph variables `{(x, code a x) : x in D}` keeps the
monomial indexed by `b` exactly when `a` and `b` agree on every point of `D`.
The surviving monomial support is then the residual graph of `b` outside `D`.

The following definition is that coefficient row, written directly at the
finite-support level.  It is the unshifted SPDP row; in the full SPDP space it
appears with shift monomial `1`.
-/

/-- The coefficient row obtained by differentiating the NW polynomial by the
graph of label `a` over the point window `D`. -/
noncomputable def nwDerivativeWindowRows
    [Fintype Label] [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point) :
    Label -> Finset (Point × Value) -> ℚ :=
  fun a m =>
    if ∃ b : Label, (∀ x ∈ D, code a x = code b x) ∧
        m = nwGraphOff code D b then 1 else 0

/-- Under low agreement and a large derivative window, the actual
NW derivative-window row is exactly the residual private-pivot indicator row.

This is the polynomial-calculus/SPDP bridge at the support-row level.  The
only surviving monomial after differentiating by label `a`'s graph over `D`
is label `a`'s own residual graph: every other label disagrees somewhere in
`D` and is killed by the derivative. -/
theorem nwDerivativeWindowRows_eq_residualIndicator_of_lowAgreement
    [Fintype Label] [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound : Nat)
    (hD : overlapBound < D.card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound) :
    nwDerivativeWindowRows code D = nwResidualIndicatorRows code D := by
  classical
  funext a m
  by_cases hm : m = nwGraphOff code D a
  · have hsurvive :
        ∃ b : Label, (∀ x ∈ D, code a x = code b x) ∧
          nwGraphOff code D a = nwGraphOff code D b := by
      exact ⟨a, by intro x hx; rfl, rfl⟩
    simp [nwDerivativeWindowRows, nwResidualIndicatorRows, hm, hsurvive]
  · have hnoSurvive :
        ¬ ∃ b : Label, (∀ x ∈ D, code a x = code b x) ∧
          m = nwGraphOff code D b := by
      rintro ⟨b, hagree, hm_b⟩
      by_cases hba : b = a
      · subst hba
        exact hm hm_b
      · have hdis :
            ∃ x ∈ D, code a x ≠ code b x :=
          exists_disagreement_in_large_window code D overlapBound hD hlow
            (fun hab => hba hab.symm)
        rcases hdis with ⟨x, hxD, hneq⟩
        exact hneq (hagree x hxD)
    simp [nwDerivativeWindowRows, nwResidualIndicatorRows, hm, hnoSurvive]

/-- The residual row has coefficient `1` at its own pivot. -/
theorem nwResidualIndicatorRows_self
    [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point) :
    ∀ a, nwResidualIndicatorRows code D a (nwGraphOff code D a) ≠ 0 := by
  intro a
  simp [nwResidualIndicatorRows]

/-- Injective residual pivots vanish off the diagonal. -/
theorem nwResidualIndicatorRows_offdiag
    [Fintype Value]
    (code : Label -> Point -> Value) (D : Finset Point)
    (hinj : Function.Injective (nwGraphOff code D)) :
    ∀ a b, a ≠ b ->
      nwResidualIndicatorRows code D b (nwGraphOff code D a) = 0 := by
  intro a b hne
  have hpivot_ne : nwGraphOff code D a ≠ nwGraphOff code D b := by
    intro h
    exact hne (hinj h)
  simp [nwResidualIndicatorRows, hpivot_ne]

/-- Low agreement constructs the leading-support hypotheses needed by the
generic algebraic SPDP pivot engine. -/
def NWSPDPIndependenceCertificate.ofLowAgreementResidualPivots
    [Fintype Label] [Fintype Value]
    {numVars degree kappa ell : Nat}
    (support : NWLeadingSupportData)
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound spdpRank : Nat)
    (support_lower_le_labels : support.lower <= Fintype.card Label)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    (span_rank_le_spdp :
      (Set.range (nwResidualIndicatorRows code D)).finrank ℚ <= spdpRank) :
    NWSPDPIndependenceCertificate numVars degree kappa ell :=
  let hinj := nwGraphOff_injective_of_lowAgreement code D overlapBound hOutside hlow
  NWSPDPIndependenceCertificate.ofLeadingSupport
    support
    (nwResidualIndicatorRows code D)
    (nwGraphOff code D)
    (nwResidualIndicatorRows_self code D)
    (nwResidualIndicatorRows_offdiag code D hinj)
    spdpRank
    support_lower_le_labels
    span_rank_le_spdp

/-- The same certificate, but with the SPDP row-containment hypothesis stated
for the actual NW derivative-window rows rather than for the normalized
residual indicator rows.

The equality theorem
`nwDerivativeWindowRows_eq_residualIndicator_of_lowAgreement` transports the
containment/rank hypothesis across the row identification. -/
def NWSPDPIndependenceCertificate.ofLowAgreementDerivativeRows
    [Fintype Label] [Fintype Value]
    {numVars degree kappa ell : Nat}
    (support : NWLeadingSupportData)
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound spdpRank : Nat)
    (support_lower_le_labels : support.lower <= Fintype.card Label)
    (hD : overlapBound < D.card)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    (span_rank_le_spdp :
      (Set.range (nwDerivativeWindowRows code D)).finrank ℚ <= spdpRank) :
    NWSPDPIndependenceCertificate numVars degree kappa ell := by
  classical
  have hrows :
      nwDerivativeWindowRows code D = nwResidualIndicatorRows code D :=
    nwDerivativeWindowRows_eq_residualIndicator_of_lowAgreement
      code D overlapBound hD hlow
  refine NWSPDPIndependenceCertificate.ofLowAgreementResidualPivots
    support code D overlapBound spdpRank support_lower_le_labels
    hOutside hlow ?_
  simpa [← hrows] using span_rank_le_spdp

/-! ## Bridge to the concrete SPDP subspace

The previous theorem is deliberately finite-support algebra.  The next layer
connects that algebra to the project's actual `MvPolynomial`/`SPDP.spdpRank`
object without introducing a free numerical rank.

The only remaining mathematical payload is `rows_mem_actual_spdp_image`: each
finite-support derivative-window coefficient row must be realized as the image
of an actual element of `SPDP.spdpSubspace kappa ell p` under a concrete
coefficient-projection linear map.  Once that realization is supplied, ordinary
linear algebra proves the finite-support row rank is bounded by the actual
SPDP rank of `p`.
-/

/-- Concrete containment bridge for NW derivative-window rows.

`coeffProjection` is the coefficient-extraction map from the ambient
`MvPolynomial` space into the finite-support row model.  The fields require
every selected NW derivative-window row to be realized by an actual SPDP
generator/span element of the concrete polynomial `p`.
-/
structure NWDerivativeRowsActualSPDPBridge
    [Fintype Label] [Fintype Value]
    {numVars kappa ell : Nat}
    (code : Label -> Point -> Value) (D : Finset Point)
    (p : MvPolynomial (Fin numVars) ℚ) : Type _ where
  coeffProjection :
    MvPolynomial (Fin numVars) ℚ →ₗ[ℚ] (Finset (Point × Value) -> ℚ)
  rows_mem_actual_spdp_image :
    ∀ a : Label, nwDerivativeWindowRows code D a ∈
      Submodule.map coeffProjection (SPDP.spdpSubspace kappa ell p)

/-- If the finite-support derivative rows are coefficient projections of the
actual SPDP subspace, their row rank is bounded by the concrete SPDP rank.

This is the real ambient bridge shape: no free `spdpRank : Nat` remains. -/
theorem nwDerivativeWindowRows_finrank_le_actual_spdpRank
    [Fintype Label] [Fintype Value]
    {numVars kappa ell : Nat}
    (code : Label -> Point -> Value) (D : Finset Point)
    (p : MvPolynomial (Fin numVars) ℚ)
    (bridge : NWDerivativeRowsActualSPDPBridge code D p
      (kappa := kappa) (ell := ell)) :
    (Set.range (nwDerivativeWindowRows code D)).finrank ℚ <=
      SPDP.spdpRank kappa ell p := by
  classical
  let W : Submodule ℚ (Finset (Point × Value) -> ℚ) :=
    Submodule.map bridge.coeffProjection (SPDP.spdpSubspace kappa ell p)
  have hspan :
      Submodule.span ℚ (Set.range (nwDerivativeWindowRows code D)) ≤ W := by
    apply Submodule.span_le.mpr
    intro row hrow
    rcases hrow with ⟨a, rfl⟩
    exact bridge.rows_mem_actual_spdp_image a
  have hmono :
      (Set.range (nwDerivativeWindowRows code D)).finrank ℚ <=
        Module.finrank ℚ W := by
    simpa using Submodule.finrank_mono hspan
  have hmap :
      Module.finrank ℚ W <=
        Module.finrank ℚ (SPDP.spdpSubspace kappa ell p) := by
    simpa [W] using
      (Submodule.finrank_map_le bridge.coeffProjection
        (SPDP.spdpSubspace kappa ell p))
  exact le_trans hmono hmap

/-! ### Concrete coefficient projection

The next definitions build the actual coefficient-extraction map used by the
bridge.  A support `m : Finset (Point × Value)` is read as the squarefree
monomial with exponent `1` on the encoded variables in `m`.
-/

/-- Squarefree exponent vector associated to a finite graph-support set. -/
noncomputable def squarefreeSupportExponent
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (m : Finset (Point × Value)) : Fin numVars →₀ Nat :=
  m.sum fun z => Finsupp.single (enc z) 1

/-- Coefficient projection from the concrete ambient `MvPolynomial` space to
the finite-support row model used by the NW combinatorics. -/
noncomputable def nwCoefficientProjection
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars) :
    MvPolynomial (Fin numVars) ℚ →ₗ[ℚ] (Finset (Point × Value) -> ℚ) where
  toFun p := fun m => MvPolynomial.coeff (squarefreeSupportExponent enc m) p
  map_add' p q := by
    ext m
    simp [MvPolynomial.coeff_add]
  map_smul' c p := by
    ext m
    simp [MvPolynomial.coeff_smul]

/-- The derivative list corresponding to differentiating by one label's graph
over the point window `D`. -/
noncomputable def nwDerivativeWindowList
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a : Label) :
    List (Fin numVars) :=
  D.toList.map fun x => enc (x, code a x)

omit [Fintype Point] [DecidableEq Point] [DecidableEq Value] in
/-- The concrete derivative list has length equal to the point-window size. -/
theorem nwDerivativeWindowList_length
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) (a : Label) :
    (nwDerivativeWindowList enc code D a).length = D.card := by
  simp [nwDerivativeWindowList]

/-! ### Actual NW polynomial target

The bridge above still accepted an arbitrary polynomial `p`.  The definitions
below pin the target down to the concrete NW polynomial encoded by `code`.
The remaining row-realization theorem is now a single coefficient identity for
this polynomial, rather than a generic bridge against a free ambient object.
-/

/-- The monomial for one NW codeword, encoded in the ambient variable set. -/
noncomputable def nwMvMonomial
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (a : Label) :
    MvPolynomial (Fin numVars) ℚ :=
  (Finset.univ : Finset Point).prod
    fun x => MvPolynomial.X (enc (x, code a x))

/-- The concrete NW polynomial `sum_a prod_x X_(x, code a x)`. -/
noncomputable def nwMvPolynomial
    [Fintype Label]
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) :
    MvPolynomial (Fin numVars) ℚ :=
  Finset.univ.sum fun a : Label => nwMvMonomial enc code a

/-- The concrete coefficient identity left by the actual-SPDP bridge.

The injectivity condition is essential: without it, distinct graph variables
`(Point × Value)` can collapse to the same ambient variable in `Fin numVars`,
so squarefree coefficient projection is no longer faithful to graph supports.

For every label `a`, differentiating the concrete NW polynomial by the encoded
window graph of `a`, then projecting squarefree residual coefficients, must
produce exactly the finite-support derivative-window row used in the
combinatorial NW argument.
-/
noncomputable def NWProjectedDerivativeRowIdentity
    [Fintype Label] [Fintype Value]
    {numVars : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point) : Prop :=
  Function.Injective enc ∧
    ∀ a : Label,
      nwCoefficientProjection enc
          (SPDP.iterDerivList (nwDerivativeWindowList enc code D a)
            (nwMvPolynomial enc code)) =
        nwDerivativeWindowRows code D a

/-- The injective-encoding side of `NWProjectedDerivativeRowIdentity`. -/
theorem NWProjectedDerivativeRowIdentity.injective
    [Fintype Label] [Fintype Value]
    {numVars : Nat}
    {enc : Point × Value -> Fin numVars}
    {code : Label -> Point -> Value} {D : Finset Point}
    (projected_rows : NWProjectedDerivativeRowIdentity enc code D) :
    Function.Injective enc :=
  projected_rows.1

/-- The concrete projected-row equality side of
`NWProjectedDerivativeRowIdentity`. -/
theorem NWProjectedDerivativeRowIdentity.row_eq
    [Fintype Label] [Fintype Value]
    {numVars : Nat}
    {enc : Point × Value -> Fin numVars}
    {code : Label -> Point -> Value} {D : Finset Point}
    (projected_rows : NWProjectedDerivativeRowIdentity enc code D) :
    ∀ a : Label,
      nwCoefficientProjection enc
          (SPDP.iterDerivList (nwDerivativeWindowList enc code D a)
            (nwMvPolynomial enc code)) =
        nwDerivativeWindowRows code D a :=
  projected_rows.2

/-- Build the actual-SPDP bridge once the concrete coefficient identity is
proved.

The hypothesis `projected_derivative_row` is the remaining polynomial-calculus
payload: after differentiating the actual NW `MvPolynomial` by label `a` over
`D`, coefficient extraction must give exactly the finite-support row
`nwDerivativeWindowRows code D a`.

Everything else in this constructor is now proved: the derivative is an
element of the concrete `SPDP.spdpSubspace`, and coefficient projection cannot
increase finrank. -/
noncomputable def NWDerivativeRowsActualSPDPBridge.ofProjectedDerivativeRows
    [Fintype Label] [Fintype Value]
    {numVars kappa ell : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point)
    (p : MvPolynomial (Fin numVars) ℚ)
    (hDcard : D.card = kappa)
    (projected_derivative_row :
      ∀ a : Label,
        nwCoefficientProjection enc
            (SPDP.iterDerivList (nwDerivativeWindowList enc code D a) p) =
          nwDerivativeWindowRows code D a) :
    NWDerivativeRowsActualSPDPBridge code D p (kappa := kappa) (ell := ell) where
  coeffProjection := nwCoefficientProjection enc
  rows_mem_actual_spdp_image := by
    intro a
    refine ⟨SPDP.iterDerivList (nwDerivativeWindowList enc code D a) p, ?_, ?_⟩
    · apply Submodule.subset_span
      refine ⟨nwDerivativeWindowList enc code D a, 1, ?_, ?_, ?_⟩
      · rw [nwDerivativeWindowList_length, hDcard]
      · simp [MvPolynomial.totalDegree_one]
      · ring
    · exact projected_derivative_row a

/-- Specialize the actual-SPDP bridge to the concrete NW polynomial.

This removes the arbitrary ambient polynomial from the interface.  The only
remaining payload is the named coefficient identity
`NWProjectedDerivativeRowIdentity`. -/
noncomputable def NWDerivativeRowsActualSPDPBridge.ofNWProjectedDerivativeRowIdentity
    [Fintype Label] [Fintype Value]
    {numVars kappa ell : Nat}
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point)
    (hDcard : D.card = kappa)
    (projected_rows : NWProjectedDerivativeRowIdentity enc code D) :
    NWDerivativeRowsActualSPDPBridge code D (nwMvPolynomial enc code)
      (kappa := kappa) (ell := ell) :=
  NWDerivativeRowsActualSPDPBridge.ofProjectedDerivativeRows
    enc code D (nwMvPolynomial enc code) hDcard projected_rows.row_eq

/-- Fully explicit low-agreement NW certificate against the concrete
`SPDP.spdpRank` of an ambient `MvPolynomial`.

The side conditions are exactly the ones exposed by the diagnostic script:

* `hD`: the differentiated window is larger than the agreement bound, so all
  nonmatching monomials are killed;
* `hOutside`: the residual outside window is larger than the agreement bound,
  so residual supports are injective.

The remaining payload is not a number: it is the concrete row-realization
bridge into `SPDP.spdpSubspace`. -/
noncomputable def NWSPDPIndependenceCertificate.ofLowAgreementActualSPDP
    [Fintype Label] [Fintype Value]
    {numVars degree kappa ell : Nat}
    (support : NWLeadingSupportData)
    (code : Label -> Point -> Value) (D : Finset Point)
    (p : MvPolynomial (Fin numVars) ℚ)
    (overlapBound : Nat)
    (support_lower_le_labels : support.lower <= Fintype.card Label)
    (hD : overlapBound < D.card)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    (bridge : NWDerivativeRowsActualSPDPBridge code D p
      (kappa := kappa) (ell := ell)) :
    NWSPDPIndependenceCertificate numVars degree kappa ell :=
  NWSPDPIndependenceCertificate.ofLowAgreementDerivativeRows
    support code D overlapBound (SPDP.spdpRank kappa ell p)
    support_lower_le_labels hD hOutside hlow
    (nwDerivativeWindowRows_finrank_le_actual_spdpRank code D p bridge)

/-- Fully concrete NW certificate against the actual SPDP rank of
`nwMvPolynomial enc code`.

This is the modest unshifted/window-row closure shape.  It is no longer about a
free polynomial or a free numerical rank; the only unproved mathematical input
is the coefficient identity proving that actual derivatives of the concrete NW
polynomial project to the finite-support rows.
-/
noncomputable def NWSPDPIndependenceCertificate.ofLowAgreementNWPolynomial
    [Fintype Label] [Fintype Value]
    {numVars degree kappa ell : Nat}
    (support : NWLeadingSupportData)
    (enc : Point × Value -> Fin numVars)
    (code : Label -> Point -> Value) (D : Finset Point)
    (overlapBound : Nat)
    (support_lower_le_labels : support.lower <= Fintype.card Label)
    (hD : overlapBound < D.card)
    (hOutside :
      overlapBound < (Finset.univ.filter fun x : Point => x ∉ D).card)
    (hlow : ∀ a b : Label, a ≠ b ->
      (nwAgreementSet code a b).card <= overlapBound)
    (hDcard : D.card = kappa)
    (projected_rows : NWProjectedDerivativeRowIdentity enc code D) :
    NWSPDPIndependenceCertificate numVars degree kappa ell :=
  NWSPDPIndependenceCertificate.ofLowAgreementActualSPDP
    support code D (nwMvPolynomial enc code) overlapBound
    support_lower_le_labels hD hOutside hlow
    (NWDerivativeRowsActualSPDPBridge.ofNWProjectedDerivativeRowIdentity
      enc code D hDcard projected_rows)

/-! ## Axiom audit -/

#print axioms exists_disagreement_in_large_window
#print axioms nwDerivativeWindowRows_eq_residualIndicator_of_lowAgreement
#print axioms nwGraphOff_injective_of_lowAgreement
#print axioms nwResidualIndicatorRows_offdiag
#print axioms NWSPDPIndependenceCertificate.ofLowAgreementResidualPivots
#print axioms NWSPDPIndependenceCertificate.ofLowAgreementDerivativeRows
#print axioms nwDerivativeWindowRows_finrank_le_actual_spdpRank
#print axioms nwCoefficientProjection
#print axioms NWDerivativeRowsActualSPDPBridge.ofProjectedDerivativeRows
#print axioms NWDerivativeRowsActualSPDPBridge.ofNWProjectedDerivativeRowIdentity
#print axioms NWSPDPIndependenceCertificate.ofLowAgreementActualSPDP
#print axioms NWSPDPIndependenceCertificate.ofLowAgreementNWPolynomial

end GraphDesign

end PallLean.Paper93.DeepMath.AlgebraicSPDP
