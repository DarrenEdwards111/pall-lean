import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Algebraic SPDP Pivot

This file records the mathematically live use of the SPDP/God-Move
instrument: algebraic circuit lower bounds, not Boolean `P` versus `NP`.

The Boolean route failed because it tried to transport a high SPDP/rank
minor into the live state of an arbitrary SAT decider.  In algebraic
complexity the object is a fixed polynomial family, so there is no
zero-rank decider presentation that can hide the polynomial.

The active target is the standard shifted-partial-derivative loop:

* prove a lower bound on `Gamma_{kappa,ell}(F)` for an explicit hard
  polynomial family such as a Nisan-Wigderson design polynomial;
* use the standard upper bound for homogeneous depth-3 circuits
  `Sigma Pi Sigma_s`:

    `Gamma_{kappa,ell}(C) <= s * choose d kappa * M(N,ell)`,

  where `M(N,ell)` is the number of monomials of degree at most `ell`
  in `N` variables;
* conclude a product-gate lower bound for depth-3 circuits.

The hard theorem is isolated as a support/leading-monomial independence
certificate.  This file does not assert that certificate; it proves the
conversion from such a certificate to a circuit lower bound.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

/-- Number of monomials of total degree at most `ell` in `numVars` variables.

By the stars-and-bars identity this is `choose (numVars + ell) ell`. -/
def monomialCountLE (numVars ell : Nat) : Nat :=
  Nat.choose (numVars + ell) ell

/-- The depth-3 shifted-partial-derivative denominator.

For a homogeneous depth-3 circuit

`f = sum_{i=1}^s prod_{j=1}^d l_{ij}`,

the usual SPDP upper-bound proof gives

`Gamma_{kappa,ell}(f) <= s * choose d kappa * M(numVars,ell)`.
-/
def depth3SpdpDenominator (numVars degree kappa ell : Nat) : Nat :=
  Nat.choose degree kappa * monomialCountLE numVars ell

/-- Abstract rank comparison data at one SPDP scale.

`spdpRank` is the actual shifted-partial-derivative rank of the fixed
polynomial object.  `analyticLower` is a proved lower bound on that rank,
typically coming from a support/leading-monomial independence theorem.

`productGates` is the `s` in a depth-3 `Sigma Pi Sigma_s` representation.
The upper-bound field is the standard depth-3 SPDP upper bound.
-/
structure Depth3SPDPComparison (numVars degree kappa ell : Nat) where
  productGates : Nat
  spdpRank : Nat
  analyticLower : Nat
  lower_le_rank : analyticLower <= spdpRank
  rank_le_depth3 :
    spdpRank <= productGates * depth3SpdpDenominator numVars degree kappa ell

/-- The complete depth-3 conversion theorem.

Once an explicit polynomial has SPDP rank at least `analyticLower`, any
homogeneous depth-3 circuit for it must have enough product gates to carry
that rank.  The output is kept in multiplicative form:

`analyticLower <= s * choose d kappa * M(N,ell)`.

Equivalently, if the denominator is positive, this says
`s >= ceil(analyticLower / denominator)`.
-/
theorem depth3_product_gate_lower_bound
    {numVars degree kappa ell : Nat}
    (C : Depth3SPDPComparison numVars degree kappa ell) :
    C.analyticLower <=
      C.productGates * depth3SpdpDenominator numVars degree kappa ell :=
  le_trans C.lower_le_rank C.rank_le_depth3

/-- A direct exclusion form of `depth3_product_gate_lower_bound`.

If a proposed depth-3 product-gate count has SPDP capacity strictly below
the analytic lower bound, then no comparison certificate for that circuit
can exist. -/
theorem no_depth3_comparison_of_capacity_lt_lower
    {numVars degree kappa ell : Nat}
    (C : Depth3SPDPComparison numVars degree kappa ell)
    (hgap :
      C.productGates * depth3SpdpDenominator numVars degree kappa ell <
        C.analyticLower) :
    False :=
  (not_lt_of_ge (depth3_product_gate_lower_bound C)) hgap

/-- Support-count data for the Nisan-Wigderson lower-bound mechanism.

The standard proof tries to construct many shifted partial derivatives with
distinct leading/support witnesses.  `basePartialRows * legalShiftRows` is
the naive row count; `collisionDefect` is the number of rows lost to support
collisions.  A real NW design theorem proves this defect is small by using
the low-intersection property of the design.
-/
structure NWLeadingSupportData where
  basePartialRows : Nat
  legalShiftRows : Nat
  collisionDefect : Nat

/-- The lower-bound expression supplied by a support-independence proof. -/
def NWLeadingSupportData.lower (D : NWLeadingSupportData) : Nat :=
  D.basePartialRows * D.legalShiftRows - D.collisionDefect

/-- The analytic theorem target for the NW polynomial.

This is the honest hard mathematical object: prove that the shifted partials
selected by the NW design contain at least `support.lower` independent rows.
In concrete proofs this is discharged by a leading-monomial/support
uniqueness argument using the design intersection bound.
-/
structure NWSPDPIndependenceCertificate
    (numVars degree kappa ell : Nat) where
  support : NWLeadingSupportData
  spdpRank : Nat
  support_lower_le_rank : support.lower <= spdpRank

/-! ## Leading-support independence engine

The standard NW lower-bound proof does not try to compute the full SPDP
rank directly.  It selects a large family of shifted partial derivatives and
assigns to each selected row a private leading/support monomial.  If that
monomial has nonzero coefficient in its own row and zero coefficient in all
other selected rows, the selected rows are linearly independent.

The next theorem proves exactly that pivot-coordinate argument.  This is the
load-bearing algebraic content that the NW design/intersection lemma must
feed: construct enough rows with private pivots.
-/

/-- A family of coefficient rows with private pivot monomials is linearly
independent.

`rows i a` is the coefficient of monomial `a` in selected row `i`.  The pivot
conditions say that row `i` has nonzero coefficient at `pivot i`, while every
other row vanishes at that coordinate. -/
theorem leadingSupport_linearIndependent
    {ι μ : Type*} [Fintype ι] [Fintype μ]
    (rows : ι -> μ -> ℚ) (pivot : ι -> μ)
    (hpivot_ne_zero : ∀ i, rows i (pivot i) ≠ 0)
    (hpivot_offdiag : ∀ i j, i ≠ j -> rows j (pivot i) = 0) :
    LinearIndependent ℚ rows := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum i
  have hcoord : (∑ j, coeff j • rows j) (pivot i) = 0 := by
    simpa using congrFun hsum (pivot i)
  have hsingle :
      (∑ j, coeff j • rows j) (pivot i) =
        coeff i * rows i (pivot i) := by
    rw [Finset.sum_apply]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hj
      simp [hpivot_offdiag i j hj.symm]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hmul : coeff i * rows i (pivot i) = 0 := by
    simpa [hsingle] using hcoord
  exact (mul_eq_zero.mp hmul).elim id (fun hrow => (hpivot_ne_zero i hrow).elim)

/-- The row-count lower bound supplied by private leading monomials.

If the selected rows sit inside the actual SPDP row space, represented here
by the external comparison `span_rank_le_spdp`, then the number of private
pivots is a lower bound on the SPDP rank. -/
theorem leadingSupport_card_le_spdpRank
    {ι μ : Type*} [Fintype ι] [Fintype μ]
    (rows : ι -> μ -> ℚ) (pivot : ι -> μ)
    (hpivot_ne_zero : ∀ i, rows i (pivot i) ≠ 0)
    (hpivot_offdiag : ∀ i j, i ≠ j -> rows j (pivot i) = 0)
    {spdpRank : Nat}
    (span_rank_le_spdp : (Set.range rows).finrank ℚ <= spdpRank) :
    Fintype.card ι <= spdpRank := by
  have hli := leadingSupport_linearIndependent rows pivot hpivot_ne_zero hpivot_offdiag
  have hcard_span : Fintype.card ι <= (Set.range rows).finrank ℚ :=
    (linearIndependent_iff_card_le_finrank_span.mp hli)
  exact le_trans hcard_span span_rank_le_spdp

/-! ### Distinct leading monomials

The private-pivot theorem above is enough for unshifted residual indicators,
but shifted partial derivatives usually share non-leading monomials.  The
standard GKKS/KLSS argument only needs a term order: each selected row has a
nonzero leading monomial, no monomial larger than that leading monomial, and
the selected leading monomials are distinct.  A maximal-leading-term
elimination then gives linear independence.
-/

/-- Rows with distinct leading monomials are linearly independent.

`hlead_max i m` says row `i` has no support above `lead i` in the chosen term
order.  Other rows may have nonzero coefficient at `lead i`; the proof chooses
a maximal active lead in a hypothetical relation, so all other active rows are
strictly below that coordinate. -/
theorem distinctLeadingMonomial_linearIndependent
    {ι μ : Type*} [Fintype ι] [LinearOrder μ]
    (rows : ι -> μ -> ℚ) (lead : ι -> μ)
    (hlead_ne_zero : ∀ i, rows i (lead i) ≠ 0)
    (hlead_max : ∀ i m, lead i < m -> rows i m = 0)
    (hlead_inj : Function.Injective lead) :
    LinearIndependent ℚ rows := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum i
  by_contra hcoeff_i
  let active : Finset ι := Finset.univ.filter fun j => coeff j ≠ 0
  have hi_active : i ∈ active := by
    simp [active, hcoeff_i]
  have hactive_nonempty : active.Nonempty := ⟨i, hi_active⟩
  let leadSet : Finset μ := active.image lead
  have hleadSet_nonempty : leadSet.Nonempty := by
    exact ⟨lead i, Finset.mem_image.mpr ⟨i, hi_active, rfl⟩⟩
  let top : μ := leadSet.max' hleadSet_nonempty
  obtain ⟨j, hj_active, hj_top⟩ : ∃ j ∈ active, lead j = top := by
    have htop_mem : top ∈ leadSet := Finset.max'_mem leadSet hleadSet_nonempty
    rcases Finset.mem_image.mp htop_mem with ⟨j, hj, hjtop⟩
    exact ⟨j, hj, hjtop⟩
  have hj_coeff : coeff j ≠ 0 := by
    exact (Finset.mem_filter.mp hj_active).2
  have hcoord : (∑ k, coeff k • rows k) (lead j) = 0 := by
    simpa using congrFun hsum (lead j)
  have hsingle :
      (∑ k, coeff k • rows k) (lead j) =
        coeff j * rows j (lead j) := by
    rw [Finset.sum_apply]
    refine Finset.sum_eq_single j ?_ ?_
    · intro k _ hkj
      by_cases hk_coeff : coeff k = 0
      · simp [hk_coeff]
      · have hk_active : k ∈ active := by
          simp [active, hk_coeff]
        have hk_le_top : lead k ≤ top := by
          exact Finset.le_max' leadSet (lead k)
            (Finset.mem_image.mpr ⟨k, hk_active, rfl⟩)
        have hk_le_j : lead k ≤ lead j := by
          simpa [top, hj_top] using hk_le_top
        have hk_ne_lead : lead k ≠ lead j := by
          intro hlead_eq
          exact hkj (hlead_inj hlead_eq)
        have hk_lt_j : lead k < lead j :=
          lt_of_le_of_ne hk_le_j hk_ne_lead
        simp [hlead_max k (lead j) hk_lt_j]
    · intro hj_not_mem
      exact (hj_not_mem (Finset.mem_univ j)).elim
  have hmul : coeff j * rows j (lead j) = 0 := by
    simpa [hsingle] using hcoord
  exact hj_coeff ((mul_eq_zero.mp hmul).elim id
    (fun hrow => (hlead_ne_zero j hrow).elim))

/-- Row-count lower bound supplied by distinct leading monomials. -/
theorem distinctLeadingMonomial_card_le_spdpRank
    {ι μ : Type*} [Fintype ι] [LinearOrder μ]
    (rows : ι -> μ -> ℚ) (lead : ι -> μ)
    (hlead_ne_zero : ∀ i, rows i (lead i) ≠ 0)
    (hlead_max : ∀ i m, lead i < m -> rows i m = 0)
    (hlead_inj : Function.Injective lead)
    {spdpRank : Nat}
    (span_rank_le_spdp : (Set.range rows).finrank ℚ <= spdpRank) :
    Fintype.card ι <= spdpRank := by
  have hli := distinctLeadingMonomial_linearIndependent rows lead
    hlead_ne_zero hlead_max hlead_inj
  have hcard_span : Fintype.card ι <= (Set.range rows).finrank ℚ :=
    (linearIndependent_iff_card_le_finrank_span.mp hli)
  exact le_trans hcard_span span_rank_le_spdp

/-- Construct the NW independence certificate from private leading monomials.

The genuinely NW-specific asymptotic work is now the construction of the
arguments:

* many selected rows (`support.lower <= Fintype.card ι`);
* private pivots (`hpivot_ne_zero`, `hpivot_offdiag`);
* containment of those rows in the actual SPDP row space
  (`span_rank_le_spdp`).

Once those are supplied, the SPDP lower bound is fully proved. -/
def NWSPDPIndependenceCertificate.ofLeadingSupport
    {numVars degree kappa ell : Nat}
    {ι μ : Type*} [Fintype ι] [Fintype μ]
    (support : NWLeadingSupportData)
    (rows : ι -> μ -> ℚ) (pivot : ι -> μ)
    (hpivot_ne_zero : ∀ i, rows i (pivot i) ≠ 0)
    (hpivot_offdiag : ∀ i j, i ≠ j -> rows j (pivot i) = 0)
    (spdpRank : Nat)
    (support_lower_le_rows : support.lower <= Fintype.card ι)
    (span_rank_le_spdp : (Set.range rows).finrank ℚ <= spdpRank) :
    NWSPDPIndependenceCertificate numVars degree kappa ell where
  support := support
  spdpRank := spdpRank
  support_lower_le_rank :=
    le_trans support_lower_le_rows
      (leadingSupport_card_le_spdpRank rows pivot hpivot_ne_zero
        hpivot_offdiag span_rank_le_spdp)

/-- Construct the NW independence certificate from distinct leading monomials
under a term order.  This is the version meant for shifted NW rows. -/
def NWSPDPIndependenceCertificate.ofDistinctLeadingMonomials
    {numVars degree kappa ell : Nat}
    {ι μ : Type*} [Fintype ι] [LinearOrder μ]
    (support : NWLeadingSupportData)
    (rows : ι -> μ -> ℚ) (lead : ι -> μ)
    (hlead_ne_zero : ∀ i, rows i (lead i) ≠ 0)
    (hlead_max : ∀ i m, lead i < m -> rows i m = 0)
    (hlead_inj : Function.Injective lead)
    (spdpRank : Nat)
    (support_lower_le_rows : support.lower <= Fintype.card ι)
    (span_rank_le_spdp : (Set.range rows).finrank ℚ <= spdpRank) :
    NWSPDPIndependenceCertificate numVars degree kappa ell where
  support := support
  spdpRank := spdpRank
  support_lower_le_rank :=
    le_trans support_lower_le_rows
      (distinctLeadingMonomial_card_le_spdpRank rows lead
        hlead_ne_zero hlead_max hlead_inj span_rank_le_spdp)

/-- Turn an NW independence certificate and a depth-3 upper bound into the
same comparison object used by the circuit-size theorem. -/
def NWSPDPIndependenceCertificate.toComparison
    {numVars degree kappa ell : Nat}
    (H : NWSPDPIndependenceCertificate numVars degree kappa ell)
    (productGates : Nat)
    (upper :
      H.spdpRank <=
        productGates * depth3SpdpDenominator numVars degree kappa ell) :
    Depth3SPDPComparison numVars degree kappa ell where
  productGates := productGates
  spdpRank := H.spdpRank
  analyticLower := H.support.lower
  lower_le_rank := H.support_lower_le_rank
  rank_le_depth3 := upper

/-- The NW lower-bound theorem in circuit-size form. -/
theorem depth3_product_gate_lower_bound_of_NW_independence
    {numVars degree kappa ell : Nat}
    (H : NWSPDPIndependenceCertificate numVars degree kappa ell)
    (productGates : Nat)
    (upper :
      H.spdpRank <=
        productGates * depth3SpdpDenominator numVars degree kappa ell) :
    H.support.lower <=
      productGates * depth3SpdpDenominator numVars degree kappa ell :=
  depth3_product_gate_lower_bound (H.toComparison productGates upper)

/-- The no-small-depth-3-circuit form of the NW route. -/
theorem no_depth3_circuit_of_NW_independence_gap
    {numVars degree kappa ell : Nat}
    (H : NWSPDPIndependenceCertificate numVars degree kappa ell)
    (productGates : Nat)
    (upper :
      H.spdpRank <=
        productGates * depth3SpdpDenominator numVars degree kappa ell)
    (hgap :
      productGates * depth3SpdpDenominator numVars degree kappa ell <
        H.support.lower) :
    False :=
  no_depth3_comparison_of_capacity_lt_lower
    (H.toComparison productGates upper) hgap

/-! ## Axiom audit -/

#print axioms depth3_product_gate_lower_bound
#print axioms no_depth3_comparison_of_capacity_lt_lower
#print axioms leadingSupport_linearIndependent
#print axioms leadingSupport_card_le_spdpRank
#print axioms NWSPDPIndependenceCertificate.ofLeadingSupport
#print axioms distinctLeadingMonomial_linearIndependent
#print axioms distinctLeadingMonomial_card_le_spdpRank
#print axioms NWSPDPIndependenceCertificate.ofDistinctLeadingMonomials
#print axioms depth3_product_gate_lower_bound_of_NW_independence
#print axioms no_depth3_circuit_of_NW_independence_gap

end PallLean.Paper93.DeepMath.AlgebraicSPDP
