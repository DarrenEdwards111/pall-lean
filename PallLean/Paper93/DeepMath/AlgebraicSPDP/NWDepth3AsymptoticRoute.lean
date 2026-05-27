import PallLean.Paper93.DeepMath.AlgebraicSPDP.NWConcrete452ShiftedActual

/-!
# NW Depth-3 Asymptotic Route

This file records the ambitious algebraic-complexity ladder that remains
closest in spirit to the original SPDP program:

* prove shifted-partial-derivative lower bounds for an explicit
  Nisan-Wigderson family;
* compare them against the standard homogeneous depth-3 upper bound;
* conclude that no polynomial-size depth-3 family can compute those
  polynomials once the NW lower bound outruns every polynomial capacity.

This is not a Boolean `P` versus `NP` theorem.  It is the correct algebraic
target: a reusable asymptotic interface for turning future NW shifted-leading
rank theorems into arithmetic-circuit lower bounds.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

open scoped BigOperators

/-- One SPDP scale for a member of an NW-like family. -/
structure NWDepth3Scale where
  numVars : Nat
  degree : Nat
  kappa : Nat
  ell : Nat

/-- The depth-3 capacity denominator at one scale. -/
def NWDepth3Scale.denominator (S : NWDepth3Scale) : Nat :=
  depth3SpdpDenominator S.numVars S.degree S.kappa S.ell

/-- A family of NW independence certificates, indexed by a scale parameter.

The hard asymptotic work is hidden in `cert`: for each scale, an actual
shifted-leading/SPDP lower-bound certificate must be supplied.  The theorem
below only proves the conversion from those certificates to depth-3
lower bounds.
-/
structure NWDepth3CertificateFamily where
  scale : Nat -> NWDepth3Scale
  cert : ∀ n,
    NWSPDPIndependenceCertificate
      (scale n).numVars (scale n).degree (scale n).kappa (scale n).ell

/-- A depth-3 realization/upper-bound surface for the same family.

`productGates n` is the number of product gates in the claimed depth-3
representation at scale `n`.  The `upper` field is the standard SPDP upper
bound for that representation.
-/
structure Depth3UpperFamily (F : NWDepth3CertificateFamily) where
  productGates : Nat -> Nat
  upper : ∀ n,
    (F.cert n).spdpRank <=
      productGates n * (F.scale n).denominator

/-- A function is polynomially bounded in the scale index.  We use `n + 1`
so the statement is nondegenerate at `n = 0`. -/
def PolynomiallyBounded (g : Nat -> Nat) : Prop :=
  ∃ C, ∀ n, g n <= (n + 1) ^ C

/-- The NW lower bound beats every polynomial-size depth-3 capacity bound.

This is the asymptotic SPDP/NW theorem one would prove by the design
counting argument in the GKKS/KLSS regime.
-/
def NWLowerBeatsPolynomialDepth3Capacity
    (F : NWDepth3CertificateFamily) : Prop :=
  ∀ C, ∃ n,
    (n + 1) ^ C * (F.scale n).denominator < (F.cert n).support.lower

/-- Pointwise depth-3 product-gate lower bound for an NW certificate family. -/
theorem depth3_family_product_gate_lower_bound
    (F : NWDepth3CertificateFamily) (U : Depth3UpperFamily F) (n : Nat) :
    (F.cert n).support.lower <=
      U.productGates n * (F.scale n).denominator := by
  exact depth3_product_gate_lower_bound_of_NW_independence
    (F.cert n) (U.productGates n) (U.upper n)

/-- Asymptotic exclusion theorem.

If the NW shifted-leading lower bound outruns every polynomial depth-3
capacity bound, then no polynomially bounded depth-3 upper-bound family can
exist.
-/
theorem no_polynomial_depth3_family_of_NW_asymptotic_gap
    (F : NWDepth3CertificateFamily)
    (U : Depth3UpperFamily F)
    (hpoly : PolynomiallyBounded U.productGates)
    (hgap : NWLowerBeatsPolynomialDepth3Capacity F) :
    False := by
  rcases hpoly with ⟨C, hC⟩
  rcases hgap C with ⟨n, hn_gap⟩
  have hlower :=
    depth3_family_product_gate_lower_bound F U n
  have hcap :
      U.productGates n * (F.scale n).denominator <=
        (n + 1) ^ C * (F.scale n).denominator :=
    Nat.mul_le_mul_right _ (hC n)
  exact (not_lt_of_ge (le_trans hlower hcap)) hn_gap

namespace NW452

/-- The closed concrete `NW_{4,5,2}` shifted certificate at `(κ,ℓ)=(2,1)`.

This packages the already-proved theorem
`spdpRank_nw452_ge_1550` in the generic certificate interface. -/
noncomputable def shifted1550Certificate :
    NWSPDPIndependenceCertificate 20 4 2 1 where
  support := shiftedSupport
  spdpRank := SPDP.spdpRank 2 1 (nwMvPolynomial enc code)
  support_lower_le_rank := by
    simpa [shiftedSupport_lower] using spdpRank_nw452_ge_1550

/-- The concrete depth-3 denominator at the closed `NW_{4,5,2}` shifted scale. -/
theorem depth3Denominator_20_4_2_1 :
    depth3SpdpDenominator 20 4 2 1 = 126 := by
  rw [show depth3SpdpDenominator 20 4 2 1 =
    Nat.choose 4 2 * Nat.choose 21 1 by rfl]
  rw [show Nat.choose 4 2 = 6 by decide]
  simp

/-- Multiplicative depth-3 lower bound from the closed `1550` SPDP theorem. -/
theorem depth3_capacity_lower_bound_of_shifted1550
    (productGates : Nat)
    (upper :
      SPDP.spdpRank 2 1 (nwMvPolynomial enc code) <=
        productGates * depth3SpdpDenominator 20 4 2 1) :
    1550 <= productGates * 126 := by
  have h :=
    depth3_product_gate_lower_bound_of_NW_independence
      shifted1550Certificate productGates upper
  simpa [shifted1550Certificate, shiftedSupport_lower,
    depth3Denominator_20_4_2_1] using h

/-- Concrete depth-3 product-gate lower bound:
any homogeneous depth-3 representation satisfying the standard SPDP upper
bound must have at least `13` product gates. -/
theorem depth3_product_gates_ge_13_of_shifted1550
    (productGates : Nat)
    (upper :
      SPDP.spdpRank 2 1 (nwMvPolynomial enc code) <=
        productGates * depth3SpdpDenominator 20 4 2 1) :
    13 <= productGates := by
  have hcap := depth3_capacity_lower_bound_of_shifted1550 productGates upper
  by_contra hnot
  have hsmall : productGates <= 12 := by
    have hlt : productGates < 13 := Nat.lt_of_not_ge hnot
    omega
  omega

/-- Exclusion form: no depth-3 representation with at most `12` product
gates can satisfy the standard SPDP upper bound for the concrete shifted
`NW_{4,5,2}` polynomial. -/
theorem no_depth3_upper_with_at_most_12_product_gates
    (productGates : Nat)
    (hsmall : productGates <= 12)
    (upper :
      SPDP.spdpRank 2 1 (nwMvPolynomial enc code) <=
        productGates * depth3SpdpDenominator 20 4 2 1) :
    False := by
  have hge := depth3_product_gates_ge_13_of_shifted1550 productGates upper
  omega

end NW452

/-! ## Axiom audit -/

#print axioms depth3_family_product_gate_lower_bound
#print axioms no_polynomial_depth3_family_of_NW_asymptotic_gap
#print axioms NW452.shifted1550Certificate
#print axioms NW452.depth3_capacity_lower_bound_of_shifted1550
#print axioms NW452.depth3_product_gates_ge_13_of_shifted1550
#print axioms NW452.no_depth3_upper_with_at_most_12_product_gates

end PallLean.Paper93.DeepMath.AlgebraicSPDP
