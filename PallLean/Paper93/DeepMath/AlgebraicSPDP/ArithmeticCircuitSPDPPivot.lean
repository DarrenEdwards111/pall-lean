import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic

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
#print axioms depth3_product_gate_lower_bound_of_NW_independence
#print axioms no_depth3_circuit_of_NW_independence_gap

end PallLean.Paper93.DeepMath.AlgebraicSPDP

