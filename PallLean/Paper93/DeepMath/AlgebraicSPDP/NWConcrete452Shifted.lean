import PallLean.Paper93.DeepMath.AlgebraicSPDP.NWConcrete452

/-!
# Concrete NW(4,5,2) Shifted-Leading Count

This file formalizes the finite shifted-leading combinatorics behind the
diagnostic value

`Gamma_{2,1}(NW_{4,5,2}) = 1550`.

The rows considered here are the concrete `kappa = 2`, `ell = 1` candidate
rows:

* a derivative point window `D` of size `2`;
* an affine label `a : ZMod 5 × ZMod 5`;
* a shift monomial of degree `0` or `1`.

Each candidate has a leading exponent vector obtained by taking the residual
graph outside `D` and adding the degree-`<=1` shift.  The theorem below closes
the finite combinatorial count: after quotienting collisions by choosing a
canonical representative for each leading exponent, exactly `1550` leading
monomials remain.

This is the strong shifted-leading count layer.  The remaining algebraic layer
is to connect these representatives to coefficient projections of actual
shifted partial derivatives in `SPDP.spdpSubspace 2 1`.
-/

namespace PallLean.Paper93.DeepMath.AlgebraicSPDP

open scoped BigOperators

namespace NW452

/-- The six two-point derivative windows for `NW_{4,5,2}`. -/
inductive Window2 where
  | w01 | w02 | w03 | w12 | w13 | w23
deriving DecidableEq, Fintype

/-- Interpret an explicit two-point window as a `Finset Point`. -/
def Window2.toFinset : Window2 -> Finset Point
  | Window2.w01 => {0, 1}
  | Window2.w02 => {0, 2}
  | Window2.w03 => {0, 3}
  | Window2.w12 => {1, 2}
  | Window2.w13 => {1, 3}
  | Window2.w23 => {2, 3}

/-- Degree-`<=1` shifts: `none` is the constant shift, `some v` is `X_v`. -/
abbrev ShiftLE1 := Option (Fin 20)

/-- Candidate shifted partial rows: window, label, and degree-`<=1` shift. -/
structure ShiftedCandidate where
  D : Window2
  a : Label
  shift : ShiftLE1
deriving DecidableEq, Fintype

/-- Residual encoded graph support outside a two-point derivative window. -/
noncomputable def candidateResidual (c : ShiftedCandidate) : Finset (Fin 20) :=
  nwEncodedGraphOff enc code c.D.toFinset c.a

/-- Exponent of variable `v` in the candidate leading monomial. -/
noncomputable def candidateExpAt (c : ShiftedCandidate) (v : Fin 20) : Nat :=
  (if v ∈ candidateResidual c then 1 else 0) +
    (if c.shift = some v then 1 else 0)

/-- Base-3 encoding of the bounded exponent vector.

For these candidates every exponent is `0`, `1`, or `2`, so this is a faithful
encoding of the leading monomial exponent vector. -/
noncomputable def candidateLeadCode (c : ShiftedCandidate) : Nat :=
  ∑ v : Fin 20, candidateExpAt c v * 3 ^ v.val

/-- The four three-point supports in a four-point universe, represented by the
omitted point. -/
inductive Point3Support where
  | omit0 | omit1 | omit2 | omit3
deriving DecidableEq, Fintype

/-- The ten unordered two-value supports in `ZMod 5`. -/
inductive ValuePair2 where
  | v01 | v02 | v03 | v04 | v12 | v13 | v14 | v23 | v24 | v34
deriving DecidableEq, Fintype

/-- Degree-two residual graph leads: choose two point positions and values. -/
abbrev Deg2GraphLeadShape :=
  Window2 × Value × Value

/-- Degree-three leads with one squared residual variable. -/
abbrev SquaredResidualLeadShape :=
  Window2 × Value × Value × Bool

/-- Degree-three squarefree leads supported on three distinct point positions. -/
abbrev ThreePointLeadShape :=
  Point3Support × Value × Value × Value

/-- Degree-three squarefree leads with two values at one point and one value at
another point. -/
abbrev TwoValuesAtOnePointLeadShape :=
  Window2 × Bool × ValuePair2 × Value

/-- The shifted-leading shape classification for the concrete `NW_{4,5,2}`,
`(kappa,ell)=(2,1)` family.

The summands have cardinalities `150`, `300`, `500`, and `600`, respectively:

* unshifted degree-two residual graph leads;
* shifted leads that square one residual variable;
* shifted squarefree leads on three distinct point positions;
* shifted squarefree leads with two values at one point and one value at a
  second point.
-/
abbrev ShiftedLeadShape :=
  Deg2GraphLeadShape ⊕ SquaredResidualLeadShape ⊕
    ThreePointLeadShape ⊕ TwoValuesAtOnePointLeadShape

theorem window2_card : Fintype.card Window2 = 6 := by
  decide

theorem point3Support_card : Fintype.card Point3Support = 4 := by
  decide

theorem valuePair2_card : Fintype.card ValuePair2 = 10 := by
  decide

theorem value_card : Fintype.card Value = 5 := by
  decide

/-- The finite shifted-leading count for the concrete `NW_{4,5,2}` candidate
family at `(kappa,ell)=(2,1)`.

This is the structural version of the diagnostic count
`150 + 300 + 500 + 600 = 1550`; it avoids the earlier one-shot quotient over
all `3150` candidate rows. -/
theorem shiftedLeadShape_card :
    Fintype.card ShiftedLeadShape = 1550 := by
  simp [ShiftedLeadShape, Deg2GraphLeadShape, SquaredResidualLeadShape,
    ThreePointLeadShape, TwoValuesAtOnePointLeadShape, window2_card,
    point3Support_card, valuePair2_card]

/-- Support data for the strong shifted-leading count. -/
def shiftedSupport : NWLeadingSupportData where
  basePartialRows := 1550
  legalShiftRows := 1
  collisionDefect := 0

theorem shiftedSupport_lower :
    shiftedSupport.lower = 1550 := by
  simp [shiftedSupport, NWLeadingSupportData.lower]

/-- Conditional strong shifted-leading SPDP certificate for the concrete
`NW_{4,5,2}` polynomial.

The remaining substantive bridge is exactly the construction of `rows`, `lead`,
and the containment proof `span_rank_le_spdp` from actual shifted partials of
`nwMvPolynomial enc code`.  Once those are supplied, the existing triangular
leading-monomial engine turns the finite `1550` count into a lower bound on the
actual `SPDP.spdpRank 2 1`. -/
noncomputable def shiftedCertificate_of_distinctLeadingRows
    {μ : Type*} [LinearOrder μ]
    (rows : ShiftedLeadShape -> μ -> ℚ)
    (lead : ShiftedLeadShape -> μ)
    (hlead_ne_zero : ∀ i, rows i (lead i) ≠ 0)
    (hlead_max : ∀ i m, lead i < m -> rows i m = 0)
    (hlead_inj : Function.Injective lead)
    (span_rank_le_spdp :
      (Set.range rows).finrank ℚ <=
        SPDP.spdpRank 2 1 (nwMvPolynomial enc code)) :
    NWSPDPIndependenceCertificate 20 4 2 1 :=
  NWSPDPIndependenceCertificate.ofDistinctLeadingMonomials
    (support := shiftedSupport)
    (rows := rows)
    (lead := lead)
    (spdpRank := SPDP.spdpRank 2 1 (nwMvPolynomial enc code))
    hlead_ne_zero
    hlead_max
    hlead_inj
    (by
      rw [shiftedSupport_lower, shiftedLeadShape_card])
    span_rank_le_spdp

/-- The target strong concrete lower bound once the shifted-leading rows are
connected to the actual SPDP subspace. -/
theorem spdpRank_nw452_ge_1550_of_distinctLeadingRows
    {μ : Type*} [LinearOrder μ]
    (rows : ShiftedLeadShape -> μ -> ℚ)
    (lead : ShiftedLeadShape -> μ)
    (hlead_ne_zero : ∀ i, rows i (lead i) ≠ 0)
    (hlead_max : ∀ i m, lead i < m -> rows i m = 0)
    (hlead_inj : Function.Injective lead)
    (span_rank_le_spdp :
      (Set.range rows).finrank ℚ <=
        SPDP.spdpRank 2 1 (nwMvPolynomial enc code)) :
    1550 <= SPDP.spdpRank 2 1 (nwMvPolynomial enc code) := by
  simpa [shiftedSupport_lower] using
    (shiftedCertificate_of_distinctLeadingRows rows lead hlead_ne_zero
      hlead_max hlead_inj span_rank_le_spdp).support_lower_le_rank

/-! ## Axiom audit -/

#print axioms shiftedLeadShape_card
#print axioms shiftedCertificate_of_distinctLeadingRows
#print axioms spdpRank_nw452_ge_1550_of_distinctLeadingRows

end NW452

end PallLean.Paper93.DeepMath.AlgebraicSPDP
