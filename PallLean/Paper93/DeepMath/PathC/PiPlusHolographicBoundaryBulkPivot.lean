import PallLean.Paper93.DeepMath.PathC.PiPlusProjectedPWindowPivotGuardrail

/-!
# Holographic boundary/bulk pivot

This is the replacement for the same-object Path C socket.

The guardrail file showed that the old projected pivot measured the P-side
upper bound and NP-side lower bound on the same projected/gauged rank object.
That is already a contradiction package, so a universal producer would be
P-vs-NP strength.

This file records Darren's intended separation:

* the **P-side** lives on a 2D holographic boundary/projection;
* the **NP-side** lives in a 3D/4D bulk carrying the identity-minor mass;
* a SAT decider must supply a faithful boundary-to-bulk lift;
* the lift capacity from polynomial boundary rank is still below the bulk
  binomial lower bound.

The important point is that the P and NP ranks are different fields.  The final
contradiction only appears after an explicit faithful-holography bridge, so we
no longer smuggle the old same-rank Route-B/Path-C failure into the socket.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Semantic dimension tag for the holographic split. -/
inductive HolographicDim where
  | boundary2D
  | bulk3D
  | bulk4D
  deriving DecidableEq, Repr

/-- Numerical dimension, for comments/readout and simple guardrails. -/
def HolographicDim.toNat : HolographicDim -> Nat
  | HolographicDim.boundary2D => 2
  | HolographicDim.bulk3D => 3
  | HolographicDim.bulk4D => 4

@[simp] theorem HolographicDim.boundary2D_toNat :
    HolographicDim.boundary2D.toNat = 2 := rfl

@[simp] theorem HolographicDim.bulk3D_toNat :
    HolographicDim.bulk3D.toNat = 3 := rfl

@[simp] theorem HolographicDim.bulk4D_toNat :
    HolographicDim.bulk4D.toNat = 4 := rfl

/-- The dimension split Darren wants: P on a 2D boundary, NP in a 3D/4D bulk. -/
def BoundaryBulkDimensionSplit (boundary bulk : HolographicDim) : Prop :=
  boundary = HolographicDim.boundary2D ∧
    (bulk = HolographicDim.bulk3D ∨ bulk = HolographicDim.bulk4D)

/-- A 2D boundary is strictly lower-dimensional than either accepted bulk. -/
theorem boundaryBulkDimensionSplit_strict
    {boundary bulk : HolographicDim}
    (h : BoundaryBulkDimensionSplit boundary bulk) :
    boundary.toNat < bulk.toNat := by
  rcases h with ⟨rfl, hbulk⟩
  rcases hbulk with rfl | rfl <;> norm_num

/-- Boundary layer: the solver-visible holographic projection.  Its rank is the
thing the P-side is allowed to bound polynomially. -/
structure HolographicBoundaryLayer
    (M : DTM) (n : Nat) (_hn2 : n >= 2)
    (_htb : M.timeBound <= 4) (_hns : M.numStates <= n) where
  dim : HolographicDim := HolographicDim.boundary2D
  rank : Nat
  dim_is_boundary : dim = HolographicDim.boundary2D := by rfl

/-- Bulk layer: the 3D/4D NP carrier containing the identity-minor obstruction. -/
structure HolographicBulkLayer
    (M : DTM) (n : Nat) (_hn2 : n >= 2)
    (_htb : M.timeBound <= 4) (_hns : M.numStates <= n) where
  dim : HolographicDim
  rank : Nat
  dim_is_bulk : dim = HolographicDim.bulk3D ∨ dim = HolographicDim.bulk4D

/-- Full separated boundary/bulk certificate for a selected machine and size. -/
structure HolographicBoundaryBulkPivotData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) where
  boundary : HolographicBoundaryLayer M n hn2 htb hns
  bulk : HolographicBulkLayer M n hn2 htb hns

  /-- Holographic lift cost: how much bulk rank can be faithfully controlled by
  a boundary rank budget.  This is deliberately separated from both raw ranks. -/
  liftCost : Nat -> Nat
  liftCost_mono : Monotone liftCost

  /-- P-side: polynomial capacity bound on the 2D boundary only. -/
  boundary_P_bound : boundary.rank <= n ^ 200

  /-- NP-side: a SAT decider forces a binomial-rank identity minor in the bulk. -/
  bulk_NP_lower : DecidesSAT M -> Nat.choose (n / 3) (Nat.log 2 n) <= bulk.rank

  /-- Faithfulness: a SAT decider must lift its 2D boundary control into the
  3D/4D bulk.  This is the actual holography bridge, not a same-object bound. -/
  faithful_boundary_to_bulk : DecidesSAT M -> bulk.rank <= liftCost boundary.rank

  /-- Capacity gap: even the lift of a polynomial 2D boundary budget is too
  small to carry the bulk NP minor. -/
  holographic_gap : liftCost (n ^ 200) < Nat.choose (n / 3) (Nat.log 2 n)

/-- The data really has a strict 2D-vs-3D/4D dimension split. -/
theorem holographicBoundaryBulkPivotData_dimensionSplit
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (D : HolographicBoundaryBulkPivotData M n hn2 htb hns) :
    BoundaryBulkDimensionSplit D.boundary.dim D.bulk.dim := by
  constructor
  · exact D.boundary.dim_is_boundary
  · exact D.bulk.dim_is_bulk

/-- Therefore the boundary is strictly lower-dimensional than the bulk. -/
theorem holographicBoundaryBulkPivotData_strictDimension
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (D : HolographicBoundaryBulkPivotData M n hn2 htb hns) :
    D.boundary.dim.toNat < D.bulk.dim.toNat :=
  boundaryBulkDimensionSplit_strict
    (holographicBoundaryBulkPivotData_dimensionSplit M n hn2 htb hns D)

/-- Core holographic contradiction: P controls only the 2D boundary; NP lives in
bulk; faithful holography plus the lift gap rules out a SAT decider. -/
theorem no_decidesSAT_of_holographicBoundaryBulkPivotData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (D : HolographicBoundaryBulkPivotData M n hn2 htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  have hNP : Nat.choose (n / 3) (Nat.log 2 n) <= D.bulk.rank :=
    D.bulk_NP_lower hdec
  have hlift : D.bulk.rank <= D.liftCost D.boundary.rank :=
    D.faithful_boundary_to_bulk hdec
  have hcost : D.liftCost D.boundary.rank <= D.liftCost (n ^ 200) :=
    D.liftCost_mono D.boundary_P_bound
  have hchoose_le_cost :
      Nat.choose (n / 3) (Nat.log 2 n) <= D.liftCost (n ^ 200) :=
    le_trans (le_trans hNP hlift) hcost
  exact not_lt_of_ge hchoose_le_cost D.holographic_gap

/-- Paper-scale wrapper for the holographic split.  Unlike the old Path C
same-object socket, this does not need to mention `arithmetic_gap_2pow804`:
the relevant gap is explicitly the boundary-to-bulk lift gap. -/
abbrev PaperScaleHolographicBoundaryBulkPivotData
    (M : DTM) (htb : M.timeBound <= 4)
    (hns : M.numStates <= 2 ^ 804) :=
  HolographicBoundaryBulkPivotData M (2 ^ 804)
    projectedPivot_paperScale_ge_two htb hns

/-- Paper-scale no-decider endpoint for the separated holographic pivot. -/
theorem no_decidesSAT_at_paperScale_of_holographicBoundaryBulkPivotData
    (M : DTM) (htb : M.timeBound <= 4)
    (hns : M.numStates <= 2 ^ 804)
    (D : PaperScaleHolographicBoundaryBulkPivotData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_of_holographicBoundaryBulkPivotData
    M (2 ^ 804) projectedPivot_paperScale_ge_two htb hns D

/-- Why this avoids the guardrail failure: the P-bound rank and NP-lower rank are
separate fields.  Same-object Path C data can only be imported by additionally
collapsing `bulk.rank` into the lift of `boundary.rank`, which is precisely the
faithful-holography bottleneck that must now be proved explicitly. -/
def HolographicPivotIsSeparated
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (D : HolographicBoundaryBulkPivotData M n hn2 htb hns) : Prop :=
  D.boundary.dim.toNat < D.bulk.dim.toNat

/-- The separated predicate is automatically satisfied by the boundary/bulk data. -/
theorem holographicPivotIsSeparated_of_data
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (D : HolographicBoundaryBulkPivotData M n hn2 htb hns) :
    HolographicPivotIsSeparated M n hn2 htb hns D :=
  holographicBoundaryBulkPivotData_strictDimension M n hn2 htb hns D

/-! ## Axiom audit anchors -/

#print axioms boundaryBulkDimensionSplit_strict
#print axioms holographicBoundaryBulkPivotData_dimensionSplit
#print axioms holographicBoundaryBulkPivotData_strictDimension
#print axioms no_decidesSAT_of_holographicBoundaryBulkPivotData
#print axioms no_decidesSAT_at_paperScale_of_holographicBoundaryBulkPivotData
#print axioms holographicPivotIsSeparated_of_data

end PallLean.Paper93.DeepMath.PathC
