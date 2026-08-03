import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameInfiniteConflictChromaticEndpoint

/-!
# N-frame continuation-conflict hypergraphs and fibre capacity

Ordinary local edges only impose a graph colouring and can remain two-colourable
in unbounded dimension.  The higher-order replacement is to forbid a large set of
continuation labels from becoming monochromatic in one amplituhedron cell.

This file formalizes that condition in two equivalent forms:

* a conflict hyperedge is every label set of cardinality greater than `r`;
* equivalently, every colour/cell fibre has cardinality at most `r`.

The counting theorem is quantitative:

```text
2^m <= (# positive cells) * (maximum labels per cell).
```

Thus polynomially many cells can coexist with exponentially many labels only if
some cell absorbs a superpolynomial monochromatic cluster.  If Ramanujan/N-frame
geometry bounded both the cell count and every cell fibre polynomially, the
exponential contradiction would follow.  The solver bridge at the end isolates
exactly that missing higher-order theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy

/-! ## Cell-fibre capacity and hypergraph propriety -/

/-- Every amplituhedron cell contains at most `r` continuation labels. -/
def FiberCapacityAtMost
    {m : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) (r : Nat) : Prop :=
  forall c : Cell,
    ((Finset.univ : Finset (Assignment m)).filter
      (fun a => cellOf a = c)).card <= r

/-- No label set larger than `r` is monochromatic.  This is the proper-colouring
condition for the hypergraph containing all `(r+1)`-large conflict sets. -/
def AvoidsLargeMonochromaticSet
    {m : Nat} {Cell : Type} [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) (r : Nat) : Prop :=
  forall S : Finset (Assignment m), r < S.card ->
    ¬ exists c : Cell, forall a, a ∈ S -> cellOf a = c

/-- A uniform fibre bound forbids every oversized monochromatic hyperedge. -/
theorem avoidsLargeMonochromaticSet_of_fiberCapacity
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (hcap : FiberCapacityAtMost cellOf r) :
    AvoidsLargeMonochromaticSet cellOf r := by
  intro S hlarge
  rintro ⟨c, hc⟩
  have hsub : S ⊆ (Finset.univ : Finset (Assignment m)).filter
      (fun a => cellOf a = c) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc a ha
  have hle := Finset.card_le_card hsub
  exact (Nat.not_lt_of_ge (le_trans hle (hcap c))) hlarge

/-- Conversely, forbidding every oversized monochromatic hyperedge bounds each
cell fibre by `r`. -/
theorem fiberCapacity_of_avoidsLargeMonochromaticSet
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (havoid : AvoidsLargeMonochromaticSet cellOf r) :
    FiberCapacityAtMost cellOf r := by
  intro c
  by_contra hnot
  have hlarge : r < ((Finset.univ : Finset (Assignment m)).filter
      (fun a => cellOf a = c)).card := by omega
  exact havoid _ hlarge ⟨c, by
    intro a ha
    exact (Finset.mem_filter.mp ha).2⟩

/-- Hypergraph propriety and the cell-fibre capacity law are exactly equivalent. -/
theorem avoidsLargeMonochromaticSet_iff_fiberCapacity
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) :
    AvoidsLargeMonochromaticSet cellOf r <->
      FiberCapacityAtMost cellOf r :=
  ⟨fiberCapacity_of_avoidsLargeMonochromaticSet cellOf,
    avoidsLargeMonochromaticSet_of_fiberCapacity cellOf⟩

/-! ## Quantitative cell-times-fibre lower bound -/

/-- Partitioning the Boolean cube by cells and bounding every fibre gives the
fundamental higher-order counting inequality. -/
theorem assignment_card_le_cell_card_mul_capacity
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (hcap : FiberCapacityAtMost cellOf r) :
    2 ^ m <= Fintype.card Cell * r := by
  classical
  have hpartition :
      (Finset.univ : Finset (Assignment m)).card =
        ∑ c : Cell,
          ((Finset.univ : Finset (Assignment m)).filter
            (fun a => cellOf a = c)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := cellOf) (t := Finset.univ)
      (fun a _ => Finset.mem_univ (cellOf a))]
  have hcube :
      (Finset.univ : Finset (Assignment m)).card = 2 ^ m := by
    simp
  calc
    2 ^ m = (Finset.univ : Finset (Assignment m)).card := hcube.symm
    _ = ∑ c : Cell,
        ((Finset.univ : Finset (Assignment m)).filter
          (fun a => cellOf a = c)).card := hpartition
    _ <= ∑ _c : Cell, r := Finset.sum_le_sum (fun c _ => hcap c)
    _ = Fintype.card Cell * r := by simp

/-- If both the number of cells and the maximum monochromatic fibre are
polynomial, their product cannot cover the Boolean cube beyond the exponential
gap. -/
theorem no_polynomial_cells_and_fibers
    {m k d : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (hcells : Fintype.card Cell <= m ^ k)
    (hfibers : FiberCapacityAtMost cellOf (m ^ d))
    (hgap : m ^ (k + d) < 2 ^ m) : False := by
  have hcover := assignment_card_le_cell_card_mul_capacity cellOf hfibers
  have hupper : Fintype.card Cell * m ^ d <= m ^ k * m ^ d :=
    Nat.mul_le_mul_right (m ^ d) hcells
  have hpow : m ^ k * m ^ d = m ^ (k + d) := by
    exact (pow_add m k d).symm
  rw [hpow] at hupper
  exact (Nat.not_lt_of_ge (le_trans hcover hupper)) hgap

/-! ## Solver-indexed higher-order bridge -/

/-- A polynomial amplituhedron cell projection whose cell-fibre capacity follows
from SAT correctness.  This is the higher-order conflict-hypergraph analogue of
the previous proper graph-colouring bridge. -/
structure SolverConflictHypergraphBridgeFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  k : Nat
  d : Nat
  Cell : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  cellOf : Assignment m -> Cell
  polyCells : @Fintype.card Cell cellFintype <= m ^ k
  fiberCapacity_of_decides : DecidesSAT U D ->
    @FiberCapacityAtMost m Cell cellFintype cellDecidableEq cellOf (m ^ d)
  expGap : m ^ (k + d) < 2 ^ m

namespace SolverConflictHypergraphBridgeFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- A genuine correctness-derived polynomial fibre-capacity theorem rules out
the corresponding solver. -/
theorem not_decidesSAT (B : SolverConflictHypergraphBridgeFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype B.Cell := B.cellFintype
  letI : DecidableEq B.Cell := B.cellDecidableEq
  exact no_polynomial_cells_and_fibers B.cellOf B.polyCells
    (B.fiberCapacity_of_decides hD) B.expGap

end SolverConflictHypergraphBridgeFor

/-- Higher-order conflict bridges for every certified machine rule out polynomial
SAT decision. -/
theorem no_SATDecisionInP_of_conflictHypergraphBridges
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverConflictHypergraphBridgeFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨B⟩ := H D
  exact B.not_decidesSAT hD

end PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint.avoidsLargeMonochromaticSet_iff_fiberCapacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint.assignment_card_le_cell_card_mul_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint.no_polynomial_cells_and_fibers
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint.no_SATDecisionInP_of_conflictHypergraphBridges
