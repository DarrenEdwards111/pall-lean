import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameNearCompleteInformationEndpoint

/-!
# Ramanujan/amplituhedron list-recovery endpoint

Higher-order fibre capacity has a standard coding-theoretic form.  An
amplituhedron cell is list recoverable with radius/list bound `r` when it carries
a candidate list of at most `r` continuation labels and the true label is always
on the list.

This file proves that finite cell list recovery is exactly equivalent to the
previous fibre-capacity law.  It therefore identifies the precise role an
expander code would have to play: SAT correctness must turn every solver-induced
positive cell into a polynomial-size list of compatible continuations.

Ordinary Ramanujan expansion does not prove this property.  If such polynomial
list recovery and polynomially many cells were available, the existing
`2^m <= cells * listSize` count would give the exponential contradiction.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint

/-! ## Cell list recovery -/

/-- A decoder attaches at most `r` candidate continuation labels to every cell,
and always includes the label that produced the cell. -/
structure CellListRecovery
    {m : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) (r : Nat) where
  candidates : Cell -> Finset (Assignment m)
  covers : forall a : Assignment m, a ∈ candidates (cellOf a)
  listSize : forall c : Cell, (candidates c).card <= r

namespace CellListRecovery

/-- A list decoder immediately bounds every exact cell fibre. -/
theorem toFiberCapacity
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (L : CellListRecovery cellOf r) :
    FiberCapacityAtMost cellOf r := by
  intro c
  have hsub :
      (Finset.univ : Finset (Assignment m)).filter
          (fun a => cellOf a = c) ⊆ L.candidates c := by
    intro a ha
    have hac : cellOf a = c := (Finset.mem_filter.mp ha).2
    simpa [hac] using L.covers a
  exact le_trans (Finset.card_le_card hsub) (L.listSize c)

/-- Conversely, the exact fibre itself is a canonical candidate list. -/
noncomputable def ofFiberCapacity
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (hcap : FiberCapacityAtMost cellOf r) :
    CellListRecovery cellOf r where
  candidates c :=
    (Finset.univ : Finset (Assignment m)).filter (fun a => cellOf a = c)
  covers a := by simp
  listSize := hcap

/-- List recovery and higher-order fibre capacity are exactly the same finite
condition. -/
theorem nonempty_iff_fiberCapacity
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell) :
    Nonempty (CellListRecovery cellOf r) <-> FiberCapacityAtMost cellOf r := by
  constructor
  · rintro ⟨L⟩
    exact L.toFiberCapacity
  · intro hcap
    exact ⟨ofFiberCapacity cellOf hcap⟩

/-- Unique list recovery (`r = 1`) is exactly strong enough to make the cell map
injective. -/
theorem cellOf_injective_of_listSize_one
    {m : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (L : CellListRecovery cellOf 1) :
    Function.Injective cellOf := by
  intro a b hab
  have hb : b ∈ L.candidates (cellOf a) := by
    rw [hab]
    exact L.covers b
  exact Finset.card_le_one.mp (L.listSize (cellOf a))
    a (L.covers a) b hb

/-- Every list-recoverable cell decomposition obeys the exact
cells-times-list-size lower bound. -/
theorem assignment_card_le_cells_mul_listSize
    {m r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    {cellOf : Assignment m -> Cell}
    (L : CellListRecovery cellOf r) :
    2 ^ m <= Fintype.card Cell * r :=
  assignment_card_le_cell_card_mul_capacity cellOf L.toFiberCapacity

end CellListRecovery

/-! ## Polynomial list recovery is the load-bearing solver theorem -/

/-- Polynomially many cells with polynomial candidate lists cannot cover all
continuation labels beyond the exponential gap. -/
theorem no_polynomial_cells_and_listRecovery
    {m k d : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (hcells : Fintype.card Cell <= m ^ k)
    (L : CellListRecovery cellOf (m ^ d))
    (hgap : m ^ (k + d) < 2 ^ m) : False :=
  no_polynomial_cells_and_fibers cellOf hcells L.toFiberCapacity hgap

/-- The exact proposed Ramanujan/amplituhedron bridge for one alleged solver:
correctness must yield polynomial list recovery of its positive cells. -/
structure SolverExpanderListRecoveryFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  k : Nat
  d : Nat
  Cell : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  cellOf : Assignment m -> Cell
  polyCells : @Fintype.card Cell cellFintype <= m ^ k
  listRecovery_of_decides : DecidesSAT U D ->
    @CellListRecovery m Cell cellFintype cellDecidableEq cellOf (m ^ d)
  expGap : m ^ (k + d) < 2 ^ m

namespace SolverExpanderListRecoveryFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- A genuine solver-correct polynomial list-recovery theorem refutes that
solver. -/
theorem not_decidesSAT (B : SolverExpanderListRecoveryFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype B.Cell := B.cellFintype
  letI : DecidableEq B.Cell := B.cellDecidableEq
  exact no_polynomial_cells_and_listRecovery B.cellOf B.polyCells
    (B.listRecovery_of_decides hD) B.expGap

end SolverExpanderListRecoveryFor

/-- Solver-indexed polynomial list recovery for every certified machine rules
out polynomial SAT decision. -/
theorem no_SATDecisionInP_of_expanderListRecovery
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverExpanderListRecoveryFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨B⟩ := H D
  exact B.not_decidesSAT hD

end PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint.CellListRecovery.nonempty_iff_fiberCapacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint.CellListRecovery.cellOf_injective_of_listSize_one
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint.no_polynomial_cells_and_listRecovery
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameExpanderListRecoveryEndpoint.no_SATDecisionInP_of_expanderListRecovery
