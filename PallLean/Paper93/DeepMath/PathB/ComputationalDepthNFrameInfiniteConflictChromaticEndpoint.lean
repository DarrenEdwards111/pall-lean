import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameLocalChargeChromaticBarrier

/-!
# Infinite-dimensional N-frame cube and the SAT conflict-chromatic endpoint

Passing from one Boolean cube to unbounded dimension does not repair the local
charge obstruction.  This file forms the sigma-union of all finite-dimensional
Boolean cubes.  Its one-coordinate transition graph still has the uniform parity
two-colouring.

The correct graph-theoretic replacement is then isolated.  A continuation-conflict
relation joins labels that an amplituhedron projection is forbidden to merge.  A
cell projection is precisely a proper colouring of this graph.  Consequently the
needed lower bound is not ordinary expansion: it is a superpolynomial lower bound
on the number of colours.

For calibration, the complete conflict relation has chromatic number `2^m`, because
a proper colouring is exactly an injective label map.  The local cube relation has
a two-colouring in every dimension.  The final solver bridge records the missing
statement without hiding it: SAT correctness must make the solver's polynomial
cell map a proper colouring of a conflict graph whose chromatic number exceeds the
polynomial cell budget.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameInfiniteConflictChromaticEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameLocalChargeChromaticBarrier

/-! ## The unbounded union of finite Boolean dimensions -/

/-- A point in some finite-dimensional Boolean cube.  The dimension is unbounded
over the whole type, while each point has a finite coordinate set. -/
abbrev UnboundedCubePoint := Sigma Assignment

/-- One-coordinate transitions within any finite slice. -/
inductive UnboundedCubeEdge : UnboundedCubePoint -> UnboundedCubePoint -> Prop
  | flip (m : Nat) (a : Assignment m) (i : Fin m) :
      UnboundedCubeEdge ⟨m, a⟩ ⟨m, flipAssignment a i⟩

/-- The same parity charge colours every finite slice, uniformly in dimension. -/
def unboundedCubeParity : UnboundedCubePoint -> Bool
  | ⟨m, a⟩ => parityLocalCharge (m := m) a

/-- Even after taking all finite dimensions at once, every local edge is separated
by the same two-valued charge. -/
theorem unboundedCubeParity_edgeSeparated :
    EdgeSeparated UnboundedCubeEdge unboundedCubeParity := by
  intro x y hxy
  cases hxy with
  | flip m a i =>
      change parityLocalCharge a ≠ parityLocalCharge (flipAssignment a i)
      exact (parityLocalCharge_edgeSeparated m) a (flipAssignment a i) ⟨i, rfl⟩

/-- Thus unbounded dimension still admits a two-colour local action. -/
theorem unboundedCube_local_chromatic_le_two :
    (Fintype.card Bool = 2) ∧
      EdgeSeparated UnboundedCubeEdge unboundedCubeParity :=
  ⟨by simp, unboundedCubeParity_edgeSeparated⟩

/-! ## Continuation-conflict chromatic number -/

/-- A finite cell map is a proper colouring when it separates every declared
continuation conflict. -/
abbrev ProperConflictColoring {m : Nat} {Cell : Type}
    (conflict : Assignment m -> Assignment m -> Prop)
    (cellOf : Assignment m -> Cell) : Prop :=
  EdgeSeparated conflict cellOf

/-- The conflict graph needs more than `q` colours: no carrier of cardinality at
most `q` admits a proper colouring. -/
def ChromaticAbove {m : Nat}
    (conflict : Assignment m -> Assignment m -> Prop) (q : Nat) : Prop :=
  forall (Cell : Type) [Fintype Cell] (cellOf : Assignment m -> Cell),
    Fintype.card Cell <= q -> ¬ ProperConflictColoring conflict cellOf

/-- The chromatic lower bound directly blocks any claimed small positive-cell
projection. -/
theorem no_small_projection_of_chromaticAbove
    {m q : Nat} {Cell : Type} [Fintype Cell]
    {conflict : Assignment m -> Assignment m -> Prop}
    (hchrom : ChromaticAbove conflict q)
    (cellOf : Assignment m -> Cell)
    (hcard : Fintype.card Cell <= q) :
    ¬ ProperConflictColoring conflict cellOf :=
  hchrom Cell cellOf hcard

/-! ## Calibration: local conflict versus complete conflict -/

/-- The complete fooling conflict relation joins every distinct pair. -/
def CompleteConflict {m : Nat} (a b : Assignment m) : Prop := a ≠ b

/-- Properly colouring the complete conflict graph is exactly injectivity. -/
theorem properColoring_complete_iff_injective
    {m : Nat} {Cell : Type} (cellOf : Assignment m -> Cell) :
    ProperConflictColoring (CompleteConflict (m := m)) cellOf <->
      Function.Injective cellOf := by
  constructor
  · intro h a b hab
    by_contra hne
    exact h a b hne hab
  · intro hinj a b hab hcell
    exact hab (hinj hcell)

/-- The complete conflict graph exceeds every colour budget below `2^m`. -/
theorem completeConflict_chromaticAbove
    {m q : Nat} (hgap : q < 2 ^ m) :
    ChromaticAbove (CompleteConflict (m := m)) q := by
  intro Cell _ cellOf hcard hproper
  have hinj : Function.Injective cellOf :=
    (properColoring_complete_iff_injective cellOf).mp hproper
  have hlower : 2 ^ m <= Fintype.card Cell :=
    boundary_card_ge_exp cellOf hinj
  omega

/-- By contrast, the local hypercube conflict graph never has chromatic number
above two: parity is an explicit proper two-colouring. -/
theorem localHypercube_not_chromaticAbove_two (m : Nat) :
    ¬ ChromaticAbove (HypercubeEdge (m := m)) 2 := by
  intro hchrom
  exact hchrom Bool parityLocalCharge (by simp)
    (parityLocalCharge_edgeSeparated m)

/-! ## The exact solver-to-conflict bridge -/

/-- A polynomial amplituhedron colouring whose propriety is derived from SAT
correctness, together with an independently proved chromatic lower bound for the
same solver-relevance graph. -/
structure SolverConflictChromaticBridgeFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  k : Nat
  conflict : Assignment m -> Assignment m -> Prop
  Cell : Type
  cellFintype : Fintype Cell
  cellOf : Assignment m -> Cell
  polyCells : @Fintype.card Cell cellFintype <= m ^ k
  proper_of_decides : DecidesSAT U D ->
    ProperConflictColoring conflict cellOf
  chromaticHard : ChromaticAbove conflict (m ^ k)

namespace SolverConflictChromaticBridgeFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- A bridge with a genuine superpolynomial conflict-chromatic theorem rules out
the corresponding machine. -/
theorem not_decidesSAT (B : SolverConflictChromaticBridgeFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype B.Cell := B.cellFintype
  exact B.chromaticHard B.Cell B.cellOf B.polyCells (B.proper_of_decides hD)

end SolverConflictChromaticBridgeFor

/-- Global solver-indexed conflict-chromatic bridges rule out polynomial SAT
decision. -/
theorem no_SATDecisionInP_of_conflictChromaticBridges
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverConflictChromaticBridgeFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨B⟩ := H D
  exact B.not_decidesSAT hD

end PallLean.Paper93.DeepMath.PathB.NFrameInfiniteConflictChromaticEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfiniteConflictChromaticEndpoint.unboundedCubeParity_edgeSeparated
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfiniteConflictChromaticEndpoint.properColoring_complete_iff_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfiniteConflictChromaticEndpoint.completeConflict_chromaticAbove
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfiniteConflictChromaticEndpoint.localHypercube_not_chromaticAbove_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameInfiniteConflictChromaticEndpoint.no_SATDecisionInP_of_conflictChromaticBridges
