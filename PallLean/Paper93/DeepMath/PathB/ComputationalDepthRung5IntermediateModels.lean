import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal

/-!
# Rung 5: intermediate models between AC⁰-style circuits and general P

**STATUS: FORMAL SUBSTRATES / FRONTIER MARKER, NOT LOWER-BOUND BREAKTHROUGH.**

Rung 5 is where the ladder reaches models such as TC⁰, NC¹/formulas,
branching programs, and bounded-space computation.  This is exactly where known
techniques thin out: strong explicit lower bounds for TC⁰ are largely open, and
Barrington's theorem shows that width-5 branching programs already capture NC¹.

This file therefore does the honest thing: it formalizes real substrates for
the main intermediate models and proves only the generic lower-bound consequences.
It does not assert Håstad/Razborov/Smolensky-style miracles at this rung, and it
certainly does not bridge to general P.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## TC⁰-style threshold circuits -/

/-- Boolean circuits with threshold gates.  `threshold k Cs` is true when at
least `k` children evaluate to true. -/
inductive ThresholdCircuitSyntax (n : Nat) : Type where
  | const : Bool -> ThresholdCircuitSyntax n
  | input : Fin n -> ThresholdCircuitSyntax n
  | not : ThresholdCircuitSyntax n -> ThresholdCircuitSyntax n
  | andGate : List (ThresholdCircuitSyntax n) -> ThresholdCircuitSyntax n
  | orGate : List (ThresholdCircuitSyntax n) -> ThresholdCircuitSyntax n
  | threshold : Nat -> List (ThresholdCircuitSyntax n) -> ThresholdCircuitSyntax n

namespace ThresholdCircuitSyntax

/-- Evaluate a threshold circuit. -/
def eval {n : Nat} : ThresholdCircuitSyntax n -> (Fin n -> Bool) -> Bool
  | const b, _ => b
  | input i, σ => σ i
  | not C, σ => !(eval C σ)
  | andGate Cs, σ => (Cs.map (fun C => eval C σ)).all id
  | orGate Cs, σ => (Cs.map (fun C => eval C σ)).any id
  | threshold k Cs, σ => decide (k <= ((Cs.map (fun C => eval C σ)).filter id).length)

/-- Threshold circuit depth. -/
def depth {n : Nat} : ThresholdCircuitSyntax n -> Nat
  | const _ => 0
  | input _ => 0
  | not C => depth C + 1
  | andGate Cs => Cs.foldl (fun m C => max m (depth C)) 0 + 1
  | orGate Cs => Cs.foldl (fun m C => max m (depth C)) 0 + 1
  | threshold _ Cs => Cs.foldl (fun m C => max m (depth C)) 0 + 1

/-- Threshold circuit size. -/
def size {n : Nat} : ThresholdCircuitSyntax n -> Nat
  | const _ => 1
  | input _ => 1
  | not C => size C + 1
  | andGate Cs => Cs.foldl (fun s C => s + size C) 0 + 1
  | orGate Cs => Cs.foldl (fun s C => s + size C) 0 + 1
  | threshold _ Cs => Cs.foldl (fun s C => s + size C) 0 + 1

/-- A threshold circuit computes a Boolean function. -/
def Computes {n : Nat} (C : ThresholdCircuitSyntax n) (F : BoolFunction n) : Prop :=
  forall σ : Fin n -> Bool, C.eval σ = F σ

/-- Every threshold circuit has positive size. -/
theorem size_pos {n : Nat} (C : ThresholdCircuitSyntax n) : 0 < C.size := by
  cases C <;> simp [size]

end ThresholdCircuitSyntax

/-- Pointwise TC⁰-style size lower bound for real threshold circuits. -/
def TC0SizeLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n d lower : Nat) : Prop :=
  forall C : ThresholdCircuitSyntax n,
    C.Computes (F n) -> C.depth <= d -> lower <= C.size

/-- A TC⁰-style lower bound rules out smaller threshold circuits. -/
theorem no_small_TC0Circuit_of_size_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat}
    (H : TC0SizeLowerBoundAt F n d lower)
    (hgap : s < lower) :
    Not (exists C : ThresholdCircuitSyntax n,
      C.Computes (F n) /\ C.depth <= d /\ C.size <= s) := by
  rintro ⟨C, hcomp, hdepth, hsize⟩
  have hlower : lower <= C.size := H C hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-! ## NC¹-style formulas -/

/-- A propositional formula computes a Boolean function. -/
def PropFormula.Computes {n : Nat} (A : PropFormula n) (F : BoolFunction n) : Prop :=
  forall σ : Fin n -> Bool, A.eval σ = F σ

/-- Pointwise NC¹/formula size lower bound for real propositional formulas. -/
def NC1FormulaSizeLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n depthBound lower : Nat) : Prop :=
  forall A : PropFormula n,
    A.Computes (F n) -> A.depth <= depthBound -> lower <= A.size

/-- A formula lower bound rules out smaller formulas at the depth bound. -/
theorem no_small_NC1Formula_of_size_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n depthBound lower s : Nat}
    (H : NC1FormulaSizeLowerBoundAt F n depthBound lower)
    (hgap : s < lower) :
    Not (exists A : PropFormula n,
      A.Computes (F n) /\ A.depth <= depthBound /\ A.size <= s) := by
  rintro ⟨A, hcomp, hdepth, hsize⟩
  have hlower : lower <= A.size := H A hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-! ## Branching programs -/

/-- One layer of a deterministic branching program of fixed width.  The next
state may inspect the whole input; read-once/read-k restrictions can be added as
future refinements. -/
structure BranchingProgramLayer (n width : Nat) where
  next : Fin width -> (Fin n -> Bool) -> Fin width

/-- A deterministic branching program with `length = layers.length` and width
carried by the state type `Fin width`. -/
structure BranchingProgram (n width : Nat) where
  layers : List (BranchingProgramLayer n width)
  start : Fin width
  accept : Finset (Fin width)

namespace BranchingProgram

/-- Run a list of branching-program layers from an initial state. -/
def runLayers {n width : Nat} (σ : Fin n -> Bool) :
    List (BranchingProgramLayer n width) -> Fin width -> Fin width
  | [], q => q
  | L :: Ls, q => runLayers σ Ls (L.next q σ)

/-- Final state of a branching program. -/
def finalState {n width : Nat} (P : BranchingProgram n width)
    (σ : Fin n -> Bool) : Fin width :=
  runLayers σ P.layers P.start

/-- Evaluate a branching program. -/
def eval {n width : Nat} (P : BranchingProgram n width)
    (σ : Fin n -> Bool) : Bool :=
  decide (P.finalState σ ∈ P.accept)

/-- Number of layers. -/
def length {n width : Nat} (P : BranchingProgram n width) : Nat :=
  P.layers.length

/-- A simple node-count measure: width times number of layers. -/
def size {n width : Nat} (P : BranchingProgram n width) : Nat :=
  width * P.length

/-- A branching program computes a Boolean function. -/
def Computes {n width : Nat} (P : BranchingProgram n width) (F : BoolFunction n) : Prop :=
  forall σ : Fin n -> Bool, P.eval σ = F σ

end BranchingProgram

/-- Pointwise length lower bound for branching programs of a fixed width. -/
def BranchingProgramLengthLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n width lower : Nat) : Prop :=
  forall P : BranchingProgram n width,
    P.Computes (F n) -> lower <= P.length

/-- A branching-program length lower bound rules out shorter programs. -/
theorem no_short_branchingProgram_of_length_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n width lower len : Nat}
    (H : BranchingProgramLengthLowerBoundAt F n width lower)
    (hgap : len < lower) :
    Not (exists P : BranchingProgram n width,
      P.Computes (F n) /\ P.length <= len) := by
  rintro ⟨P, hcomp, hlen⟩
  have hlower : lower <= P.length := H P hcomp
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hlen) hgap


/-! ## Bounded-space configuration systems -/

/-- A finite-configuration, input-dependent deterministic machine skeleton.  This
is the bounded-space substrate: a space bound gives a bound on the number of
reachable configurations.  We keep the model finite and explicit rather than
claiming a full Turing-machine space hierarchy theorem. -/
structure SpaceBoundedMachine (n configs : Nat) where
  transition : Fin configs -> (Fin n -> Bool) -> Fin configs
  start : Fin configs
  accept : Finset (Fin configs)
  time : Nat

namespace SpaceBoundedMachine

/-- Run a finite-configuration machine for a fixed number of steps. -/
def runSteps {n configs : Nat} (M : SpaceBoundedMachine n configs)
    (σ : Fin n -> Bool) : Nat -> Fin configs -> Fin configs
  | 0, q => q
  | t + 1, q => runSteps M σ t (M.transition q σ)

/-- Final state after the machine's time budget. -/
def finalState {n configs : Nat} (M : SpaceBoundedMachine n configs)
    (σ : Fin n -> Bool) : Fin configs :=
  M.runSteps σ M.time M.start

/-- Boolean acceptance by a finite-configuration machine. -/
def eval {n configs : Nat} (M : SpaceBoundedMachine n configs)
    (σ : Fin n -> Bool) : Bool :=
  decide (M.finalState σ ∈ M.accept)

/-- A finite-configuration machine computes a Boolean function. -/
def Computes {n configs : Nat} (M : SpaceBoundedMachine n configs)
    (F : BoolFunction n) : Prop :=
  forall σ : Fin n -> Bool, M.eval σ = F σ

end SpaceBoundedMachine

/-- Pointwise lower bound on the number of configurations needed by a bounded-
space machine computing a function.  Converting this to bits is logarithmic and
left to arithmetic refinements; the formal load-bearing object is the finite
configuration count. -/
def SpaceBoundedConfigLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n lowerConfigs : Nat) : Prop :=
  forall configs : Nat, forall M : SpaceBoundedMachine n configs,
    M.Computes (F n) -> lowerConfigs <= configs

/-- A configuration-count lower bound rules out smaller bounded-space machines. -/
theorem no_small_spaceBoundedMachine_of_config_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n lowerConfigs configBudget : Nat}
    (H : SpaceBoundedConfigLowerBoundAt F n lowerConfigs)
    (hgap : configBudget < lowerConfigs) :
    Not (exists configs : Nat, exists M : SpaceBoundedMachine n configs,
      M.Computes (F n) /\ configs <= configBudget) := by
  rintro ⟨configs, M, hcomp, hcfg⟩
  have hlower : lowerConfigs <= configs := H configs M hcomp
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hcfg) hgap

/-! ## Barrington-style NC¹ to width-5 branching-program interface -/

/-- A Barrington-style simulation interface for one function/length/depth budget.
The real Barrington theorem is a deep external result; this structure records
exactly what such a theorem supplies without pretending to prove it here. -/
structure BarringtonWidth5SimulationAt
    (F : (n : Nat) -> BoolFunction n) (n depthBound lengthBound : Nat) : Prop where
  simulate :
    forall A : PropFormula n,
      A.Computes (F n) ->
      A.depth <= depthBound ->
      exists P : BranchingProgram n 5,
        P.Computes (F n) /\ P.length <= lengthBound

/-- If a Barrington simulation is available and width-5 branching programs need
more than `lengthBound` layers, then no formula of the simulated depth computes
the function.  This is a checked conservation theorem, not a proof of
Barrington's theorem or of the branching-program lower bound. -/
theorem no_NC1Formula_of_barrington_and_bp_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n depthBound lengthBound lower : Nat}
    (B : BarringtonWidth5SimulationAt F n depthBound lengthBound)
    (Hbp : BranchingProgramLengthLowerBoundAt F n 5 lower)
    (hgap : lengthBound < lower) :
    Not (exists A : PropFormula n,
      A.Computes (F n) /\ A.depth <= depthBound) := by
  rintro ⟨A, hcomp, hdepth⟩
  rcases B.simulate A hcomp hdepth with ⟨P, hPcomp, hPlen⟩
  have hlower : lower <= P.length := Hbp P hPcomp
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hPlen) hgap

/-! ## Rung-5 frontier bundle -/

/-- Rung 5 formal substrates present in this repository.  The bundle is useful
because it pins down exactly what future TC⁰/NC¹/branching-program lower bounds
would have to target, while not pretending those hard lower bounds are already
proved. -/
structure Rung5FormalSubstrates : Prop where
  tc0_size :
    forall {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat},
      TC0SizeLowerBoundAt F n d lower ->
      s < lower ->
      Not (exists C : ThresholdCircuitSyntax n,
        C.Computes (F n) /\ C.depth <= d /\ C.size <= s)
  nc1_formula_size :
    forall {F : (n : Nat) -> BoolFunction n} {n depthBound lower s : Nat},
      NC1FormulaSizeLowerBoundAt F n depthBound lower ->
      s < lower ->
      Not (exists A : PropFormula n,
        A.Computes (F n) /\ A.depth <= depthBound /\ A.size <= s)
  branching_program_length :
    forall {F : (n : Nat) -> BoolFunction n} {n width lower len : Nat},
      BranchingProgramLengthLowerBoundAt F n width lower ->
      len < lower ->
      Not (exists P : BranchingProgram n width,
        P.Computes (F n) /\ P.length <= len)
  bounded_space_configs :
    forall {F : (n : Nat) -> BoolFunction n} {n lowerConfigs configBudget : Nat},
      SpaceBoundedConfigLowerBoundAt F n lowerConfigs ->
      configBudget < lowerConfigs ->
      Not (exists configs : Nat, exists M : SpaceBoundedMachine n configs,
        M.Computes (F n) /\ configs <= configBudget)
  barrington_transfer :
    forall {F : (n : Nat) -> BoolFunction n} {n depthBound lengthBound lower : Nat},
      BarringtonWidth5SimulationAt F n depthBound lengthBound ->
      BranchingProgramLengthLowerBoundAt F n 5 lower ->
      lengthBound < lower ->
      Not (exists A : PropFormula n,
        A.Computes (F n) /\ A.depth <= depthBound)

/-- Rung 5 is complete at the formal-substrate/frontier-marker level: TC⁰-style
threshold circuits, NC¹-style formulas, deterministic branching programs,
bounded-space finite-configuration machines, and a Barrington-style interface now
have real syntax/semantics and checked lower-bound consequence theorems. -/
theorem rung5_formal_substrates : Rung5FormalSubstrates where
  tc0_size := by
    intro F n d lower s H hgap
    exact no_small_TC0Circuit_of_size_lower_bound H hgap
  nc1_formula_size := by
    intro F n depthBound lower s H hgap
    exact no_small_NC1Formula_of_size_lower_bound H hgap
  branching_program_length := by
    intro F n width lower len H hgap
    exact no_short_branchingProgram_of_length_lower_bound H hgap
  bounded_space_configs := by
    intro F n lowerConfigs configBudget H hgap
    exact no_small_spaceBoundedMachine_of_config_lower_bound H hgap
  barrington_transfer := by
    intro F n depthBound lengthBound lower B Hbp hgap
    exact no_NC1Formula_of_barrington_and_bp_lower_bound B Hbp hgap

/-! ## Kernel-only trace -/

#print axioms ThresholdCircuitSyntax.size_pos
#print axioms no_small_TC0Circuit_of_size_lower_bound
#print axioms no_small_NC1Formula_of_size_lower_bound
#print axioms no_short_branchingProgram_of_length_lower_bound
#print axioms no_small_spaceBoundedMachine_of_config_lower_bound
#print axioms no_NC1Formula_of_barrington_and_bp_lower_bound
#print axioms rung5_formal_substrates

end PallLean.Paper93.DeepMath.PathB
