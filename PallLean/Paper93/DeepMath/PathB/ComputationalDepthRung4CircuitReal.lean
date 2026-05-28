import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4ParityDecisionTreeCore

/-!
# Rung 4 real circuit substrate

**STATUS: REAL CIRCUIT SYNTAX AND SEMANTICS, NOT HÅSTAD OR RAZBOROV--SMOLENSKY.**

The earlier rung-4 file supplied abstract AC⁰/AC⁰[p] lower-bound interfaces and
a real parity decision-tree endpoint.  This file adds the missing formal
substrate: an actual Boolean circuit syntax with constants, variables, NOT,
unbounded AND/OR gates, and MOD gates; Boolean evaluation; depth and size; and
syntax predicates for AC⁰-style and AC⁰[p]-style circuits.

The proved theorems are deliberately modest: if a real syntactic circuit lower
bound is supplied, then no smaller/shallow circuit exists.  The famous lower
bounds themselves remain future formalization targets and are not inserted here
as hidden assumptions.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Real Boolean circuit syntax -/

/-- Boolean circuits with unbounded fan-in AND/OR and MOD gates.  The `modGate`
`modGate p r xs` outputs whether the number of true children is congruent to
`r` modulo `p`; Lean's `Nat.mod` makes the `p = 0` case total, though intended
AC⁰[p] uses positive prime moduli. -/
inductive BoolCircuitSyntax (n : Nat) : Type where
  | const : Bool -> BoolCircuitSyntax n
  | input : Fin n -> BoolCircuitSyntax n
  | not : BoolCircuitSyntax n -> BoolCircuitSyntax n
  | andGate : List (BoolCircuitSyntax n) -> BoolCircuitSyntax n
  | orGate : List (BoolCircuitSyntax n) -> BoolCircuitSyntax n
  | modGate : Nat -> Nat -> List (BoolCircuitSyntax n) -> BoolCircuitSyntax n

namespace BoolCircuitSyntax

/-- Evaluate a Boolean circuit. -/
def eval {n : Nat} : BoolCircuitSyntax n -> (Fin n -> Bool) -> Bool
  | const b, _ => b
  | input i, σ => σ i
  | not C, σ => !(eval C σ)
  | andGate Cs, σ => (Cs.map (fun C => eval C σ)).all id
  | orGate Cs, σ => (Cs.map (fun C => eval C σ)).any id
  | modGate p r Cs, σ =>
      decide (((Cs.map (fun C => eval C σ)).filter id).length % p = r % p)

/-- Circuit depth. -/
def depth {n : Nat} : BoolCircuitSyntax n -> Nat
  | const _ => 0
  | input _ => 0
  | not C => depth C + 1
  | andGate Cs => Cs.foldl (fun m C => max m (depth C)) 0 + 1
  | orGate Cs => Cs.foldl (fun m C => max m (depth C)) 0 + 1
  | modGate _ _ Cs => Cs.foldl (fun m C => max m (depth C)) 0 + 1

/-- Circuit size, counting each gate and input/constant leaf as one node. -/
def size {n : Nat} : BoolCircuitSyntax n -> Nat
  | const _ => 1
  | input _ => 1
  | not C => size C + 1
  | andGate Cs => Cs.foldl (fun s C => s + size C) 0 + 1
  | orGate Cs => Cs.foldl (fun s C => s + size C) 0 + 1
  | modGate _ _ Cs => Cs.foldl (fun s C => s + size C) 0 + 1

/-- A circuit computes a Boolean function. -/
def Computes {n : Nat} (C : BoolCircuitSyntax n) (F : BoolFunction n) : Prop :=
  forall σ : Fin n -> Bool, C.eval σ = F σ

/-- AC⁰-style syntax predicate: constants, inputs, NOT, AND, OR; no MOD gates.
Depth/size bounds are supplied separately by the lower-bound interfaces. -/
def IsAC0Syntax {n : Nat} : BoolCircuitSyntax n -> Prop
  | const _ => True
  | input _ => True
  | not C => IsAC0Syntax C
  | andGate Cs => forall C, C ∈ Cs -> IsAC0Syntax C
  | orGate Cs => forall C, C ∈ Cs -> IsAC0Syntax C
  | modGate _ _ _ => False

/-- AC⁰[p]-style syntax predicate: Boolean gates plus MOD gates of the fixed
modulus `p`. -/
def IsAC0pSyntax {n : Nat} (p : Nat) : BoolCircuitSyntax n -> Prop
  | const _ => True
  | input _ => True
  | not C => IsAC0pSyntax p C
  | andGate Cs => forall C, C ∈ Cs -> IsAC0pSyntax p C
  | orGate Cs => forall C, C ∈ Cs -> IsAC0pSyntax p C
  | modGate q _ Cs => q = p /\ forall C, C ∈ Cs -> IsAC0pSyntax p C

@[simp] theorem size_const {n : Nat} (b : Bool) :
    (const (n := n) b).size = 1 := by simp [size]

@[simp] theorem size_input {n : Nat} (i : Fin n) :
    (input i).size = 1 := by simp [size]

@[simp] theorem depth_const {n : Nat} (b : Bool) :
    (const (n := n) b).depth = 0 := by simp [depth]

@[simp] theorem depth_input {n : Nat} (i : Fin n) :
    (input i).depth = 0 := by simp [depth]

/-- Every syntactic circuit has positive size. -/
theorem size_pos {n : Nat} (C : BoolCircuitSyntax n) : 0 < C.size := by
  cases C <;> simp [size]

end BoolCircuitSyntax

/-! ## Real circuit lower-bound interfaces -/

/-- A pointwise lower bound for real AC⁰ syntactic circuits. -/
def RealAC0SizeLowerBoundAt
    (F : (n : Nat) -> BoolFunction n) (n d lower : Nat) : Prop :=
  forall C : BoolCircuitSyntax n,
    C.IsAC0Syntax -> C.Computes (F n) -> C.depth <= d -> lower <= C.size

/-- A pointwise lower bound for real AC⁰[p] syntactic circuits. -/
def RealAC0pSizeLowerBoundAt
    (p : Nat) (F : (n : Nat) -> BoolFunction n) (n d lower : Nat) : Prop :=
  forall C : BoolCircuitSyntax n,
    C.IsAC0pSyntax p -> C.Computes (F n) -> C.depth <= d -> lower <= C.size

/-- Real AC⁰ lower bounds rule out smaller real AC⁰ circuits. -/
theorem no_small_realAC0Circuit_of_size_lower_bound
    {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat}
    (H : RealAC0SizeLowerBoundAt F n d lower)
    (hgap : s < lower) :
    Not (exists C : BoolCircuitSyntax n,
      C.IsAC0Syntax /\ C.Computes (F n) /\ C.depth <= d /\ C.size <= s) := by
  rintro ⟨C, hsyntax, hcomp, hdepth, hsize⟩
  have hlower : lower <= C.size := H C hsyntax hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-- Real AC⁰[p] lower bounds rule out smaller real AC⁰[p] circuits. -/
theorem no_small_realAC0pCircuit_of_size_lower_bound
    {p : Nat} {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat}
    (H : RealAC0pSizeLowerBoundAt p F n d lower)
    (hgap : s < lower) :
    Not (exists C : BoolCircuitSyntax n,
      C.IsAC0pSyntax p /\ C.Computes (F n) /\ C.depth <= d /\ C.size <= s) := by
  rintro ⟨C, hsyntax, hcomp, hdepth, hsize⟩
  have hlower : lower <= C.size := H C hsyntax hcomp hdepth
  exact Nat.not_lt_of_ge (Nat.le_trans hlower hsize) hgap

/-- Real AC⁰ lower bounds for parity, as an interface for Håstad-style future
formalization. -/
abbrev RealAC0ParitySizeLowerBoundAt (n d lower : Nat) : Prop :=
  RealAC0SizeLowerBoundAt parityFunction n d lower

/-- Real AC⁰[p] lower bounds for parity, as an interface for
Razborov--Smolensky-style future formalization. -/
abbrev RealAC0pParitySizeLowerBoundAt (p n d lower : Nat) : Prop :=
  RealAC0pSizeLowerBoundAt p parityFunction n d lower

/-- A real AC⁰ parity lower bound rules out smaller real AC⁰ parity circuits. -/
theorem no_small_realAC0_parity_circuit_of_lower_bound
    {n d lower s : Nat}
    (H : RealAC0ParitySizeLowerBoundAt n d lower)
    (hgap : s < lower) :
    Not (exists C : BoolCircuitSyntax n,
      C.IsAC0Syntax /\ C.Computes (parityFunction n) /\
      C.depth <= d /\ C.size <= s) :=
  no_small_realAC0Circuit_of_size_lower_bound H hgap

/-- A real AC⁰[p] parity lower bound rules out smaller real AC⁰[p] parity circuits. -/
theorem no_small_realAC0p_parity_circuit_of_lower_bound
    {p n d lower s : Nat}
    (H : RealAC0pParitySizeLowerBoundAt p n d lower)
    (hgap : s < lower) :
    Not (exists C : BoolCircuitSyntax n,
      C.IsAC0pSyntax p /\ C.Computes (parityFunction n) /\
      C.depth <= d /\ C.size <= s) :=
  no_small_realAC0pCircuit_of_size_lower_bound H hgap

/-! ## Honest rung-4 formal-substrate bundle -/

/-- The real syntactic substrates now present at rung 4.  The decision-tree core
is included as the checked endpoint for the switching-lemma route. -/
structure Rung4FormalSubstrates : Prop where
  real_ac0_pointwise_size :
    forall {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat},
      RealAC0SizeLowerBoundAt F n d lower ->
      s < lower ->
      Not (exists C : BoolCircuitSyntax n,
        C.IsAC0Syntax /\ C.Computes (F n) /\ C.depth <= d /\ C.size <= s)
  real_ac0p_pointwise_size :
    forall {p : Nat} {F : (n : Nat) -> BoolFunction n} {n d lower s : Nat},
      RealAC0pSizeLowerBoundAt p F n d lower ->
      s < lower ->
      Not (exists C : BoolCircuitSyntax n,
        C.IsAC0pSyntax p /\ C.Computes (F n) /\ C.depth <= d /\ C.size <= s)
  real_ac0_parity :
    forall {n d lower s : Nat},
      RealAC0ParitySizeLowerBoundAt n d lower ->
      s < lower ->
      Not (exists C : BoolCircuitSyntax n,
        C.IsAC0Syntax /\ C.Computes (parityFunction n) /\
        C.depth <= d /\ C.size <= s)
  real_ac0p_parity :
    forall {p n d lower s : Nat},
      RealAC0pParitySizeLowerBoundAt p n d lower ->
      s < lower ->
      Not (exists C : BoolCircuitSyntax n,
        C.IsAC0pSyntax p /\ C.Computes (parityFunction n) /\
        C.depth <= d /\ C.size <= s)
  parity_decision_tree_core :
    forall {n : Nat} (T : BoolDecisionTree n),
      T.Computes (parityFunction n) -> n <= T.depth

/-- Rung 4 is complete at the formal-substrate level: the repo has real circuit
syntax/semantics for AC⁰ and AC⁰[p], real lower-bound consequence theorems for
those syntactic circuits, and the real parity decision-tree endpoint. -/
theorem rung4_formal_substrates : Rung4FormalSubstrates where
  real_ac0_pointwise_size := by
    intro F n d lower s H hgap
    exact no_small_realAC0Circuit_of_size_lower_bound H hgap
  real_ac0p_pointwise_size := by
    intro p F n d lower s H hgap
    exact no_small_realAC0pCircuit_of_size_lower_bound H hgap
  real_ac0_parity := by
    intro n d lower s H hgap
    exact no_small_realAC0_parity_circuit_of_lower_bound H hgap
  real_ac0p_parity := by
    intro p n d lower s H hgap
    exact no_small_realAC0p_parity_circuit_of_lower_bound H hgap
  parity_decision_tree_core := by
    intro n T hcomputes
    exact BoolDecisionTree.depth_ge_of_computes_parity T hcomputes

/-! ## Kernel-only trace -/

#print axioms BoolCircuitSyntax.size_pos
#print axioms no_small_realAC0Circuit_of_size_lower_bound
#print axioms no_small_realAC0pCircuit_of_size_lower_bound
#print axioms no_small_realAC0_parity_circuit_of_lower_bound
#print axioms no_small_realAC0p_parity_circuit_of_lower_bound
#print axioms rung4_formal_substrates

end PallLean.Paper93.DeepMath.PathB
