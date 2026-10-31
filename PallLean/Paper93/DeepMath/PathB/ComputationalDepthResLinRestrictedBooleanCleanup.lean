import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinRestrictedDAG
import Mathlib.Tactic

/-!
# Constant-cost cleanup of restricted Boolean sources

Whole-dag restriction turns a Boolean source into either the original Boolean axiom (when its
variable is free) or the constant tautology `(0 = 0) ∨ (0 = 1)` (when it is fixed).  This file
proves that dichotomy syntactically and derives the constant tautology inside ordinary `Res(⊕)`.

The derivation is uniform: from `(x = 0) ∨ (x = 1)`, resolve each equation with itself to introduce
`0 = 0`, resolve the two resulting lines to introduce `0 = 1`, and simplify that false disjunct.
Thus restricted Boolean sources do not enlarge the proof system; they have a constant-cost cleanup
macro.  Reindexing those macros into a shared dag is the subsequent bookkeeping layer.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical

/-- The equation `xᵢ = b`. -/
def unitEquation (n : ℕ) (i : Fin n) (b : ZMod 2) : Equation n where
  coeff j := if j = i then 1 else 0
  rhs := b

/-- The always-true equation `0 = 0`. -/
def trueConstant (n : ℕ) : Equation n := falseConstant n 0

theorem booleanAxiom_eq_unitEquations (n : ℕ) (i : Fin n) :
    booleanAxiom n i = {unitEquation n i 0, unitEquation n i 1} := by
  rfl

theorem unitEquation_add_self (n : ℕ) (i : Fin n) (b : ZMod 2) :
    (unitEquation n i b).add (unitEquation n i b) = trueConstant n := by
  apply Equation.ext
  · intro j
    by_cases h : j = i
    · simp [Equation.add, unitEquation, trueConstant, falseConstant, h]
      decide
    · simp [Equation.add, unitEquation, trueConstant, falseConstant, h]
  · change b + b = 0
    exact (by decide : ∀ z : ZMod 2, z + z = 0) b

theorem unitEquation_zero_add_one (n : ℕ) (i : Fin n) :
    (unitEquation n i 0).add (unitEquation n i 1) = falseConstant n 1 := by
  apply Equation.ext
  · intro j
    by_cases h : j = i
    · simp [Equation.add, unitEquation, falseConstant, h]
      decide
    · simp [Equation.add, unitEquation, falseConstant, h]
  · simp [Equation.add, unitEquation, falseConstant]

theorem unitEquation_one_add_zero (n : ℕ) (i : Fin n) :
    (unitEquation n i 1).add (unitEquation n i 0) = falseConstant n 1 := by
  apply Equation.ext
  · intro j
    by_cases h : j = i
    · simp [Equation.add, unitEquation, falseConstant, h]
      decide
    · simp [Equation.add, unitEquation, falseConstant, h]
  · simp [Equation.add, unitEquation, falseConstant]

/-- Restricting a unit equation at its assigned variable produces a constant equation. -/
theorem restrictEq_unitEquation_of_assigned {n : ℕ} (ρ : Restriction n)
    (i : Fin n) (b v : ZMod 2) (hi : ρ i = some v) :
    restrictEq ρ (unitEquation n i b) = falseConstant n (b - v) := by
  have hpart : assignedPart ρ (unitEquation n i b) = v := by
    unfold assignedPart
    rw [Finset.sum_eq_single i]
    · simp [assignedContribution, unitEquation, hi]
    · intro j _ hji
      cases hj : ρ j <;> simp [assignedContribution, unitEquation, hji, hj]
    · simp
  apply Equation.ext
  · intro j
    by_cases hji : j = i
    · subst j
      simp [restrictEq, falseConstant, hi]
    · cases hj : ρ j <;> simp [restrictEq, unitEquation, falseConstant, hji, hj]
  · change b - assignedPart ρ (unitEquation n i b) = b - v
    rw [hpart]

/-- A unit equation is unchanged when its only supported variable is free. -/
theorem restrictEq_unitEquation_of_unassigned {n : ℕ} (ρ : Restriction n)
    (i : Fin n) (b : ZMod 2) (hi : ρ i = none) :
    restrictEq ρ (unitEquation n i b) = unitEquation n i b := by
  have hpart : assignedPart ρ (unitEquation n i b) = 0 := by
    unfold assignedPart
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · subst j
      simp [assignedContribution, hi]
    · cases hj : ρ j <;> simp [assignedContribution, unitEquation, hji, hj]
  apply Equation.ext
  · intro j
    by_cases hji : j = i
    · subst j
      simp [restrictEq, unitEquation, hi]
    · cases hj : ρ j <;> simp [restrictEq, unitEquation, hji, hj]
  · change b - assignedPart ρ (unitEquation n i b) = b
    rw [hpart, sub_zero]

/-- A free variable's restricted Boolean source remains the canonical Boolean axiom. -/
theorem restrictClause_booleanAxiom_of_unassigned {n : ℕ} (ρ : Restriction n)
    (i : Fin n) (hi : ρ i = none) :
    restrictClause ρ (booleanAxiom n i) = booleanAxiom n i := by
  simp [booleanAxiom_eq_unitEquations, restrictClause,
    restrictEq_unitEquation_of_unassigned ρ i 0 hi,
    restrictEq_unitEquation_of_unassigned ρ i 1 hi]

/-- A fixed variable's restricted Boolean source is exactly `(0 = 0) ∨ (0 = 1)`. -/
theorem restrictClause_booleanAxiom_of_assigned {n : ℕ} (ρ : Restriction n)
    (i : Fin n) (v : ZMod 2) (hi : ρ i = some v) :
    restrictClause ρ (booleanAxiom n i) = {trueConstant n, falseConstant n 1} := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) v with rfl | rfl
  · simp [booleanAxiom_eq_unitEquations, restrictClause,
      restrictEq_unitEquation_of_assigned ρ i 0 0 hi,
      restrictEq_unitEquation_of_assigned ρ i 1 0 hi, trueConstant]
  · simp [booleanAxiom_eq_unitEquations, restrictClause,
      restrictEq_unitEquation_of_assigned ρ i 0 1 hi,
      restrictEq_unitEquation_of_assigned ρ i 1 1 hi, trueConstant,
      Finset.pair_comm]

/-- The constant tautology has an ordinary `Res(⊕)` derivation from a Boolean axiom.  The proof
uses four resolution/simplification inferences after the shared Boolean source. -/
theorem constantTautology_derivable {n : ℕ} (Γ : Finset (Clause n)) (i : Fin n) :
    Derivation Γ ({trueConstant n, falseConstant n 1} : Clause n) := by
  let e0 := unitEquation n i 0
  let e1 := unitEquation n i 1
  have hB : Derivation Γ ({e0, e1} : Clause n) := by
    simpa [e0, e1, booleanAxiom_eq_unitEquations] using (Derivation.boolean (Γ := Γ) i)
  have hB' : Derivation Γ ({e1, e0} : Clause n) := by
    simpa [Finset.pair_comm] using hB
  have h0 : Derivation Γ ({trueConstant n, e1} : Clause n) := by
    have h := Derivation.linearResolve (C := {e1}) (D := {e1})
      (e := e0) (f := e0) hB hB
    simpa [e0, unitEquation_add_self, Finset.pair_comm] using h
  have h1 : Derivation Γ ({trueConstant n, e0} : Clause n) := by
    have h := Derivation.linearResolve (C := {e0}) (D := {e0})
      (e := e1) (f := e1) hB' hB'
    simpa [e1, unitEquation_add_self, Finset.pair_comm] using h
  have h0' : Derivation Γ ({e1, trueConstant n} : Clause n) := by
    simpa [Finset.pair_comm] using h0
  have h1' : Derivation Γ ({e0, trueConstant n} : Clause n) := by
    simpa [Finset.pair_comm] using h1
  have hfalse : Derivation Γ
      (insert (falseConstant n 1) ({trueConstant n} : Clause n)) := by
    have h := Derivation.linearResolve (C := {trueConstant n}) (D := {trueConstant n})
      (e := e1) (f := e0) h0' h1'
    simpa [e0, e1, unitEquation_one_add_zero, Finset.pair_comm] using h
  have htrue : Derivation Γ ({trueConstant n} : Clause n) :=
    Derivation.simplify (by decide : (1 : ZMod 2) ≠ 0) hfalse
  simpa [Finset.pair_comm] using Derivation.weaken htrue (falseConstant n 1)

/-- Every restricted Boolean source is derivable in the original proof system. -/
theorem restricted_booleanAxiom_derivable {n : ℕ} (Γ : Finset (Clause n))
    (ρ : Restriction n) (i : Fin n) :
    Derivation Γ (restrictClause ρ (booleanAxiom n i)) := by
  cases hi : ρ i with
  | none =>
      rw [restrictClause_booleanAxiom_of_unassigned ρ i hi]
      exact Derivation.boolean i
  | some v =>
      rw [restrictClause_booleanAxiom_of_assigned ρ i v hi]
      exact constantTautology_derivable Γ i

/-! ## Explicit checked-dag cost -/

/-- A checked dag deriving an arbitrary final line, rather than specifically the empty line. -/
structure DAGDerivation (n : ℕ) (Γ : Finset (Clause n)) (final : Clause n) where
  steps : List (DAGStep n)
  level : ℕ → ℕ
  nonempty : steps ≠ []
  valid : ∀ i, i < steps.length → ValidAt Γ steps level i
  final_line : (steps.getLast nonempty).line = final

namespace DAGDerivation

def size {n : ℕ} {Γ : Finset (Clause n)} {C : Clause n}
    (P : DAGDerivation n Γ C) : ℕ := P.steps.length

def depth {n : ℕ} {Γ : Finset (Clause n)} {C : Clause n}
    (P : DAGDerivation n Γ C) : ℕ := P.level (P.steps.length - 1) + 1

end DAGDerivation

/-- The six stored lines of the fixed-variable cleanup macro. -/
def fixedBooleanCleanupSteps (n : ℕ) (i : Fin n) : List (DAGStep n) :=
  let e0 := unitEquation n i 0
  let e1 := unitEquation n i 1
  [ ⟨{e0, e1}, .boolean i⟩,
    ⟨{trueConstant n, e1}, .linearResolve 0 0 e0 e0⟩,
    ⟨{trueConstant n, e0}, .linearResolve 0 0 e1 e1⟩,
    ⟨{falseConstant n 1, trueConstant n}, .linearResolve 1 2 e1 e0⟩,
    ⟨{trueConstant n}, .simplify 3 1⟩,
    ⟨{trueConstant n, falseConstant n 1}, .weaken 4 (falseConstant n 1)⟩ ]

/-- Exact dependency levels of the cleanup macro. -/
def fixedBooleanCleanupLevel : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | _ => 0

/-- The constant-tautology cleanup is a checked six-line dag of depth five. -/
def fixedBooleanCleanupDAG {n : ℕ} (Γ : Finset (Clause n)) (i : Fin n) :
    DAGDerivation n Γ ({trueConstant n, falseConstant n 1} : Clause n) where
  steps := fixedBooleanCleanupSteps n i
  level := fixedBooleanCleanupLevel
  nonempty := by simp [fixedBooleanCleanupSteps]
  valid := by
    intro k hk
    have hk' : k < 6 := by simpa [fixedBooleanCleanupSteps] using hk
    interval_cases k
    · simp [fixedBooleanCleanupSteps, fixedBooleanCleanupLevel, ValidAt,
        booleanAxiom_eq_unitEquations]
    · simp [fixedBooleanCleanupSteps, fixedBooleanCleanupLevel, ValidAt, lineAt,
        unitEquation_add_self]
      refine ⟨{unitEquation n i 1}, by simp [Finset.pair_comm],
        {unitEquation n i 1}, by simp [Finset.pair_comm], ?_⟩
      simp [Finset.pair_comm]
    · simp [fixedBooleanCleanupSteps, fixedBooleanCleanupLevel, ValidAt, lineAt,
        unitEquation_add_self]
      refine ⟨{unitEquation n i 0}, by simp [Finset.pair_comm],
        {unitEquation n i 0}, by simp [Finset.pair_comm], ?_⟩
      simp [Finset.pair_comm]
    · simp [fixedBooleanCleanupSteps, fixedBooleanCleanupLevel, ValidAt, lineAt,
        unitEquation_one_add_zero]
      refine ⟨{trueConstant n}, by simp [Finset.pair_comm],
        {trueConstant n}, by simp [Finset.pair_comm], ?_⟩
      simp [Finset.pair_comm]
    · simp [fixedBooleanCleanupSteps, fixedBooleanCleanupLevel, ValidAt, lineAt]
    · simp [fixedBooleanCleanupSteps, fixedBooleanCleanupLevel, ValidAt, lineAt,
        Finset.pair_comm]
  final_line := by simp [fixedBooleanCleanupSteps]

theorem fixedBooleanCleanupDAG_size {n : ℕ} (Γ : Finset (Clause n)) (i : Fin n) :
    (fixedBooleanCleanupDAG Γ i).size = 6 := by
  rfl

theorem fixedBooleanCleanupDAG_depth {n : ℕ} (Γ : Finset (Clause n)) (i : Fin n) :
    (fixedBooleanCleanupDAG Γ i).depth = 5 := by
  rfl

/-- Number of Boolean-source lines whose variable is fixed by the restriction. -/
def assignedBooleanSourceCount {n : ℕ} {Γ : Finset (Clause n)}
    (ρ : Restriction n) (P : DAGRefutation n Γ) : ℕ :=
  P.steps.countP fun s =>
    match s.why with
    | .boolean i => (ρ i).isSome
    | _ => false

theorem assignedBooleanSourceCount_le_size {n : ℕ} {Γ : Finset (Clause n)}
    (ρ : Restriction n) (P : DAGRefutation n Γ) :
    assignedBooleanSourceCount ρ P ≤ P.size := by
  exact List.countP_le_length

/-- Exact line budget for replacing each affected one-line source by its six-line cleanup macro:
the original line is replaced, so the net cost is five lines per affected source. -/
def booleanCleanupSizeBudget {n : ℕ} {Γ : Finset (Clause n)}
    (ρ : Restriction n) (P : DAGRefutation n Γ) : ℕ :=
  P.size + 5 * assignedBooleanSourceCount ρ P

/-- The cleanup budget is linear: at most six times the original dag size. -/
theorem booleanCleanupSizeBudget_le {n : ℕ} {Γ : Finset (Clause n)}
    (ρ : Restriction n) (P : DAGRefutation n Γ) :
    booleanCleanupSizeBudget ρ P ≤ 6 * P.size := by
  unfold booleanCleanupSizeBudget
  have h := assignedBooleanSourceCount_le_size ρ P
  omega

/-- Splicing a depth-five source macro requires at most five extra levels on any dependent path. -/
def booleanCleanupDepthBudget {n : ℕ} {Γ : Finset (Clause n)}
    (P : DAGRefutation n Γ) : ℕ := P.depth + 5

#print axioms restrictClause_booleanAxiom_of_assigned
#print axioms constantTautology_derivable
#print axioms restricted_booleanAxiom_derivable
#print axioms fixedBooleanCleanupDAG_size
#print axioms fixedBooleanCleanupDAG_depth
#print axioms booleanCleanupSizeBudget_le

end PallLean.Paper93.DeepMath.PathB.ResLinParity
