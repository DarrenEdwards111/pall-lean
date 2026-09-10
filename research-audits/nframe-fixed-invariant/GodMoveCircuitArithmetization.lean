import GodMoveBooleanInterpolation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade

/-!
# Gate-by-gate arithmetization with shared wires

Each existing Boolean `CGate` becomes a constant-size arithmetic expression
reading the same earlier wire indices. Arbitrary unary and binary Boolean
operations use their two- or four-entry local truth tables. The compiler
traverses the gate list; it does not enumerate assignments of its input bits.

`compile` is the retained arithmetic DAG syntax. Its expression-node count is
at most 25 times the Boolean gate count. `rawPoly` is its full-ring polynomial
denotation, whose expanded coefficient representation may be exponentially
larger. Evaluation on Boolean inputs is proved correct, including shared and
out-of-range wires (the latter default to zero, matching `false`).

This counts arithmetic syntax and operations, not bit-level Turing-machine
time, off-cube rational precision, expanded polynomial size, normalization
cost, or SPDP rank. Those quantities require separate arguments.
-/

namespace GodMoveCircuitArithmetization

open GodMoveBooleanInterpolation
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- One local arithmetic expression. A wire is a reference, not a recursively
copied prior expression, so fan-out and rereading retain sharing. -/
inductive AExpr (n : ℕ) where
  | cst : Bool → AExpr n
  | var : Fin n → AExpr n
  | wire : ℕ → AExpr n
  | add : AExpr n → AExpr n → AExpr n
  | sub : AExpr n → AExpr n → AExpr n
  | mul : AExpr n → AExpr n → AExpr n

def AExpr.size {n : ℕ} : AExpr n → ℕ
  | .cst _ | .var _ | .wire _ => 1
  | .add p q | .sub p q | .mul p q => p.size + q.size + 1

/-- Scalar additions, subtractions and multiplications; wire reads are counted
as references by `size`, not arithmetic operations. -/
def AExpr.operations {n : ℕ} : AExpr n → ℕ
  | .cst _ | .var _ | .wire _ => 0
  | .add p q | .sub p q | .mul p q => p.operations + q.operations + 1

def AExpr.eval {n : ℕ} {R : Type*} [Ring R]
    (x : Fin n → R) (vals : List R) : AExpr n → R
  | .cst b => if b then 1 else 0
  | .var i => x i
  | .wire j => vals.getD j 0
  | .add p q => p.eval x vals + q.eval x vals
  | .sub p q => p.eval x vals - q.eval x vals
  | .mul p q => p.eval x vals * q.eval x vals

/-- A two-point affine interpolation. -/
def select {n : ℕ} (p q₀ q₁ : AExpr n) : AExpr n :=
  .add (.mul (.sub (.cst true) p) q₀) (.mul p q₁)

/-- Four local truth-table entries suffice for any binary Boolean gate. -/
def arithGate {n : ℕ} : CGate n → AExpr n
  | .var i => .var i
  | .cst b => .cst b
  | .un op j => select (.wire j) (.cst (op false)) (.cst (op true))
  | .bin op j k =>
      select (.wire k)
        (select (.wire j) (.cst (op false false)) (.cst (op true false)))
        (select (.wire j) (.cst (op false true)) (.cst (op true true)))

def compile {n : ℕ} (c : List (CGate n)) : List (AExpr n) := c.map arithGate

def representationCost {n : ℕ} (c : List (AExpr n)) : ℕ :=
  (c.map AExpr.size).sum

def arithmeticCost {n : ℕ} (c : List (AExpr n)) : ℕ :=
  (c.map AExpr.operations).sum

theorem arithGate_size_le {n : ℕ} (g : CGate n) :
    (arithGate g).size ≤ 25 := by
  cases g <;> simp [arithGate, select, AExpr.size]

theorem compile_length {n : ℕ} (c : List (CGate n)) :
    (compile c).length = c.length := by simp [compile]

theorem arithGate_operations_le {n : ℕ} (g : CGate n) :
    (arithGate g).operations ≤ 12 := by
  cases g <;> simp [arithGate, select, AExpr.operations]

theorem compile_cost_le {n : ℕ} (c : List (CGate n)) :
    representationCost (compile c) ≤ 25 * c.length := by
  induction c with
  | nil => simp [representationCost, compile]
  | cons g gs ih =>
      have hg := arithGate_size_le g
      simp only [representationCost, compile, List.map_cons, List.sum_cons,
        List.length_cons] at *
      omega

theorem compile_arithmeticCost_le {n : ℕ} (c : List (CGate n)) :
    arithmeticCost (compile c) ≤ 12 * c.length := by
  induction c with
  | nil => simp [arithmeticCost, compile]
  | cons g gs ih =>
      have hg := arithGate_operations_le g
      simp only [arithmeticCost, compile, List.map_cons, List.sum_cons,
        List.length_cons] at *
      omega

def runArithmetic {n : ℕ} {R : Type*} [Ring R]
    (x : Fin n → R) (vals : List R) : List (AExpr n) → List R
  | [] => vals
  | g :: gs => runArithmetic x (vals ++ [g.eval x vals]) gs

theorem runArithmetic_length {n : ℕ} {R : Type*} [Ring R]
    (x : Fin n → R) (vals : List R) (c : List (AExpr n)) :
    (runArithmetic x vals c).length = vals.length + c.length := by
  induction c generalizing vals with
  | nil => simp [runArithmetic]
  | cons g gs ih => simp [runArithmetic, ih, Nat.add_assoc, Nat.add_comm 1]

theorem compile_wire_count {n : ℕ} (a : Assignment n) (c : List (CGate n)) :
    (runArithmetic (booleanPoint a) [] (compile c)).length = c.length := by
  simp [runArithmetic_length, compile_length]

/-- The complete polynomial is a denotation of the shared program. Constructing
this expanded mathematical object is not the claimed efficient operation. -/
noncomputable def rawPoly {n : ℕ} (c : List (CGate n)) : Poly n :=
  (runArithmetic MvPolynomial.X [] (compile c)).getD (c.length - 1) 0

theorem eval_arithGate {n : ℕ} (a : Assignment n) (vals : List Bool)
    (g : CGate n) :
    (arithGate g).eval (booleanPoint a) (vals.map bit) =
      bit (evalGate a vals g) := by
  have hw (j : ℕ) : (vals.map bit).getD j 0 = bit (vals.getD j false) := by
    simpa [bit] using (List.getD_map (l := vals) (d := false) (n := j) bit)
  cases g with
  | var i => rfl
  | cst b => rfl
  | un op j =>
      simp only [arithGate, select, AExpr.eval, hw, evalGate]
      cases vals.getD j false <;> simp [bit]
  | bin op j k =>
      simp only [arithGate, select, AExpr.eval, hw, evalGate]
      cases vals.getD j false <;> cases vals.getD k false <;> simp [bit]

theorem runArithmetic_compile {n : ℕ} (a : Assignment n) (vals : List Bool)
    (c : List (CGate n)) :
    runArithmetic (booleanPoint a) (vals.map bit) (compile c) =
      (runFrom a vals c).map bit := by
  induction c generalizing vals with
  | nil => rfl
  | cons g gs ih =>
      simp only [compile, List.map_cons, runArithmetic, runFrom]
      rw [eval_arithGate]
      simpa only [List.map_append, List.map_cons, List.map_nil] using
        ih (vals ++ [evalGate a vals g])

/-- Every stored wire on Boolean input is exactly zero or one, even though
off-cube polynomial evaluation need not retain this precision bound. -/
theorem compile_wires_boolean {n : ℕ} (a : Assignment n) (c : List (CGate n))
    (q : ℚ) (hq : q ∈ runArithmetic (booleanPoint a) [] (compile c)) :
    q = 0 ∨ q = 1 := by
  rw [show runArithmetic (booleanPoint a) [] (compile c) = (runFrom a [] c).map bit
    from runArithmetic_compile a [] c] at hq
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hq
  cases b <;> simp [bit]

theorem eval_AExpr_poly {n : ℕ} (a : Assignment n) (vals : List (Poly n))
    (g : AExpr n) :
    MvPolynomial.eval (booleanPoint a) (g.eval MvPolynomial.X vals) =
      g.eval (booleanPoint a) (vals.map (MvPolynomial.eval (booleanPoint a))) := by
  induction g with
  | cst b => cases b <;> simp [AExpr.eval]
  | var i => simp [AExpr.eval]
  | wire j =>
      simpa [AExpr.eval] using
        (List.getD_map (l := vals) (d := 0) (n := j)
          (MvPolynomial.eval (booleanPoint a))).symm
  | add p q hp hq => simp [AExpr.eval, hp, hq]
  | sub p q hp hq => simp [AExpr.eval, hp, hq]
  | mul p q hp hq => simp [AExpr.eval, hp, hq]

theorem eval_runArithmetic_poly {n : ℕ} (a : Assignment n)
    (vals : List (Poly n)) (c : List (AExpr n)) :
    (runArithmetic MvPolynomial.X vals c).map (MvPolynomial.eval (booleanPoint a)) =
      runArithmetic (booleanPoint a) (vals.map (MvPolynomial.eval (booleanPoint a))) c := by
  induction c generalizing vals with
  | nil => rfl
  | cons g gs ih =>
      simp only [runArithmetic]
      rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil, eval_AExpr_poly]

/-- Exact semantics on the Boolean cube, derived gate-by-gate. -/
theorem eval_rawPoly {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    MvPolynomial.eval (booleanPoint a) (rawPoly c) = bit (output c a) := by
  unfold rawPoly output
  have hp := List.getD_map
    (l := runArithmetic (MvPolynomial.X : Fin n → Poly n) [] (compile c))
    (d := 0) (n := c.length - 1) (MvPolynomial.eval (booleanPoint a))
  have hb := List.getD_map (l := runFrom a [] c)
    (d := false) (n := c.length - 1) bit
  rw [eval_runArithmetic_poly] at hp
  simp only [List.map_nil, map_zero] at hp
  rw [show runArithmetic (booleanPoint a) [] (compile c) = (runFrom a [] c).map bit
      from runArithmetic_compile a [] c] at hp
  rw [← hp]
  simpa [bit] using hb

end GodMoveCircuitArithmetization

#print axioms GodMoveCircuitArithmetization.arithGate_size_le
#print axioms GodMoveCircuitArithmetization.compile_length
#print axioms GodMoveCircuitArithmetization.compile_cost_le
#print axioms GodMoveCircuitArithmetization.compile_arithmeticCost_le
#print axioms GodMoveCircuitArithmetization.compile_wire_count
#print axioms GodMoveCircuitArithmetization.compile_wires_boolean
#print axioms GodMoveCircuitArithmetization.eval_arithGate
#print axioms GodMoveCircuitArithmetization.runArithmetic_compile
#print axioms GodMoveCircuitArithmetization.eval_rawPoly
