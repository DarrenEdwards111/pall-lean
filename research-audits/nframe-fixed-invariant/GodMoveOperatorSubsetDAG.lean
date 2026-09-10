import Mathlib

/-!
# A shared, executable straight-line DAG for subset-product coefficients

Each cell is a three-node block: multiply two referenced previous registers
by the supplied A/B inputs, then add the two results. Its references are typed
indices into the previous layer's array-backed vector; `none` references the
shared zero leaf. Layers never contain expanded expression trees. Evaluation
stores each new row before evaluating the next layer, so references reuse
already computed values. Two leaves supply zero and one.

The generated program has exactly 2 + 3*m*(k+1) arithmetic nodes, in addition
to its 2*m supplied input values. Correctness identifies its selected output
with the coefficient of z^k in the product of (A_i + z B_i). The bound counts
arithmetic nodes and does not price large coefficients, expanded polynomial
multiplication, or evaluation of a supplied operator on a large vector.
-/

namespace GodMoveOperatorSubsetDAG

open scoped BigOperators

/-- Two references to stored registers; the second may use the shared zero. -/
structure Cell (k : ℕ) where
  aRef : Fin (k + 1)
  bRef : Option (Fin (k + 1))
deriving Repr, DecidableEq

/-- A layer supplies its input index and its actual array of referenced cells. -/
structure Layer (m k : ℕ) where
  input : Fin m
  cells : Vector (Cell k) (k + 1)
deriving Repr, DecidableEq

/-- The derivative-order-zero cell references zero on its B branch. -/
def standardCell (k : ℕ) (j : Fin (k + 1)) : Cell k :=
  ⟨j, if h : j.val = 0 then none else some ⟨j.val - 1, by omega⟩⟩

def generatedLayer {m : ℕ} (k : ℕ) (i : Fin m) : Layer m k :=
  ⟨i, Vector.ofFn (standardCell k)⟩

/-- This executable generator emits only references, not products over subsets. -/
def program (m k : ℕ) : List (Layer m k) :=
  (List.finRange m).map (generatedLayer k)

/-- Count the two leaves and the three arithmetic nodes of each stored cell. -/
def nodeCount {m k : ℕ} (P : List (Layer m k)) : ℕ :=
  2 + (P.map (fun L => 3 * L.cells.toArray.size)).sum

theorem program_nodeCount (m k : ℕ) :
    nodeCount (program m k) = 2 + 3 * m * (k + 1) := by
  simp [nodeCount, program, Function.comp_def, Nat.mul_comm,
    Nat.mul_left_comm]

theorem program_layers (m k : ℕ) : (program m k).length = m := by
  simp [program]

variable {R : Type*} [Semiring R]

/-- The two products are computed once, then referenced by their addition. -/
def evalCell {k : ℕ} (a b : R) (old : Vector R (k + 1)) (C : Cell k) : R :=
  let lhs := a * old.get C.aRef
  let rhs := b * C.bRef.elim 0 old.get
  lhs + rhs

def evalLayer {m k : ℕ} (A B : Fin m → R) (old : Vector R (k + 1))
    (L : Layer m k) : Vector R (k + 1) :=
  Vector.ofFn (fun j => evalCell (A L.input) (B L.input) old (L.cells.get j))

def initialRow (k : ℕ) : Vector R (k + 1) :=
  Vector.ofFn (fun j => if j.val = 0 then 1 else 0)

/-- Tail-recursive layer evaluation retains a value array for the shared ports. -/
def evalProgram {m k : ℕ} (A B : Fin m → R) (P : List (Layer m k)) :
    Vector R (k + 1) :=
  P.foldl (evalLayer A B) (initialRow k)

def evalDAG {m : ℕ} (A B : Fin m → R) (k : ℕ) : R :=
  (evalProgram A B (program m k)).get ⟨k, by omega⟩

/-- Every layer implements the required recurrence from its stored predecessors. -/
theorem eval_generatedLayer_get {m k : ℕ} (A B : Fin m → R)
    (old : Vector R (k + 1)) (i : Fin m) (j : Fin (k + 1)) :
    (evalLayer A B old (generatedLayer k i)).get j =
      A i * old.get j + B i *
        (if h : j.val = 0 then 0 else old.get ⟨j.val - 1, by omega⟩) := by
  by_cases h : j = 0 <;>
    simp [evalLayer, generatedLayer, standardCell, evalCell, Vector.get, h]

/-- A single univariate factor records selecting A or selecting B. -/
noncomputable def factor (a b : R) : Polynomial R :=
  Polynomial.C a + Polynomial.C b * Polynomial.X

theorem factor_mul_coeff (a b : R) (p : Polynomial R) (j : ℕ) :
    ((factor a b) * p).coeff j = a * p.coeff j +
      b * (if j = 0 then 0 else p.coeff (j - 1)) := by
  cases j <;>
    simp [factor, add_mul, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

/-- The finite stored row computes exactly the corresponding coefficients. -/
theorem fold_coefficients {m k : ℕ} (A B : Fin m → R) (xs : List (Fin m))
    (p : Polynomial R) (row : Vector R (k + 1))
    (hrow : ∀ j : Fin (k + 1), row.get j = p.coeff j.val) :
    ∀ j : Fin (k + 1),
      (xs.foldl (fun old i => evalLayer A B old (generatedLayer k i)) row).get j =
        (xs.foldl (fun p i => factor (A i) (B i) * p) p).coeff j.val := by
  induction xs generalizing p row with
  | nil => exact hrow
  | cons i xs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro j
    rw [eval_generatedLayer_get, factor_mul_coeff]
    by_cases hj : j.val = 0 <;> simp [hj, hrow]

/-- The generated DAG's output equals the coefficient of its ordered product.
This version also allows noncommutative coefficients. -/
theorem evalDAG_eq_fold_coefficient {m : ℕ} (A B : Fin m → R) (k : ℕ) :
    evalDAG A B k =
      ((List.finRange m).foldl (fun p i => factor (A i) (B i) * p) 1).coeff k := by
  have h := fold_coefficients A B (List.finRange m) (1 : Polynomial R) (initialRow k)
    (fun j => by simp [initialRow, Vector.get, Polynomial.coeff_one]) ⟨k, by omega⟩
  simpa only [evalDAG, evalProgram, program, List.foldl_map] using h

section Commutative

variable [CommSemiring S]

theorem fold_product (f : ι → S) (xs : List ι) (p : S) :
    xs.foldl (fun q i => f i * q) p = (xs.map f).prod * p := by
  induction xs generalizing p with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
    ac_rfl

/-- In a commutative semiring this is exactly the coefficient of the product
over all input positions; expanding that product is not part of execution. -/
theorem evalDAG_eq_coefficient {m : ℕ} (A B : Fin m → S) (k : ℕ) :
    evalDAG A B k = (∏ i : Fin m, factor (A i) (B i)).coeff k := by
  rw [evalDAG_eq_fold_coefficient, fold_product, mul_one]
  congr 1

end Commutative

/-- Kernel-evaluated execution: (1+4z)(2+5z)(3+6z) has coefficient 51 at z. -/
theorem numeric_execution :
    evalDAG (fun i : Fin 3 => i.val + 1) (fun i : Fin 3 => i.val + 4) 1 = 51 ∧
    evalDAG (fun _ : Fin 5 => (1 : ℕ)) (fun _ => 1) 2 = 10 := by decide

#eval nodeCount (program 5 2)
#eval evalDAG (fun i : Fin 3 => i.val + 1) (fun i : Fin 3 => i.val + 4) 1
#eval evalDAG (fun _ : Fin 5 => (1 : ℕ)) (fun _ => 1) 2

end GodMoveOperatorSubsetDAG

#print axioms GodMoveOperatorSubsetDAG.program_nodeCount
#print axioms GodMoveOperatorSubsetDAG.program_layers
#print axioms GodMoveOperatorSubsetDAG.eval_generatedLayer_get
#print axioms GodMoveOperatorSubsetDAG.factor_mul_coeff
#print axioms GodMoveOperatorSubsetDAG.fold_coefficients
#print axioms GodMoveOperatorSubsetDAG.evalDAG_eq_fold_coefficient
#print axioms GodMoveOperatorSubsetDAG.evalDAG_eq_coefficient
#print axioms GodMoveOperatorSubsetDAG.numeric_execution
