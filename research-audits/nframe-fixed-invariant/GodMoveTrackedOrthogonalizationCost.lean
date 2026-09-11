import GodMoveTrackedOrthogonalization
import Mathlib.Algebra.BigOperators.Fin

/-!
# Arithmetic-operation accounting for cached tracked orthogonalization

The instrumented routines in this file execute rational arithmetic and retain
materialized vectors. Each rational addition, subtraction, multiplication, or
division contributes one operation. Indexing, allocation, and the natural-number
bookkeeping used to count operations are not included in this arithmetic model.

The count does not establish a bit-operation bound, bound intermediate rational
precision, or compile the builder to a Turing machine.
-/

namespace GodMoveTrackedOrthogonalizationCost

open scoped BigOperators

structure Counted (α : Type*) where
  value : α
  operations : ℕ

def qadd (a b : ℚ) : Counted ℚ := ⟨a + b, 1⟩
def qsub (a b : ℚ) : Counted ℚ := ⟨a - b, 1⟩
def qmul (a b : ℚ) : Counted ℚ := ⟨a * b, 1⟩
def qdiv (a b : ℚ) : Counted ℚ := ⟨a / b, 1⟩

/-- Evaluate each entry once and retain the resulting vector. -/
def tabulate {α : Type*} {n : ℕ} (f : Fin n → Counted α) : Counted (Vector α n) :=
  let cached := Vector.ofFn f
  ⟨cached.map Counted.value, ∑ i : Fin n, (cached[i]).operations⟩

@[simp] theorem tabulate_value {α : Type*} {n : ℕ} (f : Fin n → Counted α) :
    (tabulate f).value = Vector.ofFn (fun i => (f i).value) := by
  ext i hi
  simp [tabulate]

@[simp] theorem tabulate_operations {α : Type*} {n : ℕ} (f : Fin n → Counted α) :
    (tabulate f).operations = ∑ i : Fin n, (f i).operations := by
  simp [tabulate]

theorem tabulate_operations_const {α : Type*} {n : ℕ}
    (f : Fin n → Counted α) (c : ℕ) (hc : ∀ i, (f i).operations = c) :
    (tabulate f).operations = n * c := by
  simp [hc]

/-- A zero-seeded dot-product loop: multiply, add, and recurse on the tail. -/
def sumProductsOn {ι : Type*} (v w : ι → ℚ) : List ι → Counted ℚ → Counted ℚ
  | [], acc => acc
  | i :: is, acc =>
      let product := qmul (v i) (w i)
      let nextSum := qadd acc.value product.value
      sumProductsOn v w is
        ⟨nextSum.value, acc.operations + product.operations + nextSum.operations⟩

theorem sumProductsOn_value {ι : Type*} (v w : ι → ℚ) (is : List ι)
    (acc : Counted ℚ) :
    (sumProductsOn v w is acc).value =
      acc.value + (is.map (fun i => v i * w i)).sum := by
  induction is generalizing acc with
  | nil => simp [sumProductsOn]
  | cons i is ih => simp [sumProductsOn, ih, qmul, qadd, add_assoc]

theorem sumProductsOn_operations {ι : Type*} (v w : ι → ℚ) (is : List ι)
    (acc : Counted ℚ) :
    (sumProductsOn v w is acc).operations = acc.operations + 2 * is.length := by
  induction is generalizing acc with
  | nil => simp [sumProductsOn]
  | cons i is ih => simp [sumProductsOn, ih, qmul, qadd]; omega

def sumProducts {n : ℕ} (v w : Fin n → ℚ) : Counted ℚ :=
  sumProductsOn v w (List.finRange n) ⟨0, 0⟩

@[simp] theorem sumProducts_value {n : ℕ} (v w : Fin n → ℚ) :
    (sumProducts v w).value = ∑ i, v i * w i := by
  simp [sumProducts, sumProductsOn_value, ← List.ofFn_eq_map, Fin.sum_ofFn]

@[simp] theorem sumProducts_operations {n : ℕ} (v w : Fin n → ℚ) :
    (sumProducts v w).operations = 2 * n := by
  simp [sumProducts, sumProductsOn_operations]

def components {n k : ℕ} (v : Vector ℚ n)
    (rows : Vector (Vector ℚ n) k) (norms : Vector ℚ k) :
    Counted (Vector ℚ k) :=
  tabulate fun i =>
    let numerator := sumProducts (fun j => v[j]) (fun j => rows[i][j])
    let quotient := qdiv numerator.value norms[i]
    ⟨quotient.value, numerator.operations + quotient.operations⟩

@[simp] theorem components_value {n k : ℕ} (v : Vector ℚ n)
    (rows : Vector (Vector ℚ n) k) (norms : Vector ℚ k) :
    (components v rows norms).value =
      Vector.ofFn (fun i => (∑ j : Fin n, v[j] * rows[i][j]) / norms[i]) := by
  simp [components, qdiv]

@[simp] theorem components_operations {n k : ℕ} (v : Vector ℚ n)
    (rows : Vector (Vector ℚ n) k) (norms : Vector ℚ k) :
    (components v rows norms).operations = k * (2 * n + 1) := by
  simp [components, qdiv]

def subtractProjection {n k : ℕ} (v : Vector ℚ n) (coeff : Vector ℚ k)
    (rows : Vector (Vector ℚ n) k) : Counted (Vector ℚ n) :=
  tabulate fun j =>
    let projected := sumProducts (fun i => coeff[i]) (fun i => rows[i][j])
    let residual := qsub v[j] projected.value
    ⟨residual.value, projected.operations + residual.operations⟩

@[simp] theorem subtractProjection_value {n k : ℕ} (v : Vector ℚ n)
    (coeff : Vector ℚ k) (rows : Vector (Vector ℚ n) k) :
    (subtractProjection v coeff rows).value =
      Vector.ofFn (fun j => v[j] - ∑ i : Fin k, coeff[i] * rows[i][j]) := by
  simp [subtractProjection, qsub]

@[simp] theorem subtractProjection_operations {n k : ℕ} (v : Vector ℚ n)
    (coeff : Vector ℚ k) (rows : Vector (Vector ℚ n) k) :
    (subtractProjection v coeff rows).operations = n * (2 * k + 1) := by
  simp [subtractProjection, qsub]

/-- Materialize every scaled row before reusing it in the weight matrix. -/
def scaledRows {n : ℕ} (rows : Vector (Vector ℚ n) n) (norms : Vector ℚ n) :
    Counted (Vector (Vector ℚ n) n) :=
  tabulate fun i => tabulate fun j => qdiv rows[i][j] norms[i]

@[simp] theorem scaledRows_value {n : ℕ} (rows : Vector (Vector ℚ n) n)
    (norms : Vector ℚ n) :
    (scaledRows rows norms).value =
      Vector.ofFn (fun i => Vector.ofFn (fun j => rows[i][j] / norms[i])) := by
  simp [scaledRows, qdiv]

@[simp] theorem scaledRows_operations {n : ℕ} (rows : Vector (Vector ℚ n) n)
    (norms : Vector ℚ n) :
    (scaledRows rows norms).operations = n ^ 2 := by
  simp [scaledRows, qdiv, pow_two]

def weights {n : ℕ} (rows coeffs : Vector (Vector ℚ n) n) (norms : Vector ℚ n) :
    Counted (Vector (Vector ℚ n) n) :=
  let scaled := scaledRows rows norms
  let result := tabulate fun j => tabulate fun l =>
    sumProducts (fun i => scaled.value[i][j]) (fun i => coeffs[i][l])
  ⟨result.value, scaled.operations + result.operations⟩

@[simp] theorem weights_value {n : ℕ} (rows coeffs : Vector (Vector ℚ n) n)
    (norms : Vector ℚ n) :
    (weights rows coeffs norms).value =
      Vector.ofFn (fun j => Vector.ofFn (fun l =>
        ∑ i : Fin n, (rows[i][j] / norms[i]) * coeffs[i][l])) := by
  simp [weights]

@[simp] theorem weights_operations {n : ℕ} (rows coeffs : Vector (Vector ℚ n) n)
    (norms : Vector ℚ n) :
    (weights rows coeffs norms).operations = n ^ 2 + 2 * n ^ 3 := by
  simp [weights]
  ring

open GodMoveTrackedOrthogonalization (CachedState Table Row)

/-- Instrument the same cached state update as the numerical builder. -/
def step {n k : ℕ} (B : CachedState n k) (v c : Row n) :
    Counted (CachedState n (k + 1)) :=
  let a := components v B.rows B.norms
  let u := subtractProjection v a.value B.rows
  let d := subtractProjection c a.value B.coeffs
  let norm := sumProducts (fun j => u.value[j]) (fun j => u.value[j])
  ⟨⟨B.rows.push u.value, B.coeffs.push d.value, B.norms.push norm.value⟩,
    a.operations + u.operations + d.operations + norm.operations⟩

@[simp] theorem step_value {n k : ℕ} (B : CachedState n k) (v c : Row n) :
    (step B v c).value = GodMoveTrackedOrthogonalization.step B v c := by
  simp [step, GodMoveTrackedOrthogonalization.step,
    GodMoveTrackedOrthogonalization.components,
    GodMoveTrackedOrthogonalization.subtractComponents,
    GodMoveTrackedOrthogonalization.dotRows]

@[simp] theorem step_operations {n k : ℕ} (B : CachedState n k) (v c : Row n) :
    (step B v c).operations = k * (6 * n + 1) + 4 * n := by
  simp [step]
  ring

/-- The recursive call returns materialized cached state, used once by `step`. -/
def build {n : ℕ} (A : Table n) : (k : ℕ) → Counted (CachedState n k)
  | 0 => ⟨GodMoveTrackedOrthogonalization.emptyState n, 0⟩
  | k + 1 =>
      let previous := build A k
      let next := step previous.value
        (GodMoveTrackedOrthogonalization.inputRow A k)
        (GodMoveTrackedOrthogonalization.unitRow n k)
      ⟨next.value, previous.operations + next.operations⟩

@[simp] theorem build_value {n : ℕ} (A : Table n) (k : ℕ) :
    (build A k).value = GodMoveTrackedOrthogonalization.build A k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [build, GodMoveTrackedOrthogonalization.build, ih]

theorem build_operations {n : ℕ} (A : Table n) (k : ℕ) :
    (build A k).operations = ∑ i ∈ Finset.range k, (i * (6 * n + 1) + 4 * n) := by
  induction k with
  | zero => simp [build]
  | succ k ih => simp [build, Finset.sum_range_succ, ih]

/-- An exact polynomial identity without natural-number division or subtraction. -/
theorem build_operations_exact {n : ℕ} (A : Table n) (k : ℕ) :
    2 * (build A k).operations + (6 * n + 1) * k =
      (6 * n + 1) * k ^ 2 + 8 * n * k := by
  induction k with
  | zero => simp [build]
  | succ k ih =>
      simp only [build, step_operations]
      nlinarith

def inverseTable {n : ℕ} (A : Table n) : Counted (Table n) :=
  let basis := build A n
  let result := weights basis.value.rows basis.value.coeffs basis.value.norms
  ⟨result.value, basis.operations + result.operations⟩

@[simp] theorem inverseTable_value {n : ℕ} (A : Table n) :
    (inverseTable A).value = GodMoveTrackedOrthogonalization.inverseTable A := by
  simp [inverseTable, GodMoveTrackedOrthogonalization.inverseTable,
    GodMoveTrackedOrthogonalization.inverseFromState,
    GodMoveTrackedOrthogonalization.scaledRows]

/-- The exact total count is `(10 n³ + 5 n² - n) / 2`. -/
theorem inverseTable_operations_exact {n : ℕ} (A : Table n) :
    2 * (inverseTable A).operations + n = 10 * n ^ 3 + 5 * n ^ 2 := by
  have h := build_operations_exact A n
  simp only [inverseTable, weights_operations]
  nlinarith

theorem inverseTable_operations_le_cubic {n : ℕ} (A : Table n) :
    (inverseTable A).operations ≤ 8 * n ^ 3 := by
  have h := inverseTable_operations_exact A
  have hs : n ^ 2 ≤ n ^ 3 := by
    cases n with
    | zero => simp
    | succ n => exact Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- A materialized matrix-input wrapper. The cost of obtaining supplied entries
is outside the rational-arithmetic count. -/
def inverseWeights {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Counted (Matrix (Fin n) (Fin n) ℚ) :=
  let input := Vector.ofFn (fun i => Vector.ofFn (A i))
  let result := inverseTable input
  ⟨GodMoveTrackedOrthogonalization.tableValue result.value, result.operations⟩

@[simp] theorem inverseWeights_value {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (inverseWeights A).value = GodMoveTrackedOrthogonalization.inverseWeights A := by
  simp [inverseWeights, GodMoveTrackedOrthogonalization.inverseWeights]

theorem inverseWeights_operations_le_cubic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (inverseWeights A).operations ≤ 8 * n ^ 3 :=
  inverseTable_operations_le_cubic _

/-- Correctness and arithmetic cost of the same executed weight builder. -/
theorem inverseWeights_correct_and_cost {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : LinearIndependent ℚ A) :
    (inverseWeights A).value * A = 1 ∧
      (inverseWeights A).operations ≤ 8 * n ^ 3 := by
  constructor
  · rw [inverseWeights_value]
    exact GodMoveTrackedOrthogonalization.inverseWeights_mul A hA
  · exact inverseWeights_operations_le_cubic A

end GodMoveTrackedOrthogonalizationCost

#print axioms GodMoveTrackedOrthogonalizationCost.sumProducts_value
#print axioms GodMoveTrackedOrthogonalizationCost.sumProducts_operations
#print axioms GodMoveTrackedOrthogonalizationCost.step_value
#print axioms GodMoveTrackedOrthogonalizationCost.step_operations
#print axioms GodMoveTrackedOrthogonalizationCost.build_value
#print axioms GodMoveTrackedOrthogonalizationCost.build_operations_exact
#print axioms GodMoveTrackedOrthogonalizationCost.inverseTable_value
#print axioms GodMoveTrackedOrthogonalizationCost.inverseTable_operations_exact
#print axioms GodMoveTrackedOrthogonalizationCost.inverseTable_operations_le_cubic
#print axioms GodMoveTrackedOrthogonalizationCost.inverseWeights_value
#print axioms GodMoveTrackedOrthogonalizationCost.inverseWeights_operations_le_cubic
#print axioms GodMoveTrackedOrthogonalizationCost.inverseWeights_correct_and_cost
