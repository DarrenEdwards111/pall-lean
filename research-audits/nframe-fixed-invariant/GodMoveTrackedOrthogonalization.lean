import GodMoveRationalRowBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Cached rational orthogonalization with original-row coordinates

The numeric algorithm stores rows, provenance coefficients, and squared
norms in vectors. Each step materializes its component coefficients once,
then materializes both residual rows before appending them. It processes
every supplied row; full row independence ensures its stored norms are
nonzero. The final numeric inverse is also materialized before lookup.

The correctness result concerns exact rational arithmetic. It does not
prove polynomial bit complexity, sample discovery, or a SAT rank bound.
-/

namespace GodMoveTrackedOrthogonalization

open GodMoveRationalRowBasis
open scoped BigOperators

abbrev Row (n : ℕ) := Vector ℚ n
abbrev Table (n : ℕ) := Vector (Row n) n

def rowValue {n : ℕ} (v : Row n) : Vec n := fun j => v[j]
def tableValue {n : ℕ} (A : Table n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => A[i][j]

def dotRows {n : ℕ} (v w : Row n) : ℚ :=
  ∑ j : Fin n, v[j] * w[j]

structure CachedState (n k : ℕ) where
  rows : Vector (Row n) k
  coeffs : Vector (Row n) k
  norms : Vector ℚ k

def emptyState (n : ℕ) : CachedState n 0 :=
  ⟨#v[], #v[], #v[]⟩

def components {n k : ℕ} (B : CachedState n k) (v : Row n) : Vector ℚ k :=
  Vector.ofFn (fun i => dotRows v B.rows[i] / B.norms[i])

def subtractComponents {n k : ℕ} (v : Row n) (a : Vector ℚ k)
    (rows : Vector (Row n) k) : Row n :=
  Vector.ofFn (fun j => v[j] - ∑ i : Fin k, a[i] * rows[i][j])

def step {n k : ℕ} (B : CachedState n k) (v c : Row n) : CachedState n (k + 1) :=
  let a := components B v
  let u := subtractComponents v a B.rows
  let d := subtractComponents c a B.coeffs
  let norm := dotRows u u
  ⟨B.rows.push u, B.coeffs.push d, B.norms.push norm⟩

def unitRow (n k : ℕ) : Row n :=
  Vector.ofFn (fun j => if j.val = k then 1 else 0)

def inputRow {n : ℕ} (A : Table n) (k : ℕ) : Row n :=
  if h : k < n then A[k] else Vector.replicate n 0

def build {n : ℕ} (A : Table n) : (k : ℕ) → CachedState n k
  | 0 => emptyState n
  | k + 1 => step (build A k) (inputRow A k) (unitRow n k)

def scaledRows {n k : ℕ} (B : CachedState n k) : Vector (Row n) k :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => B.rows[i][j] / B.norms[i]))

def inverseFromState {n k : ℕ} (B : CachedState n k) : Table n :=
  let scaled := scaledRows B
  Vector.ofFn (fun j => Vector.ofFn
    (fun l => ∑ i : Fin k, scaled[i][j] * B.coeffs[i][l]))

def inverseTable {n : ℕ} (A : Table n) : Table n :=
  let B := build A n
  inverseFromState B

/-- The two tables are constructed outside the returned lookup closure. -/
def inverseWeights {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let input := Vector.ofFn (fun i => Vector.ofFn (A i))
  let output := inverseTable input
  tableValue output

noncomputable def synthesis {n : ℕ} (A : Table n) : Vec n →ₗ[ℚ] Vec n where
  toFun c := ∑ j : Fin n, c j • tableValue A j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, mul_smul]

noncomputable def prefixSpan {n : ℕ} (A : Table n) (k : ℕ) : Submodule ℚ (Vec n) :=
  Submodule.span ℚ (tableValue A '' {i : Fin n | i.val < k})

structure Valid {n k : ℕ} (A : Table n) (B : CachedState n k) : Prop where
  norms_correct : ∀ i : Fin k, B.norms[i] = dot (rowValue B.rows[i]) (rowValue B.rows[i])
  nonzero : ∀ i : Fin k, rowValue B.rows[i] ≠ 0
  orthogonal : ∀ i j : Fin k, i ≠ j → dot (rowValue B.rows[i]) (rowValue B.rows[j]) = 0
  tracking : ∀ i : Fin k, rowValue B.rows[i] = synthesis A (rowValue B.coeffs[i])
  span_eq : Submodule.span ℚ (Set.range (fun i : Fin k => rowValue B.rows[i])) = prefixSpan A k

def Valid.toRowBasis {n k : ℕ} {A : Table n} {B : CachedState n k}
    (h : Valid A B) : RowBasis n where
  count := k
  rows := fun i => rowValue B.rows[i]
  nonzero := h.nonzero
  orthogonal := h.orthogonal

theorem empty_valid {n : ℕ} (A : Table n) : Valid A (emptyState n) where
  norms_correct := fun i => Fin.elim0 i
  nonzero := fun i => Fin.elim0 i
  orthogonal := fun i => Fin.elim0 i
  tracking := fun i => Fin.elim0 i
  span_eq := by simp [emptyState, prefixSpan, Set.range_eq_empty]

theorem prefixSpan_succ {n : ℕ} (A : Table n) (k : ℕ) (hk : k < n) :
    prefixSpan A (k + 1) = prefixSpan A k ⊔
      Submodule.span ℚ {tableValue A ⟨k, hk⟩} := by
  have hs : {i : Fin n | i.val < k + 1} =
      {i : Fin n | i.val < k} ∪ {⟨k, hk⟩} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
    omega
  simp only [prefixSpan, hs, Set.image_union, Set.image_singleton, Submodule.span_union]

theorem input_not_mem_prefix {n : ℕ} (A : Table n)
    (hA : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k < n) :
    tableValue A ⟨k, hk⟩ ∉ prefixSpan A k := by
  intro hmem
  apply hA.notMem_span ⟨k, hk⟩
  apply Submodule.span_mono (s := tableValue A '' {i : Fin n | i.val < k}) ?_ hmem
  rintro y ⟨i, hi, rfl⟩
  refine ⟨i, ?_, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Fin.ext_iff]
  exact Nat.ne_of_lt hi

theorem rowValue_subtractComponents {n k : ℕ} (v : Row n)
    (a : Vector ℚ k) (rows : Vector (Row n) k) :
    rowValue (subtractComponents v a rows) =
      rowValue v - ∑ i : Fin k, a[i] • rowValue rows[i] := by
  funext j
  simp [rowValue, subtractComponents, Finset.sum_apply]

theorem synthesis_unitRow {n : ℕ} (A : Table n) (k : ℕ) (hk : k < n) :
    synthesis A (rowValue (unitRow n k)) = rowValue (inputRow A k) := by
  have he : rowValue (unitRow n k) =
      (fun j : Fin n => if j = ⟨k, hk⟩ then (1 : ℚ) else 0) := by
    funext j
    simp [rowValue, unitRow, Fin.ext_iff]
  rw [he]
  simp [synthesis, inputRow, hk]
  rfl

theorem components_eq {n k : ℕ} {A : Table n} {B : CachedState n k}
    (h : Valid A B) (v : Row n) (i : Fin k) :
    (components B v)[i] = component h.toRowBasis (rowValue v) i := by
  simp [components, component, h.norms_correct, dotRows, dot, rowValue, dotProduct,
    Valid.toRowBasis]

theorem residualRow_eq {n k : ℕ} {A : Table n} {B : CachedState n k}
    (h : Valid A B) (v : Row n) :
    rowValue (subtractComponents v (components B v) B.rows) =
      residual h.toRowBasis (rowValue v) := by
  rw [rowValue_subtractComponents]
  simp only [components_eq h, GodMoveRationalRowBasis.residual, projected, Valid.toRowBasis]

theorem step_valid {n k : ℕ} (A : Table n)
    (hA : LinearIndependent ℚ (tableValue A)) (hk : k < n)
    (B : CachedState n k) (h : Valid A B) :
    Valid A (step B (inputRow A k) (unitRow n k)) := by
  let v := inputRow A k
  have hv : rowValue v = tableValue A ⟨k, hk⟩ := by
    simp [v, inputRow, hk]
    rfl
  have hnz : residual h.toRowBasis (rowValue v) ≠ 0 := by
    rw [ne_eq, residual_eq_zero_iff]
    change rowValue v ∉ Submodule.span ℚ (Set.range (fun i : Fin k => rowValue B.rows[i]))
    rw [h.span_eq, hv]
    exact input_not_mem_prefix A hA k hk
  have hr : (fun i : Fin (k + 1) =>
      rowValue (step B v (unitRow n k)).rows[i]) =
      (grow h.toRowBasis (rowValue v) hnz).rows := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [step, grow, Valid.toRowBasis] using residualRow_eq h v
    · simp [step, grow, Valid.toRowBasis]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [step, dotRows, dot, rowValue, dotProduct]
    · simpa [step] using h.norms_correct j
  · intro i
    change (fun i : Fin (k + 1) => rowValue (step B v (unitRow n k)).rows[i]) i ≠ 0
    rw [hr]
    exact (grow h.toRowBasis (rowValue v) hnz).nonzero i
  · intro i j hij
    change dot ((fun i : Fin (k + 1) => rowValue (step B v (unitRow n k)).rows[i]) i)
      ((fun i : Fin (k + 1) => rowValue (step B v (unitRow n k)).rows[i]) j) = 0
    rw [hr]
    exact (grow h.toRowBasis (rowValue v) hnz).orthogonal i j hij
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [step, Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq]
      rw [rowValue_subtractComponents, rowValue_subtractComponents,
        map_sub, map_sum, synthesis_unitRow A k hk]
      simp only [map_smul, ← h.tracking]
    · simpa [step] using h.tracking j
  · change Submodule.span ℚ (Set.range
      (fun i : Fin (k + 1) => rowValue (step B v (unitRow n k)).rows[i])) = _
    rw [hr]
    change rowSpan (grow h.toRowBasis (rowValue v) hnz) = _
    rw [grow_span]
    change Submodule.span ℚ (Set.range (fun i : Fin k => rowValue B.rows[i])) ⊔
      Submodule.span ℚ {rowValue v} = _
    rw [h.span_eq, hv, prefixSpan_succ A k hk]

theorem build_valid {n : ℕ} (A : Table n)
    (hA : LinearIndependent ℚ (tableValue A)) (k : ℕ) (hk : k ≤ n) :
    Valid A (build A k) := by
  induction k with
  | zero => exact empty_valid A
  | succ k ih => exact step_valid A hA (by omega) (build A k) (ih (by omega))

theorem build_norms_ne_zero {n : ℕ} (A : Table n)
    (hA : LinearIndependent ℚ (tableValue A)) (i : Fin n) :
    (build A n).norms[i] ≠ 0 := by
  have h := build_valid A hA n le_rfl
  rw [h.norms_correct, ne_eq, dot_self_eq_zero_iff]
  exact h.nonzero i

theorem prefixSpan_full {n : ℕ} (A : Table n)
    (hA : LinearIndependent ℚ (tableValue A)) : prefixSpan A n = ⊤ := by
  have hs : {i : Fin n | i.val < n} = Set.univ := by
    ext i
    simp
  rw [prefixSpan, hs, Set.image_univ]
  apply Submodule.eq_top_of_finrank_eq
  simpa [Module.finrank_fintype_fun_eq_card] using finrank_span_eq_card hA

theorem inverseFromState_row {n k : ℕ} (B : CachedState n k) (j : Fin n) :
    rowValue (inverseFromState B)[j] =
      ∑ i : Fin k, (B.rows[i][j] / B.norms[i]) • rowValue B.coeffs[i] := by
  funext l
  simp [rowValue, inverseFromState, scaledRows, Finset.sum_apply]

theorem dot_unitRow {n : ℕ} (j : Fin n) (v : Vec n) :
    dot (rowValue (unitRow n j.val)) v = v j := by
  simp only [dot, dotProduct, rowValue, unitRow, Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [← Fin.ext_iff, ite_mul, one_mul, zero_mul]
  simp

theorem inverseFromState_mul_apply {n k : ℕ} (A : Table n)
    (B : CachedState n k) (h : Valid A B) (j l : Fin n) :
    (tableValue (inverseFromState B) * tableValue A) j l =
      projected h.toRowBasis (rowValue (unitRow n j.val)) l := by
  calc
    _ = synthesis A (rowValue (inverseFromState B)[j]) l := by
      simp [Matrix.mul_apply, synthesis, tableValue, rowValue, Finset.sum_apply]
    _ = (∑ i : Fin k, (B.rows[i][j] / B.norms[i]) • rowValue B.rows[i]) l := by
      rw [inverseFromState_row, map_sum]
      simp only [map_smul, ← h.tracking]
    _ = _ := by
      simp only [projected, component, Valid.toRowBasis, dot_unitRow, ← h.norms_correct]
      rfl

/-- The cached final numeric table is a left inverse of the supplied square
matrix. Linear independence is the sole nonsingularity premise. -/
theorem inverseTable_mul {n : ℕ} (A : Table n)
    (hA : LinearIndependent ℚ (tableValue A)) :
    tableValue (inverseTable A) * tableValue A = 1 := by
  have h := build_valid A hA n le_rfl
  have hproj : ∀ v : Vec n, projected h.toRowBasis v = v := by
    intro v
    have hz : residual h.toRowBasis v = 0 := by
      apply (residual_eq_zero_iff h.toRowBasis v).mpr
      change v ∈ Submodule.span ℚ (Set.range (fun i : Fin n => rowValue (build A n).rows[i]))
      rw [h.span_eq, prefixSpan_full A hA]
      trivial
    exact (sub_eq_zero.mp hz).symm
  ext j l
  change (tableValue (inverseFromState (build A n)) * tableValue A) j l = _
  rw [inverseFromState_mul_apply A (build A n) h, hproj]
  simp [rowValue, unitRow, Matrix.one_apply, Fin.ext_iff, eq_comm]

/-- Executable cached inverse weights, ready for the finite sample duality
certificate. No inverse matrix or duality proof is supplied to the builder. -/
theorem inverseWeights_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : LinearIndependent ℚ A) : inverseWeights A * A = 1 := by
  let input : Table n := Vector.ofFn (fun i => Vector.ofFn (A i))
  have hi : tableValue input = A := by
    ext i j
    simp [input, tableValue]
  change tableValue (inverseTable input) * A = 1
  rw [← hi]
  exact inverseTable_mul input (by rw [hi]; exact hA)

-- These checks execute the numeric builder; theorem proofs above use no
-- native evaluation axiom.
#guard inverseWeights !![(1 : ℚ), 1; 1, 0] = !![0, 1; 1, -1]
#guard (inverseTable (#v[] : Table 0)).toArray.size = 0

end GodMoveTrackedOrthogonalization

#print axioms GodMoveTrackedOrthogonalization.step_valid
#print axioms GodMoveTrackedOrthogonalization.build_valid
#print axioms GodMoveTrackedOrthogonalization.build_norms_ne_zero
#print axioms GodMoveTrackedOrthogonalization.inverseTable_mul
#print axioms GodMoveTrackedOrthogonalization.inverseWeights_mul
