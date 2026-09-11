import GodMoveTrackedOrthogonalizationCost

/-!
# Cached orthogonal-row insertion for adaptive discovery

Each state stores materialized rational rows and their squared norms. Insertion
materializes its projection coefficients and residual exactly once, computes one
squared norm, and makes one zero comparison. Its semantic row basis is exactly
the existing `GodMoveRationalRowBasis.insert` result. The arithmetic count is for
the executed counted rational loops; it excludes comparison, indexing, allocation,
input-row acquisition, and the internal integer cost of rational primitives.
-/

namespace GodMoveCachedDiscoveryBasis

open GodMoveTrackedOrthogonalization (Row rowValue)
open GodMoveTrackedOrthogonalizationCost (Counted)
open scoped BigOperators

structure CachedBasis (s : ℕ) where
  count : ℕ
  rows : Vector (Row s) count
  norms : Vector ℚ count
  nonzero : ∀ i : Fin count, rowValue rows[i] ≠ 0
  orthogonal : ∀ i j : Fin count, i ≠ j →
    GodMoveRationalRowBasis.dot (rowValue rows[i]) (rowValue rows[j]) = 0
  norms_correct : ∀ i : Fin count, norms[i] =
    GodMoveRationalRowBasis.dot (rowValue rows[i]) (rowValue rows[i])

def CachedBasis.toRowBasis {s : ℕ} (B : CachedBasis s) :
    GodMoveRationalRowBasis.RowBasis s where
  count := B.count
  rows i := rowValue B.rows[i]
  nonzero := B.nonzero
  orthogonal := B.orthogonal

@[simp] theorem toRowBasis_count {s : ℕ} (B : CachedBasis s) :
    B.toRowBasis.count = B.count := rfl

theorem count_le_width {s : ℕ} (B : CachedBasis s) : B.count ≤ s :=
  GodMoveRationalRowBasis.count_le_width B.toRowBasis

def empty (s : ℕ) : CachedBasis s where
  count := 0
  rows := #v[]
  norms := #v[]
  nonzero := fun i => Fin.elim0 i
  orthogonal := fun i => Fin.elim0 i
  norms_correct := fun i => Fin.elim0 i

private theorem rowBasis_ext {s : ℕ} {B C : GodMoveRationalRowBasis.RowBasis s}
    (hc : B.count = C.count)
    (hr : ∀ i : Fin B.count, B.rows i = C.rows (Fin.cast hc i)) : B = C := by
  cases B with
  | mk bc br bn bo =>
    cases C with
    | mk cc cr cn co =>
      dsimp only at hc
      subst cc
      have he : br = cr := funext hr
      subst cr
      rfl

@[simp] theorem empty_value (s : ℕ) :
    (empty s).toRowBasis = GodMoveRationalRowBasis.empty s := by
  apply rowBasis_ext
  case hc => rfl
  case hr =>
    intro i
    exact Fin.elim0 i

/-- Components and the residual are each cached before reuse. -/
def residual {s : ℕ} (B : CachedBasis s) (v : Row s) : Counted (Row s) :=
  let coeff := GodMoveTrackedOrthogonalizationCost.components v B.rows B.norms
  let result := GodMoveTrackedOrthogonalizationCost.subtractProjection v coeff.value B.rows
  ⟨result.value, coeff.operations + result.operations⟩

theorem residual_value {s : ℕ} (B : CachedBasis s) (v : Row s) :
    rowValue (residual B v).value =
      GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v) := by
  funext j
  simp [residual, GodMoveRationalRowBasis.residual, GodMoveRationalRowBasis.projected,
    GodMoveRationalRowBasis.component, B.norms_correct, CachedBasis.toRowBasis,
    GodMoveRationalRowBasis.dot, rowValue, dotProduct, Finset.sum_apply]

theorem residual_operations {s : ℕ} (B : CachedBasis s) (v : Row s) :
    (residual B v).operations = B.count * (4 * s + 1) + s := by
  simp [residual]
  ring

private theorem residual_ne_zero {s : ℕ} (B : CachedBasis s) (v r : Row s)
    (hrow : rowValue r = GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v))
    (norm : ℚ) (hnorm : norm = GodMoveRationalRowBasis.dot (rowValue r) (rowValue r))
    (hn : norm ≠ 0) : GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v) ≠ 0 := by
  rw [← hrow]
  intro hr
  apply hn
  rw [hnorm, hr]
  simp [GodMoveRationalRowBasis.dot]

/-- Append the already computed row and norm. All proof fields are erased. -/
def grow {s : ℕ} (B : CachedBasis s) (v r : Row s)
    (hrow : rowValue r = GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v))
    (norm : ℚ) (hnorm : norm = GodMoveRationalRowBasis.dot (rowValue r) (rowValue r))
    (hn : norm ≠ 0) : CachedBasis s := by
  let logical := GodMoveRationalRowBasis.grow B.toRowBasis (rowValue v)
    (residual_ne_zero B v r hrow norm hnorm hn)
  have he : ∀ i : Fin (B.count + 1), rowValue (B.rows.push r)[i] = logical.rows i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [logical, GodMoveRationalRowBasis.grow] using hrow
    · simp [logical, GodMoveRationalRowBasis.grow, CachedBasis.toRowBasis]
  exact {
    count := B.count + 1
    rows := B.rows.push r
    norms := B.norms.push norm
    nonzero := fun i => by rw [he]; exact logical.nonzero i
    orthogonal := fun i j hij => by rw [he, he]; exact logical.orthogonal i j hij
    norms_correct := fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hnorm
      · simpa using B.norms_correct j
  }

theorem grow_value {s : ℕ} (B : CachedBasis s) (v r : Row s)
    (hrow : rowValue r = GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v))
    (norm : ℚ) (hnorm : norm = GodMoveRationalRowBasis.dot (rowValue r) (rowValue r))
    (hn : norm ≠ 0) :
    (grow B v r hrow norm hnorm hn).toRowBasis =
      GodMoveRationalRowBasis.grow B.toRowBasis (rowValue v)
        (residual_ne_zero B v r hrow norm hnorm hn) := by
  apply rowBasis_ext
  case hc => rfl
  case hr =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [grow, CachedBasis.toRowBasis, GodMoveRationalRowBasis.grow] using hrow
    · simp [grow, CachedBasis.toRowBasis, GodMoveRationalRowBasis.grow]

/-- One cached residual, one cached squared norm, and one zero comparison. -/
def insert {s : ℕ} (B : CachedBasis s) (v : Row s) : Counted (CachedBasis s) :=
  let r := residual B v
  let norm := GodMoveTrackedOrthogonalizationCost.sumProducts
    (fun j => r.value[j]) (fun j => r.value[j])
  let next := if hn : norm.value = 0 then B else
    grow B v r.value (residual_value B v) norm.value
      (by simp [norm, GodMoveRationalRowBasis.dot, rowValue, dotProduct]) hn
  ⟨next, r.operations + norm.operations⟩

theorem insert_value {s : ℕ} (B : CachedBasis s) (v : Row s) :
    (insert B v).value.toRowBasis =
      GodMoveRationalRowBasis.insert B.toRowBasis (rowValue v) := by
  have he : (GodMoveTrackedOrthogonalizationCost.sumProducts
      (fun j => (residual B v).value[j]) (fun j => (residual B v).value[j])).value = 0 ↔
      GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v) = 0 := by
    rw [← residual_value B v, ← GodMoveRationalRowBasis.dot_self_eq_zero_iff]
    simp [GodMoveRationalRowBasis.dot, rowValue, dotProduct]
  by_cases hz : GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v) = 0
  · simp only [insert, GodMoveRationalRowBasis.insert, hz, he.mpr hz, ↓reduceDIte]
  · have hn : ¬ (GodMoveTrackedOrthogonalizationCost.sumProducts
        (fun j => (residual B v).value[j]) (fun j => (residual B v).value[j])).value = 0 :=
      fun h => hz (he.mp h)
    simp only [insert, GodMoveRationalRowBasis.insert, hz, hn, ↓reduceDIte]
    exact grow_value _ _ _ _ _ _ _

theorem insert_operations {s : ℕ} (B : CachedBasis s) (v : Row s) :
    (insert B v).operations = B.count * (4 * s + 1) + 3 * s := by
  simp only [insert, residual_operations, GodMoveTrackedOrthogonalizationCost.sumProducts_operations]
  ring

theorem insert_operations_le_quadratic {s : ℕ} (B : CachedBasis s) (v : Row s) :
    (insert B v).operations ≤ 8 * (s + 1) ^ 2 := by
  rw [insert_operations]
  have h := count_le_width B
  nlinarith

theorem insert_count {s : ℕ} (B : CachedBasis s) (v : Row s) :
    (insert B v).value.count = B.count +
      if GodMoveRationalRowBasis.accepts B.toRowBasis (rowValue v) then 1 else 0 := by
  have h := congrArg GodMoveRationalRowBasis.RowBasis.count (insert_value B v)
  simpa only [toRowBasis_count, GodMoveRationalRowBasis.insert_count] using h

theorem insert_span {s : ℕ} (B : CachedBasis s) (v : Row s) :
    GodMoveRationalRowBasis.rowSpan (insert B v).value.toRowBasis =
      GodMoveRationalRowBasis.rowSpan B.toRowBasis ⊔
        Submodule.span ℚ {rowValue v} := by
  rw [insert_value, GodMoveRationalRowBasis.insert_span]

end GodMoveCachedDiscoveryBasis

#print axioms GodMoveCachedDiscoveryBasis.residual_value
#print axioms GodMoveCachedDiscoveryBasis.residual_operations
#print axioms GodMoveCachedDiscoveryBasis.insert_value
#print axioms GodMoveCachedDiscoveryBasis.insert_operations
#print axioms GodMoveCachedDiscoveryBasis.insert_operations_le_quadratic
#print axioms GodMoveCachedDiscoveryBasis.insert_count
#print axioms GodMoveCachedDiscoveryBasis.insert_span
