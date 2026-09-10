import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

/-!
# Exact rational row-basis updates

Finite rational Gram--Schmidt requires no square roots: subtract each
orthogonal component using a rational dot-product quotient. The executable
state retains nonzero pairwise orthogonal rows. A new row is accepted exactly
when its residual is nonzero, equivalently when it is outside the old span.

This is finite arithmetic on supplied rows. No polynomial bound on rational
bit lengths or on the number of rows supplied by an outer search is asserted.
-/

namespace GodMoveRationalRowBasis

open scoped BigOperators

abbrev Vec (s : ℕ) := Fin s → ℚ

def dot {s : ℕ} (v w : Vec s) : ℚ := dotProduct v w

theorem dot_comm {s : ℕ} (v w : Vec s) : dot v w = dot w v := dotProduct_comm _ _

theorem dot_self_eq_zero_iff {s : ℕ} (v : Vec s) : dot v v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    funext i
    have hi : v i * v i ≤ ∑ j : Fin s, v j * v j :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
    change (∑ j : Fin s, v j * v j) = 0 at hv
    have hsq : v i * v i = 0 := le_antisymm (hi.trans_eq hv) (mul_self_nonneg _)
    exact (mul_self_eq_zero.mp hsq)
  · rintro rfl
    simp [dot]

def dotRight {s : ℕ} (w : Vec s) : Vec s →ₗ[ℚ] ℚ where
  toFun := fun v => dot v w
  map_add' := fun v u => add_dotProduct _ _ _
  map_smul' := fun a v => by simp [dot, smul_dotProduct]

@[simp] theorem dotRight_apply {s : ℕ} (v w : Vec s) : dotRight w v = dot v w := rfl

/-- Rows are orthogonal but need not have unit length. -/
structure RowBasis (s : ℕ) where
  count : ℕ
  rows : Fin count → Vec s
  nonzero : ∀ i, rows i ≠ 0
  orthogonal : ∀ i j, i ≠ j → dot (rows i) (rows j) = 0

def empty (s : ℕ) : RowBasis s where
  count := 0
  rows := Fin.elim0
  nonzero := by intro i; exact Fin.elim0 i
  orthogonal := by intro i; exact Fin.elim0 i

noncomputable def rowSpan {s : ℕ} (B : RowBasis s) : Submodule ℚ (Vec s) :=
  Submodule.span ℚ (Set.range B.rows)

theorem row_dot_self_ne_zero {s : ℕ} (B : RowBasis s) (i : Fin B.count) :
    dot (B.rows i) (B.rows i) ≠ 0 := by
  rw [ne_eq, dot_self_eq_zero_iff]
  exact B.nonzero i

theorem dot_row {s : ℕ} (B : RowBasis s) (i j : Fin B.count) :
    dot (B.rows i) (B.rows j) = if i = j then dot (B.rows j) (B.rows j) else 0 := by
  by_cases hij : i = j
  · subst i; simp
  · simp [hij, B.orthogonal i j hij]

theorem dot_sum_rows {s : ℕ} (B : RowBasis s) (g : Fin B.count → ℚ) (j : Fin B.count) :
    dot (∑ i, g i • B.rows i) (B.rows j) = g j * dot (B.rows j) (B.rows j) := by
  change dotRight (B.rows j) (∑ i, g i • B.rows i) = _
  simp only [map_sum, map_smul, dotRight_apply, smul_eq_mul]
  calc
    _ = ∑ i : Fin B.count, if i = j then g j * dot (B.rows j) (B.rows j) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : i = j
      · subst i; simp
      · simp [B.orthogonal i j hij, hij]
    _ = _ := by simp

theorem rows_linearIndependent {s : ℕ} (B : RowBasis s) : LinearIndependent ℚ B.rows := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (dotRight (B.rows j)) hg
  rw [map_zero] at h
  change dot (∑ i, g i • B.rows i) (B.rows j) = 0 at h
  rw [dot_sum_rows] at h
  exact (mul_eq_zero.mp h).resolve_right (row_dot_self_ne_zero B j)

theorem count_le_width {s : ℕ} (B : RowBasis s) : B.count ≤ s := by
  have h := (rows_linearIndependent B).fintype_card_le_finrank
  simpa [Vec, Module.finrank_fintype_fun_eq_card] using h

def component {s : ℕ} (B : RowBasis s) (v : Vec s) (i : Fin B.count) : ℚ :=
  dot v (B.rows i) / dot (B.rows i) (B.rows i)

def projected {s : ℕ} (B : RowBasis s) (v : Vec s) : Vec s :=
  ∑ i : Fin B.count, component B v i • B.rows i

def residual {s : ℕ} (B : RowBasis s) (v : Vec s) : Vec s := v - projected B v

theorem projected_mem {s : ℕ} (B : RowBasis s) (v : Vec s) : projected B v ∈ rowSpan B := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem dot_projected {s : ℕ} (B : RowBasis s) (v : Vec s) (j : Fin B.count) :
    dot (projected B v) (B.rows j) = dot v (B.rows j) := by
  change dot (∑ i, component B v i • B.rows i) (B.rows j) = _
  rw [dot_sum_rows]
  simp [component, row_dot_self_ne_zero B j]

theorem residual_orthogonal {s : ℕ} (B : RowBasis s) (v : Vec s) (j : Fin B.count) :
    dot (residual B v) (B.rows j) = 0 := by
  change dotRight (B.rows j) (v - projected B v) = 0
  rw [map_sub, dotRight_apply, dotRight_apply, dot_projected, sub_self]

theorem residual_orthogonal_span {s : ℕ} (B : RowBasis s) (v w : Vec s)
    (hw : w ∈ rowSpan B) : dot (residual B v) w = 0 := by
  rw [dot_comm]
  change dotRight (residual B v) w = 0
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      rw [dotRight_apply, dot_comm]
      exact residual_orthogonal B v j
  | zero => exact map_zero _
  | add w u _ _ hw hu => simp [map_add, hw, hu]
  | smul a w _ hw => simp [hw]

/-- The executable zero test is exactly a span-membership test. -/
theorem residual_eq_zero_iff {s : ℕ} (B : RowBasis s) (v : Vec s) :
    residual B v = 0 ↔ v ∈ rowSpan B := by
  constructor
  · intro h
    have hv : v = projected B v := sub_eq_zero.mp h
    rw [hv]
    exact projected_mem B v
  · intro hv
    have hr : residual B v ∈ rowSpan B := (rowSpan B).sub_mem hv (projected_mem B v)
    exact (dot_self_eq_zero_iff _).mp (residual_orthogonal_span B v _ hr)

/-- Appending a nonzero residual keeps every invariant without a square root. -/
def grow {s : ℕ} (B : RowBasis s) (v : Vec s) (hv : residual B v ≠ 0) : RowBasis s where
  count := B.count + 1
  rows := Fin.snoc B.rows (residual B v)
  nonzero := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hv
    · simpa using B.nonzero j
  orthogonal := by
    intro i j
    refine Fin.lastCases ?_ (fun k => ?_) i
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · intro hij; exact False.elim (hij rfl)
      · intro _; simpa using residual_orthogonal B v k
    · refine Fin.lastCases ?_ (fun l => ?_) j
      · intro _; simpa [dot_comm] using residual_orthogonal B v k
      · intro hij
        simpa using B.orthogonal k l (fun h => hij (congrArg Fin.castSucc h))

def accepts {s : ℕ} (B : RowBasis s) (v : Vec s) : Bool :=
  decide (residual B v ≠ 0)

def insert {s : ℕ} (B : RowBasis s) (v : Vec s) : RowBasis s :=
  if hv : residual B v = 0 then B else grow B v hv

theorem accepts_iff {s : ℕ} (B : RowBasis s) (v : Vec s) :
    accepts B v = true ↔ v ∉ rowSpan B := by
  simp [accepts, residual_eq_zero_iff]

theorem insert_count {s : ℕ} (B : RowBasis s) (v : Vec s) :
    (insert B v).count = B.count + if accepts B v then 1 else 0 := by
  unfold insert accepts
  split <;> simp_all [grow]

theorem grow_span {s : ℕ} (B : RowBasis s) (v : Vec s) (hv : residual B v ≠ 0) :
    rowSpan (grow B v hv) = rowSpan B ⊔ Submodule.span ℚ {v} := by
  have hrange : Set.range (grow B v hv).rows = Set.range B.rows ∪ {residual B v} := by
    change Set.range (Fin.snoc B.rows (residual B v)) = _
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Or.inr (by simp)
      · exact Or.inl ⟨j, by simp⟩
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨j.castSucc, by simp⟩
      · exact ⟨Fin.last B.count, by simp⟩
  have hsp : rowSpan (grow B v hv) = rowSpan B ⊔ Submodule.span ℚ {residual B v} := by
    unfold rowSpan
    rw [hrange, Submodule.span_union]
  rw [hsp]
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro w hw
    have hwv : w = residual B v := Set.mem_singleton_iff.mp hw
    rw [hwv]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
      (Submodule.mem_sup_left (projected_mem B v))
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro w hw
    have hwv : w = v := Set.mem_singleton_iff.mp hw
    rw [hwv]
    have hmem := Submodule.add_mem (rowSpan B ⊔ Submodule.span ℚ {residual B v})
      (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton (residual B v))))
      (Submodule.mem_sup_left (projected_mem B v))
    simpa only [residual, sub_add_cancel] using hmem

/-- Each update spans exactly the previous rows together with the new supplied row. -/
theorem insert_span {s : ℕ} (B : RowBasis s) (v : Vec s) :
    rowSpan (insert B v) = rowSpan B ⊔ Submodule.span ℚ {v} := by
  unfold insert
  split
  next hv =>
    symm
    apply sup_eq_left.mpr
    exact Submodule.span_le.mpr (by
      intro w hw
      rw [Set.mem_singleton_iff.mp hw]
      exact (residual_eq_zero_iff B v).mp hv)
  next hv => exact grow_span B v hv

@[simp] theorem empty_count (s : ℕ) : (empty s).count = 0 := rfl

@[simp] theorem empty_span (s : ℕ) : rowSpan (empty s) = ⊥ := by
  simp [rowSpan, empty, Set.range_eq_empty]

theorem insert_eq_of_rejects {s : ℕ} (B : RowBasis s) (v : Vec s)
    (h : accepts B v = false) : insert B v = B := by
  have hz : residual B v = 0 := by simpa [accepts] using h
  simp [insert, hz]

/-- The span of the original vectors in a labeled input list. -/
noncomputable def rowListSpan {A : Type*} {s : ℕ} (xs : List (A × Vec s)) :
    Submodule ℚ (Vec s) := Submodule.span ℚ {v | ∃ x ∈ xs, x.2 = v}

@[simp] theorem rowListSpan_nil {A : Type*} {s : ℕ} :
    rowListSpan ([] : List (A × Vec s)) = ⊥ := by
  simp [rowListSpan]

theorem rowListSpan_cons {A : Type*} {s : ℕ} (x : A × Vec s) (xs : List (A × Vec s)) :
    rowListSpan (x :: xs) = Submodule.span ℚ {x.2} ⊔ rowListSpan xs := by
  have hs : {v | ∃ y ∈ x :: xs, y.2 = v} = {x.2} ∪ {v | ∃ y ∈ xs, y.2 = v} := by
    ext v
    simp only [Set.mem_setOf_eq, List.mem_cons, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, rfl | hy, hv⟩
      · exact Or.inl hv.symm
      · exact Or.inr ⟨y, hy, hv⟩
    · rintro (hv | ⟨y, hy, hv⟩)
      · exact ⟨x, Or.inl rfl, hv.symm⟩
      · exact ⟨y, Or.inr hy, hv⟩
  unfold rowListSpan
  rw [hs, Submodule.span_union]

/-- A computable scan retains the original entry whenever its residual adds a direction. -/
def scan {A : Type*} {s : ℕ} (B : RowBasis s) :
    List (A × Vec s) → RowBasis s × List (A × Vec s)
  | [] => (B, [])
  | x :: xs =>
      let out := scan (insert B x.2) xs
      (out.1, if accepts B x.2 then x :: out.2 else out.2)

/-- Executable selection from an arbitrary finite list of labeled rational rows. -/
def selectRows {A : Type*} {s : ℕ} (xs : List (A × Vec s)) : List (A × Vec s) :=
  (scan (empty s) xs).2

theorem scan_count {A : Type*} {s : ℕ} (B : RowBasis s) (xs : List (A × Vec s)) :
    (scan B xs).1.count = B.count + (scan B xs).2.length := by
  induction xs generalizing B with
  | nil => simp [scan]
  | cons x xs ih =>
      have hc := ih (insert B x.2)
      rw [insert_count] at hc
      cases ha : accepts B x.2 <;> simp [scan, ha] at * <;> omega

theorem scan_span {A : Type*} {s : ℕ} (B : RowBasis s) (xs : List (A × Vec s)) :
    rowSpan (scan B xs).1 = rowSpan B ⊔ rowListSpan xs := by
  induction xs generalizing B with
  | nil => simp [scan]
  | cons x xs ih =>
      change rowSpan (scan (insert B x.2) xs).1 = _
      rw [ih, insert_span, rowListSpan_cons, sup_assoc]

theorem scan_selected_span {A : Type*} {s : ℕ} (B : RowBasis s)
    (xs : List (A × Vec s)) :
    rowSpan (scan B xs).1 = rowSpan B ⊔ rowListSpan (scan B xs).2 := by
  induction xs generalizing B with
  | nil => simp [scan]
  | cons x xs ih =>
      cases ha : accepts B x.2 with
      | false =>
          simp only [scan, ha, Bool.false_eq_true, ↓reduceIte]
          rw [insert_eq_of_rejects B x.2 ha]
          exact ih B
      | true =>
          simp only [scan, ha, ↓reduceIte]
          rw [ih, insert_span, rowListSpan_cons, sup_assoc]

theorem scan_subset {A : Type*} {s : ℕ} (B : RowBasis s) (xs : List (A × Vec s)) :
    ∀ x ∈ (scan B xs).2, x ∈ xs := by
  induction xs generalizing B with
  | nil => simp [scan]
  | cons y ys ih =>
      intro x hx
      cases ha : accepts B y.2 with
      | false =>
          simp only [scan, ha, Bool.false_eq_true, ↓reduceIte] at hx
          exact List.mem_cons_of_mem y (ih (insert B y.2) x hx)
      | true =>
          simp only [scan, ha, ↓reduceIte, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem y (ih (insert B y.2) x hx)

theorem selectRows_subset {A : Type*} {s : ℕ} (xs : List (A × Vec s)) :
    ∀ x ∈ selectRows xs, x ∈ xs := scan_subset (empty s) xs

/-- The retained original rows span exactly all supplied rows. -/
theorem selectRows_span {A : Type*} {s : ℕ} (xs : List (A × Vec s)) :
    rowListSpan (selectRows xs) = rowListSpan xs := by
  have hs := scan_span (empty s) xs
  have ht := scan_selected_span (empty s) xs
  simpa [selectRows] using ht.symm.trans hs

/-- The exact row-basis scan retains at most the vector width many original entries. -/
theorem selectRows_length_le {A : Type*} {s : ℕ} (xs : List (A × Vec s)) :
    (selectRows xs).length ≤ s := by
  have hc := scan_count (empty s) xs
  have hb := count_le_width (scan (empty s) xs).1
  rw [hc, empty_count, zero_add] at hb
  exact hb

theorem count_eq_finrank {s : ℕ} (B : RowBasis s) :
    B.count = Module.finrank ℚ (rowSpan B) := by
  simpa [rowSpan] using (finrank_span_eq_card (rows_linearIndependent B)).symm

/-- The returned list contains exactly as many rows as the dimension of the supplied span. -/
theorem selectRows_length_eq_finrank {A : Type*} {s : ℕ} (xs : List (A × Vec s)) :
    (selectRows xs).length = Module.finrank ℚ (rowListSpan xs) := by
  have hc := scan_count (empty s) xs
  have hd := count_eq_finrank (scan (empty s) xs).1
  rw [hc, empty_count, zero_add, scan_span, empty_span, bot_sup_eq] at hd
  exact hd

theorem rowListSpan_eq_span_get {A : Type*} {s : ℕ} (xs : List (A × Vec s)) :
    rowListSpan xs = Submodule.span ℚ (Set.range (fun i : Fin xs.length => (xs.get i).2)) := by
  unfold rowListSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, List.exists_mem_iff_get, Set.mem_range]

/-- The selected original vectors themselves, and not merely their orthogonal residuals,
are linearly independent. -/
theorem selectRows_linearIndependent {A : Type*} {s : ℕ} (xs : List (A × Vec s)) :
    LinearIndependent ℚ (fun i : Fin (selectRows xs).length => ((selectRows xs).get i).2) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  simp only [Fintype.card_fin, Set.finrank]
  rw [← rowListSpan_eq_span_get, selectRows_span]
  exact selectRows_length_eq_finrank xs

end GodMoveRationalRowBasis

#print axioms GodMoveRationalRowBasis.rows_linearIndependent
#print axioms GodMoveRationalRowBasis.count_le_width
#print axioms GodMoveRationalRowBasis.residual_eq_zero_iff
#print axioms GodMoveRationalRowBasis.accepts_iff
#print axioms GodMoveRationalRowBasis.insert_count
#print axioms GodMoveRationalRowBasis.insert_span
#print axioms GodMoveRationalRowBasis.selectRows_subset
#print axioms GodMoveRationalRowBasis.selectRows_span
#print axioms GodMoveRationalRowBasis.selectRows_length_le
#print axioms GodMoveRationalRowBasis.selectRows_length_eq_finrank
#print axioms GodMoveRationalRowBasis.selectRows_linearIndependent
