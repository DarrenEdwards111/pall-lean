import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerCoords
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# Round 70 Plucker general progress

This file adds determinant-backed Plucker infrastructure that is reusable
beyond fixed generated examples:

* ordered maximal minors with column permutation, swap, repeated-column,
  zero-row/zero-column, and scalar-multiplication behavior;
* support/cardinality lemmas for the unordered `pluckerCoord`;
* the Grassmann-Plucker relation for every ordered quadruple of columns in a
  `2 x n` matrix.

Kernel-only: no `sorry`, no custom `axiom`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

noncomputable section

/-! ## Ordered Plucker coordinates -/

/-- Ordered maximal minor: select columns by an arbitrary map `c : Fin k -> Fin n`.
This version keeps the ordering visible, so column permutations and repeated
selected columns can be stated without constructing a `Finset`. -/
def orderedPluckerCoord {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin k → Fin n) : ℝ :=
  (M.submatrix id c).det

/-- The ordered coordinate is just the determinant of its selected submatrix. -/
theorem orderedPluckerCoord_def {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin k → Fin n) :
    orderedPluckerCoord M c = (M.submatrix id c).det := rfl

/-- A determinant identity for permuting columns of a square matrix. Mathlib has
`Matrix.det_permute` for rows; applying it to the transpose gives this column
version. -/
theorem det_submatrix_id_perm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (σ : Equiv.Perm (Fin k)) :
    (A.submatrix id σ).det = ((Equiv.Perm.sign σ : ℤˣ) : ℝ) * A.det := by
  rw [← Matrix.det_transpose]
  have hsub : (A.submatrix id σ).transpose = A.transpose.submatrix σ id := by
    ext i j
    rfl
  rw [hsub, Matrix.det_permute, Matrix.det_transpose]

/-- Ordered Plucker coordinates transform by the sign of a column permutation. -/
theorem orderedPluckerCoord_perm_columns {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n)
    (σ : Equiv.Perm (Fin k)) :
    orderedPluckerCoord M (c ∘ σ) =
      ((Equiv.Perm.sign σ : ℤˣ) : ℝ) * orderedPluckerCoord M c := by
  unfold orderedPluckerCoord
  rw [show M.submatrix id (c ∘ σ) = (M.submatrix id c).submatrix id σ from by
    ext i j
    rfl]
  exact det_submatrix_id_perm (M.submatrix id c) σ

/-- Swapping two selected columns negates the ordered coordinate. -/
theorem orderedPluckerCoord_swap_columns {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n)
    {i j : Fin k} (hij : i ≠ j) :
    orderedPluckerCoord M (c ∘ Equiv.swap i j) = - orderedPluckerCoord M c := by
  rw [orderedPluckerCoord_perm_columns]
  rw [Equiv.Perm.sign_swap hij]
  norm_num

/-- If two selected columns coincide, the ordered coordinate vanishes. -/
theorem orderedPluckerCoord_zero_of_repeated_selected_column {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n)
    {i j : Fin k} (hij : i ≠ j) (hc : c i = c j) :
    orderedPluckerCoord M c = 0 := by
  unfold orderedPluckerCoord
  exact Matrix.det_zero_of_column_eq hij (fun r => by
    change M r (c i) = M r (c j)
    rw [hc])

/-- A nonzero ordered coordinate can only use an injective column selector. -/
theorem orderedPluckerCoord_injective_of_ne_zero {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n)
    (hne : orderedPluckerCoord M c ≠ 0) :
    Function.Injective c := by
  intro i j hc
  by_contra hij
  exact hne (orderedPluckerCoord_zero_of_repeated_selected_column M c hij hc)

/-- If more rows are selected than ambient columns, every ordered maximal minor
vanishes by the finite pigeonhole obstruction. -/
theorem orderedPluckerCoord_eq_zero_of_card_lt {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n) (hkn : n < k) :
    orderedPluckerCoord M c = 0 := by
  by_contra hne
  have hinj : Function.Injective c := orderedPluckerCoord_injective_of_ne_zero M c hne
  have hle : k ≤ n := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective c hinj
  exact (Nat.not_lt_of_ge hle) hkn

/-- A selected zero column forces the ordered coordinate to vanish. -/
theorem orderedPluckerCoord_zero_of_selected_zero_column {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n) (j : Fin k)
    (hcol : ∀ r : Fin k, M r (c j) = 0) :
    orderedPluckerCoord M c = 0 := by
  unfold orderedPluckerCoord
  exact Matrix.det_eq_zero_of_column_eq_zero j (fun r => hcol r)

/-- A zero row in the ambient matrix forces every ordered coordinate to vanish. -/
theorem orderedPluckerCoord_zero_of_row_zero {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n) (r : Fin k)
    (hrow : ∀ j : Fin n, M r j = 0) :
    orderedPluckerCoord M c = 0 := by
  unfold orderedPluckerCoord
  exact Matrix.det_eq_zero_of_row_eq_zero r (fun j => hrow (c j))

/-- Scalar multiplication of the ambient matrix scales an ordered maximal minor
by `alpha^k`. -/
theorem orderedPluckerCoord_smul {k n : ℕ} (α : ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (c : Fin k → Fin n) :
    orderedPluckerCoord (α • M) c = α ^ k * orderedPluckerCoord M c := by
  unfold orderedPluckerCoord
  rw [show (α • M).submatrix id c = α • (M.submatrix id c) from by
    ext i j
    rfl]
  rw [Matrix.det_smul]
  simp [Fintype.card_fin]

/-! ## Unordered coordinates and support -/

/-- The unordered `pluckerCoord` does not depend on which proof of the
cardinality condition is supplied. -/
theorem pluckerCoord_card_proof_irrel {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (I : Finset (Fin n))
    (h₁ h₂ : I.card = k) :
    pluckerCoord M I h₁ = pluckerCoord M I h₂ := by
  cases Subsingleton.elim h₁ h₂
  rfl

/-- Scalar multiplication of the ambient matrix scales an unordered Plucker
coordinate by `alpha^k`. -/
theorem pluckerCoord_smul {k n : ℕ} (α : ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (I : Finset (Fin n)) (hI : I.card = k) :
    pluckerCoord (α • M) I hI = α ^ k * pluckerCoord M I hI := by
  unfold pluckerCoord
  let e : Fin k ≃ I := (Finset.equivFinOfCardEq hI).symm
  change ((α • M).submatrix id (fun i : Fin k => (e i).val)).det =
      α ^ k * (M.submatrix id (fun i : Fin k => (e i).val)).det
  rw [show (α • M).submatrix id (fun i : Fin k => (e i).val) =
      α • (M.submatrix id (fun i : Fin k => (e i).val)) from by
    ext i j
    rfl]
  rw [Matrix.det_smul]
  simp [Fintype.card_fin]

/-- A zero row in the ambient matrix forces every unordered Plucker coordinate
to vanish. -/
theorem pluckerCoord_zero_of_row_zero {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (I : Finset (Fin n)) (hI : I.card = k)
    (r : Fin k) (hrow : ∀ j : Fin n, M r j = 0) :
    pluckerCoord M I hI = 0 := by
  unfold pluckerCoord
  let e : Fin k ≃ I := (Finset.equivFinOfCardEq hI).symm
  change (M.submatrix id (fun i : Fin k => (e i).val)).det = 0
  exact Matrix.det_eq_zero_of_row_eq_zero r (fun j => hrow ((e j).val))

/-- The unique empty-row Plucker coordinate is the determinant of a `0 x 0`
matrix, hence `1`. -/
theorem pluckerCoord_fin_zero_eq_one {n : ℕ}
    (M : Matrix (Fin 0) (Fin n) ℝ) (I : Finset (Fin n)) (hI : I.card = 0) :
    pluckerCoord M I hI = 1 := by
  unfold pluckerCoord
  exact Matrix.det_isEmpty

/-- Support predicate for unordered Plucker coordinates. It packages the
cardinality proof together with nonvanishing. -/
def PluckerSupport {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ)
    (I : Finset (Fin n)) : Prop :=
  ∃ hI : I.card = k, pluckerCoord M I hI ≠ 0

/-- Any supported unordered Plucker coordinate has the correct cardinality. -/
theorem PluckerSupport.card {k n : ℕ} {M : Matrix (Fin k) (Fin n) ℝ}
    {I : Finset (Fin n)} (h : PluckerSupport M I) :
    I.card = k :=
  h.1

/-- If a subset has the wrong cardinality, it cannot support an unordered
Plucker coordinate. -/
theorem not_PluckerSupport_of_card_ne {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (I : Finset (Fin n))
    (hcard : I.card ≠ k) :
    ¬ PluckerSupport M I := by
  intro h
  exact hcard h.card

/-- With a fixed cardinality proof, support is equivalent to nonvanishing of the
corresponding coordinate. -/
theorem PluckerSupport_iff_ne_zero {k n : ℕ}
    (M : Matrix (Fin k) (Fin n) ℝ) (I : Finset (Fin n)) (hI : I.card = k) :
    PluckerSupport M I ↔ pluckerCoord M I hI ≠ 0 := by
  constructor
  · intro h
    obtain ⟨hJ, hne⟩ := h
    rwa [pluckerCoord_card_proof_irrel M I hJ hI] at hne
  · intro hne
    exact ⟨hI, hne⟩

/-! ## General `2 x n` Plucker relation -/

/-- Ordered `2 x 2` Plucker coordinate written directly in entries. This is the
usual `p_ij` for a `2 x n` matrix. -/
def plucker2 {n : ℕ} (M : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  M 0 i * M 1 j - M 1 i * M 0 j

/-- The entry formula agrees with the ordered determinant for the two chosen
columns. -/
theorem orderedPluckerCoord_fin2_pair {n : ℕ}
    (M : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) :
    orderedPluckerCoord M (fun r : Fin 2 => if r = 0 then i else j) = plucker2 M i j := by
  unfold orderedPluckerCoord plucker2
  rw [Matrix.det_fin_two]
  simp
  ring

/-- The direct `2 x 2` coordinate is antisymmetric. -/
theorem plucker2_swap {n : ℕ} (M : Matrix (Fin 2) (Fin n) ℝ) (i j : Fin n) :
    plucker2 M j i = - plucker2 M i j := by
  unfold plucker2
  ring

/-- A repeated column gives a zero `2 x 2` coordinate. -/
theorem plucker2_self {n : ℕ} (M : Matrix (Fin 2) (Fin n) ℝ) (i : Fin n) :
    plucker2 M i i = 0 := by
  unfold plucker2
  ring

/-- The Grassmann-Plucker relation for every ordered quadruple of columns in a
`2 x n` matrix. Repetitions are allowed, so this also covers boundary
vanishing cases used by positroid support arguments. -/
theorem plucker2_relation {n : ℕ}
    (M : Matrix (Fin 2) (Fin n) ℝ) (i j k l : Fin n) :
    plucker2 M i j * plucker2 M k l
      - plucker2 M i k * plucker2 M j l
      + plucker2 M i l * plucker2 M j k = 0 := by
  unfold plucker2
  ring

/-- The same `2 x n` relation written as a replacement scheme: if six symbols
are known to be the corresponding coordinates, the quadratic Plucker relation
follows. -/
theorem plucker2_relation_scheme {n : ℕ}
    (M : Matrix (Fin 2) (Fin n) ℝ) (i j k l : Fin n)
    (pij pik pil pjk pjl pkl : ℝ)
    (hpij : pij = plucker2 M i j) (hpik : pik = plucker2 M i k)
    (hpil : pil = plucker2 M i l) (hpjk : pjk = plucker2 M j k)
    (hpjl : pjl = plucker2 M j l) (hpkl : pkl = plucker2 M k l) :
    pij * pkl - pik * pjl + pil * pjk = 0 := by
  subst pij
  subst pik
  subst pil
  subst pjk
  subst pjl
  subst pkl
  exact plucker2_relation M i j k l

end

end PallLean.Paper93.DeepMath.PathB.Positroid
