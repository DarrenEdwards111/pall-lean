import GodMoveCachedDiscoveryBasis
import GodMoveTrackedRowPrecision

/-!
# Precision preserved by arbitrary Boolean-row insertion histories

`Ready` records both a Boolean-generated span and precision of each stored
orthogonal row. The latter does not follow merely from the span: arbitrary
orthogonal bases can be rescaled. It is preserved here by the actual cached
insertion, whose new row is the unique orthogonal residual of a Boolean row.

A finite independent Boolean subfamily and the integer Gram formula bound that
residual directly. No precision recurrence is iterated through the history, and
no caller supplies precision for a newly inserted row. These are canonical
rational-value bounds, not a machine-runtime theorem.
-/

namespace GodMoveCachedBasisPrecision

open GodMoveCachedDiscoveryBasis
open GodMoveTrackedOrthogonalization (Row rowValue)
open GodMoveRationalRowBasis (Vec rowSpan rowListSpan selectRows)
open GodMoveTrackedRowPrecision
open GodMoveGramPrecision (BooleanEntries rationalMatrix)
open GodMoveRationalPrecisionArithmetic
open scoped BigOperators

def BooleanRow {s : ℕ} (v : Vec s) : Prop := ∀ j, v j = 0 ∨ v j = 1

/-- A finite Boolean generating history; neither the generators nor their
number are assumed to be linearly independent. -/
def BooleanGenerated {s : ℕ} (W : Submodule ℚ (Vec s)) : Prop :=
  ∃ xs : List (Unit × Vec s),
    (∀ x ∈ xs, BooleanRow x.2) ∧ W = rowListSpan xs

theorem booleanGenerated_bot (s : ℕ) : BooleanGenerated (⊥ : Submodule ℚ (Vec s)) := by
  refine ⟨[], ?_, ?_⟩
  · simp
  · simp

theorem BooleanGenerated.sup_single {s : ℕ} {W : Submodule ℚ (Vec s)}
    (h : BooleanGenerated W) (v : Vec s) (hv : BooleanRow v) :
    BooleanGenerated (W ⊔ Submodule.span ℚ {v}) := by
  obtain ⟨xs, hx, hW⟩ := h
  refine ⟨((), v) :: xs, ?_, ?_⟩
  · intro x hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hv
    · exact hx x hmem
  · rw [GodMoveRationalRowBasis.rowListSpan_cons, hW, sup_comm]

/-- Select an independent subfamily of the original Boolean generators.
This theorem supplies all premises of the rectangular integer Gram formula. -/
theorem BooleanGenerated.exists_independent {s : ℕ} {W : Submodule ℚ (Vec s)}
    (h : BooleanGenerated W) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin s) ℤ),
      r ≤ s ∧ BooleanEntries R ∧ LinearIndependent ℚ (rationalMatrix R) ∧
        W = Submodule.span ℚ (Set.range (rationalMatrix R)) := by
  obtain ⟨xs, hx, hW⟩ := h
  let ys := selectRows xs
  let F : Fin ys.length → Vec s := fun i => (ys.get i).2
  have hF : ∀ i, BooleanRow (F i) := by
    intro i
    apply hx (ys.get i)
    exact GodMoveRationalRowBasis.selectRows_subset xs _ (List.get_mem _ _)
  let R : Matrix (Fin ys.length) (Fin s) ℤ :=
    fun i j => if F i j = 0 then 0 else 1
  have hR : BooleanEntries R := by
    intro i j
    dsimp [R]
    split <;> simp
  have hcast : rationalMatrix R = F := by
    funext i j
    rcases hF i j with hz | ho
    · simp [rationalMatrix, R, hz]
    · simp [rationalMatrix, R, ho]
  refine ⟨ys.length, R, GodMoveRationalRowBasis.selectRows_length_le xs, hR, ?_, ?_⟩
  · rw [hcast]
    exact GodMoveRationalRowBasis.selectRows_linearIndependent xs
  · rw [hcast, hW, ← GodMoveRationalRowBasis.selectRows_span xs]
    exact GodMoveRationalRowBasis.rowListSpan_eq_span_get ys

def rowBits (s : ℕ) : ℕ := 5 * (s + 1) ^ 2
def normBits (s : ℕ) : ℕ := (2 * rowBits s + 1) * (s + 1)

structure Ready {s : ℕ} (B : CachedBasis s) : Prop where
  generated : BooleanGenerated (rowSpan B.toRowBasis)
  rows : ∀ (i : Fin B.count) (j : Fin s), BitBound B.rows[i][j] (rowBits s)

theorem empty_ready (s : ℕ) : Ready (empty s) where
  generated := by simpa only [empty_value, GodMoveRationalRowBasis.empty_span] using
    booleanGenerated_bot s
  rows := fun i => Fin.elim0 i

/-- Any orthogonal basis of a Boolean-generated span has the same bounded
residual on a Boolean input, even if its existing rows were rescaled. -/
theorem residual_integerRowBound {s : ℕ} (B : CachedBasis s)
    (hB : BooleanGenerated (rowSpan B.toRowBasis)) (v : Row s)
    (hv : BooleanRow (rowValue v)) :
    IntegerRowBound (rowValue (residual B v).value) (s * gramBound s) (gramBound s) := by
  obtain ⟨r, R, hrs, hR, hLI, hspan⟩ := hB.exists_independent
  let z : Fin s → ℤ := fun j => if v[j] = 0 then 0 else 1
  have hz : ∀ j, z j = 0 ∨ z j = 1 := by
    intro j
    dsimp [z]
    split <;> simp
  have hcast : (fun j => (z j : ℚ)) = rowValue v := by
    funext j
    rcases hv j with h | h <;> simp [z, rowValue] at h ⊢ <;> simp [h]
  rw [residual_value]
  rw [← hcast]
  exact residual_boolean_integerRowBound R hR hLI hrs B.toRowBasis hspan z hz

theorem residual_bitBound {s : ℕ} (B : CachedBasis s) (hB : Ready B)
    (v : Row s) (hv : BooleanRow (rowValue v)) (j : Fin s) :
    BitBound (residual B v).value[j] (rowBits s) := by
  have h := (residual_integerRowBound B hB.generated v hv).num_den_le j
  have hb := row_bounds_le_uniform s
  exact ⟨h.1.trans hb.1, h.2.trans hb.2⟩

/-- Readiness is preserved on both accepted and rejected Boolean insertions. -/
theorem insert_ready {s : ℕ} (B : CachedBasis s) (hB : Ready B)
    (v : Row s) (hv : BooleanRow (rowValue v)) : Ready (insert B v).value := by
  constructor
  · rw [insert_span]
    exact hB.generated.sup_single (rowValue v) hv
  · change ∀ (i : Fin (insert B v).value.toRowBasis.count) (j : Fin s),
      BitBound ((insert B v).value.toRowBasis.rows i j) (rowBits s)
    rw [insert_value]
    by_cases hz : GodMoveRationalRowBasis.residual B.toRowBasis (rowValue v) = 0
    · have he : GodMoveRationalRowBasis.insert B.toRowBasis (rowValue v) = B.toRowBasis :=
        dif_pos hz
      rw [he]
      exact hB.rows
    · have he : GodMoveRationalRowBasis.insert B.toRowBasis (rowValue v) =
          GodMoveRationalRowBasis.grow B.toRowBasis (rowValue v) hz := dif_neg hz
      rw [he]
      intro i j
      refine Fin.lastCases ?_ (fun l => ?_) i
      · have hr := residual_bitBound B hB v hv j
        change BitBound (rowValue (residual B v).value j) (rowBits s) at hr
        rw [residual_value] at hr
        simpa [GodMoveRationalRowBasis.grow] using hr
      · simpa [GodMoveRationalRowBasis.grow] using hB.rows l j

theorem norms_bitBound {s : ℕ} (B : CachedBasis s) (hB : Ready B) (i : Fin B.count) :
    BitBound B.norms[i] (normBits s) := by
  rw [B.norms_correct]
  have h := dot_bitBound Finset.univ (fun j : Fin s => B.rows[i][j])
    (fun j : Fin s => B.rows[i][j]) (rowBits s) (rowBits s)
    (fun j _ => hB.rows i j) (fun j _ => hB.rows i j)
  apply h.mono
  simp only [Finset.card_univ, Fintype.card_fin]
  unfold normBits
  nlinarith

theorem stored_row_sizes {s : ℕ} (B : CachedBasis s) (hB : Ready B)
    (i : Fin B.count) (j : Fin s) :
    B.rows[i][j].num.natAbs.size ≤ rowBits s + 1 ∧
      B.rows[i][j].den.size ≤ rowBits s + 1 := (hB.rows i j).canonical_sizes

theorem stored_norm_sizes {s : ℕ} (B : CachedBasis s) (hB : Ready B) (i : Fin B.count) :
    B.norms[i].num.natAbs.size ≤ normBits s + 1 ∧
      B.norms[i].den.size ≤ normBits s + 1 := (norms_bitBound B hB i).canonical_sizes

end GodMoveCachedBasisPrecision

#print axioms GodMoveCachedBasisPrecision.BooleanGenerated.exists_independent
#print axioms GodMoveCachedBasisPrecision.empty_ready
#print axioms GodMoveCachedBasisPrecision.residual_integerRowBound
#print axioms GodMoveCachedBasisPrecision.residual_bitBound
#print axioms GodMoveCachedBasisPrecision.insert_ready
#print axioms GodMoveCachedBasisPrecision.norms_bitBound
#print axioms GodMoveCachedBasisPrecision.stored_row_sizes
#print axioms GodMoveCachedBasisPrecision.stored_norm_sizes
