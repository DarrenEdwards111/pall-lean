import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWeakeningDAG
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRestrictDerivation

/-!
# Combining two unit-clause derivations into a refutation

The recombination step of the fat-clause recursion: given weakening-DAGs deriving
the unit clauses `{ℓ}` and `{¬ℓ}` over the same axioms, concatenate them and resolve
the two units to obtain a refutation of `∅`, of width `≤ max` of the two and one
more clause.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {Edge : Type*} [DecidableEq Edge] {Axiom : ResolutionClause (TLit Edge) → Prop}

/-- Concatenated clause array: `D1`, then `D2`, then `∅`. -/
def combineClause {n1 n2 : ℕ} (D1 : WeakeningDAG tcompl Axiom n1)
    (D2 : WeakeningDAG tcompl Axiom n2) :
    Fin (n1 + n2 + 1) → ResolutionClause (TLit Edge) := fun i =>
  if h1 : (i : ℕ) < n1 then D1.clause ⟨i, h1⟩
  else if h2 : (i : ℕ) < n1 + n2 then D2.clause ⟨(i : ℕ) - n1, by omega⟩
  else ∅

theorem combineClause_d1 {n1 n2 : ℕ} (D1 : WeakeningDAG tcompl Axiom n1)
    (D2 : WeakeningDAG tcompl Axiom n2) (i : Fin (n1 + n2 + 1)) (h : (i : ℕ) < n1) :
    combineClause D1 D2 i = D1.clause ⟨i, h⟩ := dif_pos h

theorem combineClause_d2 {n1 n2 : ℕ} (D1 : WeakeningDAG tcompl Axiom n1)
    (D2 : WeakeningDAG tcompl Axiom n2) (i : Fin (n1 + n2 + 1)) (h1 : ¬ (i : ℕ) < n1)
    (h2 : (i : ℕ) < n1 + n2) :
    combineClause D1 D2 i = D2.clause ⟨(i : ℕ) - n1, by omega⟩ := by
  unfold combineClause; rw [dif_neg h1, dif_pos h2]

theorem combineClause_last {n1 n2 : ℕ} (D1 : WeakeningDAG tcompl Axiom n1)
    (D2 : WeakeningDAG tcompl Axiom n2) (i : Fin (n1 + n2 + 1)) (h : (i : ℕ) = n1 + n2) :
    combineClause D1 D2 i = ∅ := by
  unfold combineClause; rw [dif_neg (by omega), dif_neg (by omega)]

/-- **Combine.**  Two weakening-DAGs deriving `{ℓ}` and `{ℓ}`'s complement resolve to
a refutation of `∅`. -/
def WeakeningDAG.combine {n1 n2 : ℕ} (ℓ : TLit Edge)
    (D1 : WeakeningDAG tcompl Axiom n1) (D2 : WeakeningDAG tcompl Axiom n2)
    (i1 : Fin n1) (hi1 : D1.clause i1 = {ℓ})
    (i2 : Fin n2) (hi2 : D2.clause i2 = {tcompl ℓ}) :
    WeakeningDAG tcompl Axiom (n1 + n2 + 1) where
  clause := combineClause D1 D2
  valid i := by
    have hn1 : 0 < n1 := lt_of_le_of_lt (Nat.zero_le _) i1.2
    have hn2 : 0 < n2 := lt_of_le_of_lt (Nat.zero_le _) i2.2
    rcases lt_trichotomy (i : ℕ) n1 with h1 | h1 | h1
    · -- inside D1
      rw [combineClause_d1 D1 D2 i h1]
      rcases D1.valid ⟨i, h1⟩ with hax | ⟨a, b, p, ha, hb, he⟩ | ⟨a, ha, hsub⟩
      · exact Or.inl hax
      · have ha' : (a : ℕ) < (i : ℕ) := ha
        have hb' : (b : ℕ) < (i : ℕ) := hb
        refine Or.inr (Or.inl ⟨⟨a, by omega⟩, ⟨b, by omega⟩, p,
          Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), ?_⟩)
        rw [combineClause_d1 D1 D2 _ (by exact a.2), combineClause_d1 D1 D2 _ (by exact b.2)]
        exact he
      · have ha' : (a : ℕ) < (i : ℕ) := ha
        refine Or.inr (Or.inr ⟨⟨a, by omega⟩, Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), ?_⟩)
        rw [combineClause_d1 D1 D2 _ (by exact a.2)]; exact hsub
    · -- i = n1
      rw [combineClause_d2 D1 D2 i (by omega) (by omega)]
      rcases D2.valid ⟨(i : ℕ) - n1, by omega⟩ with hax | ⟨a, b, p, ha, hb, he⟩ | ⟨a, ha, hsub⟩
      · exact Or.inl hax
      · have ha' : (a : ℕ) < (i : ℕ) - n1 := ha
        have hb' : (b : ℕ) < (i : ℕ) - n1 := hb
        refine Or.inr (Or.inl ⟨⟨n1 + a, by omega⟩, ⟨n1 + b, by omega⟩, p,
          Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), ?_⟩)
        rw [combineClause_d2 D1 D2 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
          combineClause_d2 D1 D2 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
          show (⟨n1 + (a:ℕ) - n1, by omega⟩ : Fin n2) = a from Fin.ext (by simp only [Fin.val_mk]; omega),
          show (⟨n1 + (b:ℕ) - n1, by omega⟩ : Fin n2) = b from Fin.ext (by simp only [Fin.val_mk]; omega)]
        exact he
      · have ha' : (a : ℕ) < (i : ℕ) - n1 := ha
        refine Or.inr (Or.inr ⟨⟨n1 + a, by omega⟩, Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), ?_⟩)
        rw [combineClause_d2 D1 D2 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
          show (⟨n1 + (a:ℕ) - n1, by omega⟩ : Fin n2) = a from Fin.ext (by simp only [Fin.val_mk]; omega)]
        exact hsub
    · rcases lt_trichotomy (i : ℕ) (n1 + n2) with h2 | h2 | h2
      · -- still in D2
        rw [combineClause_d2 D1 D2 i (by omega) h2]
        rcases D2.valid ⟨(i : ℕ) - n1, by omega⟩ with hax | ⟨a, b, p, ha, hb, he⟩ | ⟨a, ha, hsub⟩
        · exact Or.inl hax
        · have ha' : (a : ℕ) < (i : ℕ) - n1 := ha
          have hb' : (b : ℕ) < (i : ℕ) - n1 := hb
          refine Or.inr (Or.inl ⟨⟨n1 + a, by omega⟩, ⟨n1 + b, by omega⟩, p,
            Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), ?_⟩)
          rw [combineClause_d2 D1 D2 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
            combineClause_d2 D1 D2 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
            show (⟨n1 + (a:ℕ) - n1, by omega⟩ : Fin n2) = a from Fin.ext (by simp only [Fin.val_mk]; omega),
            show (⟨n1 + (b:ℕ) - n1, by omega⟩ : Fin n2) = b from Fin.ext (by simp only [Fin.val_mk]; omega)]
          exact he
        · have ha' : (a : ℕ) < (i : ℕ) - n1 := ha
          refine Or.inr (Or.inr ⟨⟨n1 + a, by omega⟩, Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), ?_⟩)
          rw [combineClause_d2 D1 D2 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
            show (⟨n1 + (a:ℕ) - n1, by omega⟩ : Fin n2) = a from Fin.ext (by simp only [Fin.val_mk]; omega)]
          exact hsub
      · -- i = n1 + n2: the final resolvent of {ℓ} and {tcompl ℓ}
        rw [combineClause_last D1 D2 i h2]
        refine Or.inr (Or.inl ⟨⟨i1, by omega⟩, ⟨n1 + i2, by omega⟩, ℓ,
          Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega),
          Fin.lt_def.mpr (by simp only [Fin.val_mk]; omega), ?_⟩)
        rw [combineClause_d1 D1 D2 _ (by exact i1.2),
          combineClause_d2 D1 D2 _ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega),
          show (⟨(i1:ℕ), by exact i1.2⟩ : Fin n1) = i1 from Fin.ext rfl,
          show (⟨n1 + (i2:ℕ) - n1, by omega⟩ : Fin n2) = i2 from Fin.ext (by simp only [Fin.val_mk]; omega),
          hi1, hi2]
        ext x
        simp [ResolutionClause.resolvent, TseitinRestriction.ne_tcompl ℓ,
          (TseitinRestriction.ne_tcompl ℓ).symm]
      · omega

/-- The combined refutation derives `∅` at its last index. -/
theorem WeakeningDAG.combine_root {n1 n2 : ℕ} (ℓ : TLit Edge)
    (D1 : WeakeningDAG tcompl Axiom n1) (D2 : WeakeningDAG tcompl Axiom n2)
    (i1 : Fin n1) (hi1 : D1.clause i1 = {ℓ})
    (i2 : Fin n2) (hi2 : D2.clause i2 = {tcompl ℓ}) :
    (WeakeningDAG.combine ℓ D1 D2 i1 hi1 i2 hi2).clause ⟨n1 + n2, by omega⟩
      = (∅ : ResolutionClause (TLit Edge)) :=
  combineClause_last D1 D2 ⟨n1 + n2, by omega⟩ rfl

/-- Every clause of the combined refutation is within the common width bound of the
two inputs (the new clause `∅` has width `0`). -/
theorem WeakeningDAG.combine_width_le {n1 n2 : ℕ} (ℓ : TLit Edge)
    (D1 : WeakeningDAG tcompl Axiom n1) (D2 : WeakeningDAG tcompl Axiom n2)
    (i1 : Fin n1) (hi1 : D1.clause i1 = {ℓ})
    (i2 : Fin n2) (hi2 : D2.clause i2 = {tcompl ℓ}) {B : ℕ}
    (hb1 : ∀ j, ResolutionClause.width (D1.clause j) ≤ B)
    (hb2 : ∀ j, ResolutionClause.width (D2.clause j) ≤ B)
    (i : Fin (n1 + n2 + 1)) :
    ResolutionClause.width ((WeakeningDAG.combine ℓ D1 D2 i1 hi1 i2 hi2).clause i) ≤ B := by
  have hn2 : 0 < n2 := lt_of_le_of_lt (Nat.zero_le _) i2.2
  show ResolutionClause.width (combineClause D1 D2 i) ≤ B
  rcases lt_trichotomy (i : ℕ) n1 with h | h | h
  · rw [combineClause_d1 D1 D2 i h]; exact hb1 _
  · rw [combineClause_d2 D1 D2 i (by omega) (by omega)]; exact hb2 _
  · rcases lt_trichotomy (i : ℕ) (n1 + n2) with h2 | h2 | h2
    · rw [combineClause_d2 D1 D2 i (by omega) h2]; exact hb2 _
    · rw [combineClause_last D1 D2 i h2]; simp [ResolutionClause.width]
    · omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.combine
#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.combine_root
#print axioms PallLean.Paper93.DeepMath.PathB.WeakeningDAG.combine_width_le
