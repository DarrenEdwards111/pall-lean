import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafClauses

/-!
# Order-preserving normalization for canonical DNF trees

The multi-switching encoder needs duplicate-free clause lists.  `List.eraseDups` supplies that
invariant without changing the canonical first-active-term walk: it retains the first occurrence
of every clause.  This module is deliberately below both the quantitative iteration and layered
bridge modules so they can share the same normalization facts.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- Membership is unchanged by the order-preserving duplicate eraser. -/
theorem mem_eraseDups_iff {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ l : List α, a ∈ l.eraseDups ↔ a ∈ l
  | [] => by simp
  | b :: bs => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff]
      by_cases h : a = b <;> simp [h]
termination_by l => l.length
decreasing_by exact lt_of_le_of_lt (List.length_filter_le _ _) (by simp)

/-- The order-preserving duplicate eraser produces a duplicate-free list. -/
theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ l : List α, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [mem_eraseDups_iff]
        simp
      · exact eraseDups_nodup (as.filter fun b => !b == a)
termination_by l => l.length
decreasing_by exact lt_of_le_of_lt (List.length_filter_le _ _) (by simp)

theorem eraseDups_length_le {α : Type} [BEq α] (l : List α) :
    l.eraseDups.length ≤ l.length := by
  cases l with
  | nil => simp
  | cons a as =>
    rw [List.eraseDups_cons]
    simp only [List.length_cons]
    exact Nat.succ_le_succ <| le_trans (eraseDups_length_le _)
      (List.length_filter_le _ _)
termination_by l.length
decreasing_by exact lt_of_le_of_lt (List.length_filter_le _ _) (by simp)

/-- Removing later copies of `a` preserves the first element satisfying `p` when `a` fails `p`. -/
theorem find?_filter_ne_of_false {α : Type} [BEq α] [LawfulBEq α]
    (p : α → Bool) (a : α) (ha : p a = false) :
    ∀ l : List α, (l.filter fun b => !b == a).find? p = l.find? p
  | [] => by simp
  | b :: bs => by
      by_cases hba : b = a
      · subst b
        simp [ha, find?_filter_ne_of_false p a ha bs]
      · by_cases hb : p b = true
        · simp [hba, hb]
        · have hbf : p b = false := Bool.eq_false_of_not_eq_true hb
          simp [hba, hbf, find?_filter_ne_of_false p a ha bs]

/-- `eraseDups` preserves the first satisfying element, not merely membership. -/
theorem find?_eraseDups {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) :
    ∀ l : List α, l.eraseDups.find? p = l.find? p
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons]
      by_cases ha : p a = true
      · simp [ha]
      · have haf : p a = false := Bool.eq_false_of_not_eq_true ha
        simp only [List.find?_cons, haf, Bool.false_eq_true, if_false]
        rw [find?_eraseDups p, find?_filter_ne_of_false p a haf]
termination_by l => l.length
decreasing_by exact lt_of_le_of_lt (List.length_filter_le _ _) (by simp)

/-- Order-preserving normalization leaves the DNF satisfied test unchanged. -/
theorem anyTermSat_eraseDups {n : ℕ} (cs : List (Clause n)) (σ : Restriction n) :
    anyTermSat cs.eraseDups σ = anyTermSat cs σ := by
  apply Bool.eq_iff_iff.mpr
  simp only [anyTermSat, List.any_eq_true]
  constructor <;> rintro ⟨T, hT, hsat⟩
  · exact ⟨T, (mem_eraseDups_iff T _).mp hT, hsat⟩
  · exact ⟨T, (mem_eraseDups_iff T _).mpr hT, hsat⟩

/-- Order-preserving normalization leaves the first active term unchanged. -/
theorem activeTerm_eraseDups {n : ℕ} (cs : List (Clause n)) (σ : Restriction n) :
    activeTerm cs.eraseDups σ = activeTerm cs σ := by
  unfold activeTerm
  rw [anyTermSat_eraseDups]
  cases h : anyTermSat cs σ <;> simp [h, find?_eraseDups]

/-- Normalization preserves the complete canonical decision tree at every fuel and restriction. -/
theorem canonicalDT_eraseDups {n : ℕ} (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Restriction n), canonicalDT cs.eraseDups F σ = canonicalDT cs F σ := by
  intro F
  induction F with
  | zero =>
      intro σ
      simp only [canonicalDT]
      rw [anyTermSat_eraseDups]
  | succ F ih =>
      intro σ
      simp only [canonicalDT]
      rw [anyTermSat_eraseDups, activeTerm_eraseDups]
      cases hsat : anyTermSat cs σ with
      | true => simp
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases hT : activeTerm cs σ with
          | none => rfl
          | some T =>
              cases hh : (freeLits σ T).head? with
              | none => simp [hh]
              | some ell =>
                  simp only [hh]
                  rw [ih (fixVar σ (litVar ell) false),
                    ih (fixVar σ (litVar ell) true)]

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingQuantitativeIteration.canonicalDT_eraseDups
