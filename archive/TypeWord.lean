/-
  TypeWord.lean — Ordered derivative-type words and their histograms

  A TypeWord is the ordered sequence of derivative types applied in
  a block-admissible derivative list. The histogram (profile) of a
  TypeWord counts occurrences of each type.

  Paper: §9.2 (P7 local word normal forms), Definition 21.
-/
import PallLean.DerivType
import Mathlib.Tactic

namespace TypeWord

open DerivType

/-- An ordered derivative-type word of length κ -/
abbrev TypeWord := List DerivType

/-- Profile: histogram of a type word.
    Counts occurrences of each derivative type. -/
def profileOf (w : TypeWord) : DerivType → ℕ :=
  fun τ => w.count τ

/-- Profile is a function DerivType → ℕ -/
abbrev Profile := DerivType → ℕ

/-- Total mass of a profile = length of any word with that profile -/
def totalMass (h : Profile) : ℕ :=
  (Finset.univ : Finset DerivType).sum h

/-- Profile sum equals word length -/
-- Helper: for a finite type, sum of List.count over all elements = length
theorem profileOf_sum_eq_length (w : TypeWord) :
    totalMass (profileOf w) = w.length := by
  -- Prove for DerivType specifically by exhaustive case analysis
  unfold totalMass profileOf
  induction w with
  | nil => simp
  | cons x xs ih =>
    rw [show (Finset.univ : Finset DerivType) =
      {.dz, .dv1, .dv2, .dv3} from by ext x; cases x <;> simp]
    simp only [Finset.sum_cons, Finset.sum_empty, Finset.mem_cons,
      Finset.mem_singleton, not_or, List.length_cons, List.count_cons]
    -- After simp, we have sums of if-then-else expressions
    -- Each List.count_cons gives (if x == a then count+1 else count)
    -- Exactly one matches, giving +1 total
    -- Rewrite ih to expose the sum for xs
    -- ih : ∑ over {dz, dv1, dv2, dv3} count = xs.length
    -- Goal after outer simp: various count_cons if-then-else + 0 = xs.length + 1
    -- The `ih` in the rewritten univ form gives us what omega needs
    rw [show (Finset.univ : Finset DerivType) =
      {.dz, .dv1, .dv2, .dv3} from by ext x; cases x <;> simp] at ih
    simp only [Finset.sum_insert (by simp [DerivType.noConfusion] : DerivType.dz ∉
      ({.dv1, .dv2, .dv3} : Finset DerivType)),
      Finset.sum_insert (by simp [DerivType.noConfusion] : DerivType.dv1 ∉
      ({.dv2, .dv3} : Finset DerivType)),
      Finset.sum_insert (by simp [DerivType.noConfusion] : DerivType.dv2 ∉
      ({.dv3} : Finset DerivType)),
      Finset.sum_singleton] at ih ⊢
    cases x <;> simp [List.count_cons, beq_iff_eq] <;> omega

/-- Number of distinct profiles with total mass ≤ R:
    weak compositions of ≤ R into 4 bins ≤ C(R+4, 4). -/
theorem profile_count_le_choose (R : ℕ) :
    ∀ (S : Finset Profile),
      (∀ h ∈ S, totalMass h ≤ R) →
      S.card ≤ Nat.choose (R + 4) 4 := by
  sorry  -- Stars-and-bars counting

end TypeWord
