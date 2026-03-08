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
theorem profileOf_sum_eq_length (w : TypeWord) :
    totalMass (profileOf w) = w.length := by
  simp only [totalMass, profileOf]
  -- sum of counts over all types = total length
  rw [show (Finset.univ : Finset DerivType) =
    {.dz, .dv1, .dv2, .dv3} from by ext x; fin_cases x <;> simp]
  simp [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton]
  -- count dz + count dv1 + count dv2 + count dv3 = length
  -- This is List.length_eq_countP_add_countP generalized
  sorry

/-- Number of distinct profiles with total mass ≤ R:
    weak compositions of ≤ R into 4 bins ≤ C(R+4, 4). -/
theorem profile_count_le_choose (R : ℕ) :
    ∀ (S : Finset Profile),
      (∀ h ∈ S, totalMass h ≤ R) →
      S.card ≤ Nat.choose (R + 4) 4 := by
  sorry  -- Stars-and-bars counting

end TypeWord
