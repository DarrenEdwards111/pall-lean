/-
  MobiusInversion.lean -- Mobius inversion on the Boolean lattice (PROVED)

  Paper-faithful: this is the inclusion-exclusion identity underlying
  the paper's evaluation-matrix / annihilator argument (§8.6).

  Key theorem: For T ⊆ Fin w,
    ∑_{S ⊇ T} (-1)^{w-|S|} = δ_{T, univ}

  Proof via Finset.sum_involution with toggle involution S ↦ S △ {i}
  for any i ∉ T. Each pair (S, S △ {i}) contributes 0.
-/
import Mathlib.Tactic

namespace MobiusInversion

open Finset

/-- Toggle element i in/out of S. -/
def toggle {α : Type*} [DecidableEq α] (i : α) (S : Finset α) : Finset α :=
  if i ∈ S then S.erase i else insert i S

lemma toggle_invol {α : Type*} [DecidableEq α] (i : α) (S : Finset α) :
    toggle i (toggle i S) = S := by
  ext j; unfold toggle; split_ifs with h1 h2 h3 <;> simp_all [mem_erase, mem_insert]

lemma toggle_ne {α : Type*} [DecidableEq α] (i : α) (S : Finset α) :
    toggle i S ≠ S := by
  unfold toggle; split_ifs with h <;> intro heq
  · have := heq ▸ h; simp [mem_erase] at this
  · have := heq ▸ mem_insert_self i S; contradiction

lemma toggle_card_mem {α : Type*} [DecidableEq α] (i : α) (S : Finset α) (h : i ∈ S) :
    (toggle i S).card = S.card - 1 := by
  unfold toggle; rw [if_pos h]; exact card_erase_of_mem h

lemma toggle_card_not_mem {α : Type*} [DecidableEq α] (i : α) (S : Finset α) (h : i ∉ S) :
    (toggle i S).card = S.card + 1 := by
  unfold toggle; rw [if_neg h]; exact card_insert_of_notMem h

lemma toggle_subset_superset {w : ℕ} {T : Finset (Fin w)} {i : Fin w} (hiT : i ∉ T)
    {S : Finset (Fin w)} (hTS : T ⊆ S) : T ⊆ toggle i S := by
  intro j hj; unfold toggle; split_ifs with h
  · exact mem_erase.mpr ⟨by rintro rfl; exact hiT hj, hTS hj⟩
  · exact mem_insert.mpr (Or.inr (hTS hj))

/-- PROVED: For T ⊊ univ, the alternating superset sum is 0.
    Proof: toggle involution S ↦ S △ {i} pairs terms that cancel. -/
theorem superset_mobius_sum_zero (w : ℕ) (T : Finset (Fin w)) (hT : T ≠ univ) :
    ∑ S ∈ (univ : Finset (Fin w)).powerset.filter (T ⊆ ·),
      (-1 : ℚ) ^ (w - S.card) = 0 := by
  obtain ⟨i, hiT⟩ : ∃ i : Fin w, i ∉ T := by
    by_contra h; push_neg at h; exact hT (eq_univ_of_forall h)
  apply Finset.sum_involution (fun S _ => toggle i S)
  · -- f(S) + f(toggle i S) = 0
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    have hSw : S.card ≤ w := by
      have := card_le_card hS.1; rwa [card_univ, Fintype.card_fin] at this
    by_cases h : i ∈ S
    · rw [toggle_card_mem i S h]
      have hpos : 1 ≤ S.card := card_pos.mpr ⟨i, h⟩
      rw [show w - (S.card - 1) = (w - S.card) + 1 from by omega, pow_succ]; ring
    · rw [toggle_card_not_mem i S h]
      have hlt : S.card + 1 ≤ w := by
        have := card_le_card (show insert i S ⊆ univ from subset_univ _)
        rw [card_insert_of_notMem h, card_univ, Fintype.card_fin] at this; exact this
      rw [show w - S.card = (w - (S.card + 1)) + 1 from by omega, pow_succ]; ring
  · intro S _ _; exact toggle_ne i S
  · intro S hS
    simp only [mem_filter, mem_powerset] at hS ⊢
    exact ⟨subset_univ _, toggle_subset_superset hiT hS.2⟩
  · intro S _; exact toggle_invol i S

/-- PROVED: Superset Mobius sum = δ_{T, univ}. -/
theorem superset_mobius_sum (w : ℕ) (T : Finset (Fin w)) :
    ∑ S ∈ (univ : Finset (Fin w)).powerset.filter (T ⊆ ·),
      (-1 : ℚ) ^ (w - S.card) = if T = univ then 1 else 0 := by
  split_ifs with hT
  · subst hT
    have : (univ : Finset (Fin w)).powerset.filter ((univ : Finset (Fin w)) ⊆ ·) = {univ} := by
      ext S; simp [mem_filter]
    rw [this, sum_singleton, card_univ, Fintype.card_fin, Nat.sub_self, pow_zero]
  · exact superset_mobius_sum_zero w T hT

end MobiusInversion
