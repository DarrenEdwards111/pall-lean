import Mathlib

/-!
# GF(2) Parity System Satisfiability

For a connected graph with even total target parity, the vertex parity
system is always satisfiable.
-/

namespace GF2

open Finset

/-- The parity of vertex v under edge assignment β. -/
def vertexParity (n m : ℕ) (src tgt : Fin m → Fin n) (β : Fin m → Bool)
    (v : Fin n) : ℕ :=
  (univ.filter fun e : Fin m =>
    (src e = v ∨ tgt e = v) ∧ β e = true).card % 2

/-- The target value as 0 or 1. -/
def targetVal (target : Fin n → Bool) (v : Fin n) : ℕ :=
  if target v then 1 else 0

/-- All vertices satisfied. -/
def AllSatisfied (n m : ℕ) (src tgt : Fin m → Fin n) (target : Fin n → Bool)
    (β : Fin m → Bool) : Prop :=
  ∀ v, vertexParity n m src tgt β v = targetVal target v

/-- The number of unsatisfied vertices (the defect). -/
noncomputable def defect (n m : ℕ) (src tgt : Fin m → Fin n)
    (target : Fin n → Bool) (β : Fin m → Bool) : ℕ :=
  (univ.filter fun v : Fin n =>
    vertexParity n m src tgt β v ≠ targetVal target v).card

/-- Total vertex parity is always even (each edge has 2 endpoints). -/
theorem total_parity_even (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e : Fin m, src e ≠ tgt e) (β : Fin m → Bool) :
    (univ.filter fun v : Fin n =>
      vertexParity n m src tgt β v = 1).card % 2 = 0 := by
  sorry

/-- The defect is always even when targets have even parity. -/
theorem defect_parity (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e, src e ≠ tgt e) (target : Fin n → Bool)
    (h_even : (univ.filter fun v => target v = true).card % 2 = 0)
    (β : Fin m → Bool) :
    defect n m src tgt target β % 2 = 0 := by
  sorry

/-- Reachability via edges. -/
inductive Reachable (n m : ℕ) (src tgt : Fin m → Fin n) :
    Fin n → Fin n → Prop where
  | refl (v : Fin n) : Reachable n m src tgt v v
  | step (u v w : Fin n) (e : Fin m) :
      Reachable n m src tgt u v →
      (src e = v ∧ tgt e = w ∨ src e = w ∧ tgt e = v) →
      Reachable n m src tgt u w

def Connected (n m : ℕ) (src tgt : Fin m → Fin n) : Prop :=
  ∀ u v : Fin n, Reachable n m src tgt u v

/-- Flipping an edge changes parity at its endpoints and nowhere else. -/
theorem flip_edge_parity (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e, src e ≠ tgt e)
    (β : Fin m → Bool) (e₀ : Fin m) (v : Fin n) :
    vertexParity n m src tgt (Function.update β e₀ (!β e₀)) v =
    if src e₀ = v ∨ tgt e₀ = v then (vertexParity n m src tgt β v + 1) % 2
    else vertexParity n m src tgt β v := by
  simp only [vertexParity]
  split_ifs with h_inc
  · -- e₀ incident to v: exactly one element changes membership
    set S_old := univ.filter fun e : Fin m =>
      (src e = v ∨ tgt e = v) ∧ β e = true
    set S_new := univ.filter fun e : Fin m =>
      (src e = v ∨ tgt e = v) ∧ Function.update β e₀ (!β e₀) e = true
    have h_other : ∀ e : Fin m, e ≠ e₀ → (e ∈ S_new ↔ e ∈ S_old) := by
      intro e he
      simp only [S_new, S_old, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.update_apply, if_neg he]
    cases hb : β e₀ with
    | false =>
      have h_not_old : e₀ ∉ S_old := by simp [S_old, Finset.mem_filter, hb]
      have h_in_new : e₀ ∈ S_new := by
        simp [S_new, Finset.mem_filter, Function.update_self, hb, h_inc]
      have h_eq : S_new = insert e₀ S_old := by
        ext e; simp only [Finset.mem_insert]
        constructor
        · intro he; by_cases h : e = e₀
          · exact Or.inl h
          · exact Or.inr ((h_other e h).mp he)
        · intro he; rcases he with rfl | he
          · exact h_in_new
          · exact (h_other e (by intro h; subst h; exact h_not_old he)).mpr he
      rw [h_eq]; simp [h_not_old]
    | true =>
      have h_in_old : e₀ ∈ S_old := by simp [S_old, Finset.mem_filter, hb, h_inc]
      have h_not_new : e₀ ∉ S_new := by
        simp [S_new, Finset.mem_filter, Function.update_self, hb]
      have h_eq : S_old = insert e₀ S_new := by
        ext e; simp only [Finset.mem_insert]
        constructor
        · intro he; by_cases h : e = e₀
          · exact Or.inl h
          · exact Or.inr ((h_other e h).mpr he)
        · intro he; rcases he with rfl | he
          · exact h_in_old
          · exact (h_other e (by intro h; subst h; exact h_not_new he)).mp he
      rw [h_eq] at *; simp [h_not_new] at *; omega
  · -- e₀ not incident to v: filter unchanged
    push_neg at h_inc
    congr 1; congr 1; ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update]
    split_ifs with h_eq
    · subst h_eq; simp only [Bool.not_eq_true'] at *; tauto
    · rfl

-- If defect is 0, all vertices are satisfied.
theorem defect_zero_satisfied (n m : ℕ) (src tgt : Fin m → Fin n)
    (target : Fin n → Bool) (β : Fin m → Bool)
    (h : defect n m src tgt target β = 0) :
    AllSatisfied n m src tgt target β := by
  intro v; by_contra hv
  have hv_mem : v ∈ univ.filter fun v =>
      vertexParity n m src tgt β v ≠ targetVal target v :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  have := Finset.card_pos.mpr ⟨v, hv_mem⟩
  simp only [defect] at h; omega

-- If defect > 0 on a connected graph with even targets, can reduce defect.
theorem defect_reduction (n m : ℕ) (hn : n ≥ 1)
    (src tgt : Fin m → Fin n) (h_no_self : ∀ e, src e ≠ tgt e)
    (target : Fin n → Bool)
    (h_even : (univ.filter fun v => target v = true).card % 2 = 0)
    (h_conn : Connected n m src tgt)
    (h_cover : ∀ v, ∃ e, src e = v ∨ tgt e = v)
    (β : Fin m → Bool)
    (h_def : defect n m src tgt target β > 0) :
    ∃ β' : Fin m → Bool,
      defect n m src tgt target β' < defect n m src tgt target β := by
  sorry

-- Main theorem: connected + even parity → satisfiable.
theorem gf2_connected_satisfiable (n m : ℕ) (hn : n ≥ 1)
    (src tgt : Fin m → Fin n) (h_no_self : ∀ e : Fin m, src e ≠ tgt e)
    (target : Fin n → Bool)
    (h_even : (univ.filter fun v : Fin n => target v = true).card % 2 = 0)
    (h_conn : Connected n m src tgt)
    (h_cover : ∀ v : Fin n, ∃ e : Fin m, src e = v ∨ tgt e = v) :
    ∃ β : Fin m → Bool, AllSatisfied n m src tgt target β := by
  set β₀ : Fin m → Bool := fun _ => false
  suffices h : ∀ (d : ℕ) (β : Fin m → Bool),
      defect n m src tgt target β ≤ d →
      ∃ β', AllSatisfied n m src tgt target β' by
    exact h _ β₀ le_rfl
  intro d
  induction d with
  | zero =>
    intro β hd
    exact ⟨β, defect_zero_satisfied n m src tgt target β (by omega)⟩
  | succ d ih =>
    intro β hd
    by_cases h0 : defect n m src tgt target β = 0
    · exact ⟨β, defect_zero_satisfied n m src tgt target β h0⟩
    · obtain ⟨β', hlt⟩ := defect_reduction n m hn src tgt h_no_self target
        h_even h_conn h_cover β (Nat.pos_of_ne_zero h0)
      exact ih β' (by omega)

end GF2
