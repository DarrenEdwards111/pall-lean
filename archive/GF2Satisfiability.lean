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

-- vertexParity is always 0 or 1
theorem vertexParity_le_one (n m : ℕ) (src tgt : Fin m → Fin n)
    (β : Fin m → Bool) (v : Fin n) :
    vertexParity n m src tgt β v = 0 ∨ vertexParity n m src tgt β v = 1 := by
  simp only [vertexParity]; exact Nat.mod_two_eq_zero_or_one _

/-- Flipping an edge changes parity at its endpoints and nowhere else. -/
theorem flip_edge_parity (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e, src e ≠ tgt e)
    (β : Fin m → Bool) (e₀ : Fin m) (v : Fin n) :
    vertexParity n m src tgt (Function.update β e₀ (!β e₀)) v =
    if src e₀ = v ∨ tgt e₀ = v then (vertexParity n m src tgt β v + 1) % 2
    else vertexParity n m src tgt β v := by
  simp only [vertexParity]
  split_ifs with h_inc
  · set S_old := univ.filter fun e : Fin m =>
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
  · push_neg at h_inc
    congr 1; congr 1; ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update]
    split_ifs with h_eq
    · subst h_eq; simp only [Bool.not_eq_true'] at *; tauto
    · rfl

-- Flipping one edge preserves parity of odd-vertex count.
-- The odd set changes at exactly {src e₀, tgt e₀} (2 vertices),
-- so its cardinality changes by 0 or ±2.
theorem flip_preserves_odd_parity (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e, src e ≠ tgt e) (β : Fin m → Bool) (e₀ : Fin m) :
    (univ.filter fun v : Fin n =>
      vertexParity n m src tgt (Function.update β e₀ (!β e₀)) v = 1).card % 2 =
    (univ.filter fun v : Fin n =>
      vertexParity n m src tgt β v = 1).card % 2 := by
  set s := src e₀; set t := tgt e₀
  set S := univ.filter fun v : Fin n => vertexParity n m src tgt β v = 1
  set S' := univ.filter fun v : Fin n =>
    vertexParity n m src tgt (Function.update β e₀ (!β e₀)) v = 1
  have hst : s ≠ t := h_no_self e₀
  -- For v ≠ s and v ≠ t: v ∈ S' ↔ v ∈ S
  have h_agree : ∀ v : Fin n, v ≠ s → v ≠ t → (v ∈ S' ↔ v ∈ S) := by
    intro v hs' ht'
    simp only [S, S', Finset.mem_filter, Finset.mem_univ, true_and]
    have := flip_edge_parity n m src tgt h_no_self β e₀ v
    rw [if_neg (by push_neg; exact ⟨fun h => hs' h.symm, fun h => ht' h.symm⟩)] at this
    rw [this]
  -- For v ∈ {s, t}: parity flips, so v ∈ S' ↔ v ∉ S
  have h_flip_s : s ∈ S' ↔ s ∉ S := by
    simp only [S, S', Finset.mem_filter, Finset.mem_univ, true_and]
    have := flip_edge_parity n m src tgt h_no_self β e₀ s
    rw [if_pos (Or.inl rfl)] at this; rw [this]
    rcases vertexParity_le_one n m src tgt β s with h | h <;> simp [h] <;> omega
  have h_flip_t : t ∈ S' ↔ t ∉ S := by
    simp only [S, S', Finset.mem_filter, Finset.mem_univ, true_and]
    have := flip_edge_parity n m src tgt h_no_self β e₀ t
    rw [if_pos (Or.inr rfl)] at this; rw [this]
    rcases vertexParity_le_one n m src tgt β t with h | h <;> simp [h] <;> omega
  -- Case split on s ∈ S, t ∈ S
  rcases Decidable.em (s ∈ S) with hs_in | hs_out <;>
    rcases Decidable.em (t ∈ S) with ht_in | ht_out
  · -- Both in S → both not in S' → S' = S \ {s,t} → |S'| = |S| - 2
    have hs' : s ∉ S' := by rwa [h_flip_s, not_not]
    have ht' : t ∉ S' := by rwa [h_flip_t, not_not]
    have h_eq : S' = (S.erase s).erase t := by
      ext v; simp only [Finset.mem_erase]
      constructor
      · intro hv
        have hvs : v ≠ s := fun h => by subst h; exact hs' hv
        have hvt : v ≠ t := fun h => by subst h; exact ht' hv
        exact ⟨hvt, hvs, (h_agree v hvs hvt).mp hv⟩
      · intro ⟨hvt, hvs, hv⟩; exact (h_agree v hvs hvt).mpr hv
    rw [h_eq]
    have : t ∈ S.erase s := Finset.mem_erase.mpr ⟨hst.symm, ht_in⟩
    rw [Finset.card_erase_of_mem this, Finset.card_erase_of_mem hs_in]
    have h1 := Finset.card_pos.mpr ⟨s, hs_in⟩
    have h2 := Finset.card_pos.mpr ⟨t, Finset.mem_erase.mpr ⟨hst.symm, ht_in⟩⟩
    rw [Finset.card_erase_of_mem hs_in] at h2; omega
  · -- s in, t out → s not in S', t in S' → swap
    have hs' : s ∉ S' := by rwa [h_flip_s, not_not]
    have ht' : t ∈ S' := h_flip_t.mpr ht_out
    have h_eq : S' = (S.erase s).cons t (by
        simp only [Finset.mem_erase]; intro ⟨_, h⟩; exact ht_out h) := by
      ext v; simp only [Finset.mem_cons, Finset.mem_erase]
      constructor
      · intro hv
        by_cases hvt : v = t
        · exact Or.inl hvt
        · have hvs : v ≠ s := fun h => by subst h; exact hs' hv
          exact Or.inr ⟨hvs, (h_agree v hvs hvt).mp hv⟩
      · intro hv; rcases hv with rfl | ⟨hvs, hv⟩
        · exact ht'
        · have hvt : v ≠ t := fun h => by subst h; exact ht_out hv
          exact (h_agree v hvs hvt).mpr hv
    rw [h_eq, Finset.card_cons, Finset.card_erase_of_mem hs_in]
    have := Finset.card_pos.mpr ⟨s, hs_in⟩; omega
  · -- s out, t in → s in S', t not in S' → swap
    have hs' : s ∈ S' := h_flip_s.mpr hs_out
    have ht' : t ∉ S' := by rwa [h_flip_t, not_not]
    have h_eq : S' = (S.erase t).cons s (by
        simp only [Finset.mem_erase]; intro ⟨_, h⟩; exact hs_out h) := by
      ext v; simp only [Finset.mem_cons, Finset.mem_erase]
      constructor
      · intro hv
        by_cases hvs : v = s
        · exact Or.inl hvs
        · have hvt : v ≠ t := fun h => by subst h; exact ht' hv
          exact Or.inr ⟨hvt, (h_agree v hvs hvt).mp hv⟩
      · intro hv; rcases hv with rfl | ⟨hvt, hv⟩
        · exact hs'
        · have hvs : v ≠ s := fun h => by subst h; exact hs_out hv
          exact (h_agree v hvs hvt).mpr hv
    rw [h_eq, Finset.card_cons, Finset.card_erase_of_mem ht_in]
    have := Finset.card_pos.mpr ⟨t, ht_in⟩; omega
  · -- Both out → both in S' → S' = S ∪ {s,t}
    have hs' : s ∈ S' := h_flip_s.mpr hs_out
    have ht' : t ∈ S' := h_flip_t.mpr ht_out
    have h_eq : S' = (S.cons s hs_out).cons t (by
        simp only [Finset.mem_cons]; push_neg; exact ⟨hst.symm, ht_out⟩) := by
      ext v; simp only [Finset.mem_cons]
      constructor
      · intro hv
        by_cases hvt : v = t; · exact Or.inl hvt
        by_cases hvs : v = s; · exact Or.inr (Or.inl hvs)
        exact Or.inr (Or.inr ((h_agree v hvs hvt).mp hv))
      · intro hv; rcases hv with rfl | rfl | hv
        · exact ht'
        · exact hs'
        · have hvs : v ≠ s := fun h => by subst h; exact hs_out hv
          have hvt : v ≠ t := fun h => by subst h; exact ht_out hv
          exact (h_agree v hvs hvt).mpr hv
    rw [h_eq, Finset.card_cons, Finset.card_cons]; omega

/-- Total vertex parity is always even (each edge has 2 endpoints).
    Proof by induction on number of true edges. -/
theorem total_parity_even (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e : Fin m, src e ≠ tgt e) (β : Fin m → Bool) :
    (univ.filter fun v : Fin n =>
      vertexParity n m src tgt β v = 1).card % 2 = 0 := by
  -- Induction on number of true edges
  suffices h : ∀ (k : ℕ) (β : Fin m → Bool),
      (univ.filter fun e => β e = true).card ≤ k →
      (univ.filter fun v => vertexParity n m src tgt β v = 1).card % 2 = 0 by
    exact h _ β le_rfl
  intro k
  induction k with
  | zero =>
    intro β hk
    have h_all_false : ∀ e : Fin m, β e = false := by
      intro e; by_contra he
      have he' : β e = true := by cases β e <;> simp_all
      have : (univ.filter fun e => β e = true).card > 0 :=
        Finset.card_pos.mpr ⟨e, by simp [Finset.mem_filter, he']⟩
      omega
    have h0 : ∀ v, vertexParity n m src tgt β v = 0 := by
      intro v; simp only [vertexParity]
      have : (univ.filter fun e => (src e = v ∨ tgt e = v) ∧ β e = true) = ∅ := by
        ext e; simp [Finset.mem_filter, h_all_false e]
      rw [this]; simp
    simp [h0]
  | succ k ih =>
    intro β hk
    by_cases h0 : (univ.filter fun e => β e = true).card = 0
    · have h_all_false : ∀ e : Fin m, β e = false := by
        intro e; by_contra he
        have : β e = true := by cases β e <;> simp_all
        have : (univ.filter fun e => β e = true).card > 0 :=
          Finset.card_pos.mpr ⟨e, by simp [Finset.mem_filter, ‹β e = true›]⟩
        omega
      have h0' : ∀ v, vertexParity n m src tgt β v = 0 := by
        intro v; simp only [vertexParity]
        have : (univ.filter fun e => (src e = v ∨ tgt e = v) ∧ β e = true) = ∅ := by
          ext e; simp [Finset.mem_filter, h_all_false e]
        rw [this]; simp
      simp [h0']
    · have hne : (univ.filter fun e => β e = true).Nonempty :=
        Finset.card_pos.mp (by omega)
      obtain ⟨e₀, he₀⟩ := hne
      have he₀_true : β e₀ = true := (Finset.mem_filter.mp he₀).2
      set β' := Function.update β e₀ false
      have h_card' : (univ.filter fun e => β' e = true).card ≤ k := by
        have : (univ.filter fun e => β' e = true) =
            (univ.filter fun e => β e = true).erase e₀ := by
          ext e; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
          constructor
          · intro h
            have hne : e ≠ e₀ := by
              intro heq; subst heq; simp [β', Function.update_self] at h
            exact ⟨hne, by simp [β', Function.update_apply, if_neg hne] at h; exact h⟩
          · intro ⟨hne, h⟩; simp [β', Function.update_apply, if_neg hne]; exact h
        rw [this, Finset.card_erase_of_mem he₀]; omega
      have ih' := ih β' h_card'
      -- β = Function.update β' e₀ (!β' e₀) since β' e₀ = false
      have h_restore : Function.update β' e₀ (!β' e₀) = β := by
        ext e; simp only [Function.update_apply]
        split_ifs with h
        · subst h; simp only [β', Function.update_self, Bool.not_false, he₀_true]
        · simp only [β', Function.update_apply, if_neg h]
      rw [← h_restore]
      exact (flip_preserves_odd_parity n m src tgt h_no_self β' e₀).trans ih'

/-- The defect is always even when targets have even parity.
    defect = |O Δ T| where O = odd-parity vertices, T = target-true vertices.
    |O Δ T| = |O| + |T| - 2|O ∩ T|, so defect % 2 = (|O| + |T|) % 2 = 0. -/
theorem defect_parity (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e, src e ≠ tgt e) (target : Fin n → Bool)
    (h_even : (univ.filter fun v => target v = true).card % 2 = 0)
    (β : Fin m → Bool) :
    defect n m src tgt target β % 2 = 0 := by
  simp only [defect]
  set O := univ.filter fun v : Fin n => vertexParity n m src tgt β v = 1
  set T := univ.filter fun v : Fin n => target v = true
  set D := univ.filter fun v : Fin n =>
    vertexParity n m src tgt β v ≠ targetVal target v
  have h_O := total_parity_even n m src tgt h_no_self β
  -- D is the symmetric difference of O and T
  have h_D_sdiff : D = (O \ T) ∪ (T \ O) := by
    ext v; simp only [D, O, T, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_sdiff, targetVal]
    rcases vertexParity_le_one n m src tgt β v with hp | hp <;>
      cases ht : target v <;> simp [hp, ht] <;> omega
  have h_disj : Disjoint (O \ T) (T \ O) := by
    rw [Finset.disjoint_left]; intro v hv1 hv2
    simp only [Finset.mem_sdiff] at hv1 hv2; exact hv1.2 hv2.1
  rw [h_D_sdiff, Finset.card_union_of_disjoint h_disj]
  -- (O \ T).card + (T \ O).card = O.card + T.card - 2 * (O ∩ T).card
  -- (O \ T).card = O.card - (O ∩ T).card, (T \ O).card = T.card - (T ∩ O).card
  -- Sum ≡ O.card + T.card (mod 2) since we subtract (O∩T).card twice
  have h1 : (O \ T).card + (O ∩ T).card = O.card := by
    rw [Finset.card_sdiff_add_card_inter]
  have h2 : (T \ O).card + (T ∩ O).card = T.card := by
    rw [Finset.card_sdiff_add_card_inter]
  rw [Finset.inter_comm] at h2
  -- (O\T).card + (T\O).card + 2*(O∩T).card = O.card + T.card
  have h3 : (O \ T).card + (T \ O).card + 2 * (O ∩ T).card = O.card + T.card := by omega
  -- x % 2 = (x + 2k) % 2 = (O.card + T.card) % 2
  -- x + 2k ≡ x (mod 2), so (O\T + T\O) % 2 = (O + T) % 2
  -- From h3: x + 2k = y where x = |O\T| + |T\O|, k = |O∩T|, y = |O| + |T|
  -- x % 2 = y % 2 (since x = y - 2k and 2k ≡ 0 mod 2)
  -- y % 2 = 0 since |O| % 2 = 0 and |T| % 2 = 0
  calc ((O \ T).card + (T \ O).card) % 2
      = ((O \ T).card + (T \ O).card + 2 * (O ∩ T).card) % 2 := by
        rw [show (O \ T).card + (T \ O).card + 2 * (O ∩ T).card =
          (O \ T).card + (T \ O).card + (O ∩ T).card * 2 from by ring,
          Nat.add_mul_mod_self_right]
    _ = (O.card + T.card) % 2 := by rw [h3]
    _ = 0 := by
      have : O.card % 2 = 0 := h_O
      have : T.card % 2 = 0 := h_even
      omega

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

-- Path flipping: flip all edges along a Reachable path.
-- For u ≠ w: parity flips at u and w, unchanged elsewhere.
-- For u = w (empty path): parity unchanged everywhere.
theorem path_flip_exists (n m : ℕ) (src tgt : Fin m → Fin n)
    (h_no_self : ∀ e, src e ≠ tgt e) (β : Fin m → Bool)
    (u w : Fin n) (h_reach : Reachable n m src tgt u w) (h_uw : u ≠ w) :
    ∃ β' : Fin m → Bool, ∀ v : Fin n,
      vertexParity n m src tgt β' v =
      if v = u ∨ v = w then (vertexParity n m src tgt β v + 1) % 2
      else vertexParity n m src tgt β v := by
  induction h_reach with
  | refl => exact absurd rfl h_uw
  | step b w' e₁ _ he ih =>
    by_cases hab_eq : u = b
    · subst hab_eq
      refine ⟨Function.update β e₁ (!β e₁), fun v => ?_⟩
      rw [flip_edge_parity _ _ _ _ h_no_self β e₁ v]
      -- flip gives: if src e₁ = v ∨ tgt e₁ = v then (p+1)%2 else p
      -- need: if v = u ∨ v = w' then (p+1)%2 else p
      -- he says: src e₁ = u ∧ tgt e₁ = w' ∨ src e₁ = w' ∧ tgt e₁ = u
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
        simp only [eq_comm] <;> split_ifs <;> simp_all
    · obtain ⟨β', ih'⟩ := ih hab_eq
      refine ⟨Function.update β' e₁ (!β' e₁), fun v => ?_⟩
      rw [flip_edge_parity _ _ _ _ h_no_self β' e₁ v, ih' v]
      -- IH: β' has if v=u ∨ v=b then (p+1)%2 else p
      -- flip e₁: changes at src/tgt of e₁ = b and w'
      -- Net: u stays flipped, b double-flips (cancels), w' newly flipped
      -- Case analysis on which vertices v equals
      -- 4 possibilities: v=u, v=b, v=w', or none
      -- Goal: result = if v = u ∨ v = w' then (p+1)%2 else p
      -- We have: result = if (src e₁ = v ∨ tgt e₁ = v)
      --            then (if v = u ∨ v = b then (p+1)%2 else p + 1) % 2
      --            else (if v = u ∨ v = b then (p+1)%2 else p)
      -- e₁ connects b and w' (from he). We case-split on v:
      -- v = u: not endpoint of e₁ (u ≠ b, u ≠ w'), so outer if = false.
      --        Inner if v=u is true. Result = (p+1)%2. ✓
      -- v = b: endpoint of e₁, so outer if = true. Inner if v=b is true.
      --        Result = ((p+1)%2 + 1)%2 = p. Need if false → p. ✓
      -- v = w': endpoint of e₁, so outer if = true. Inner if v=w' is false (w'≠u, w'≠b).
      --        Result = (p + 1)%2. Need if true → (p+1)%2. ✓
      -- v = other: not endpoint. Outer if false. Inner if false. Result = p. ✓
      -- All 4 cases: the two conditions (src/tgt incident) and (v=u ∨ v=b) interact.
      -- Use h_no_self, hab_eq, h_uw to derive which ifs are true/false.
      have h_e_inc : ∀ x : Fin n, (src e₁ = x ∨ tgt e₁ = x) ↔ (x = b ∨ x = w') := by
        intro x; rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> intro h <;>
          rcases h with rfl | rfl <;> simp_all
      -- Translate edge incidence to vertex equality
      have h_src_tgt : ∀ x, (src e₁ = x ∨ tgt e₁ = x) ↔ (x = b ∨ x = w') := by
        intro x; rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          constructor <;> intro hx <;> rcases hx with rfl | rfl <;> simp_all
      -- Key facts about which vertices are distinct
      have hub : u ≠ b := hab_eq
      have huw : u ≠ w' := h_uw
      -- Simplify using these
      have h_outer : (v = b ∨ v = w') → (src e₁ = v ∨ tgt e₁ = v) := (h_src_tgt v).mpr
      have h_not_outer : ¬(v = b ∨ v = w') → ¬(src e₁ = v ∨ tgt e₁ = v) :=
        fun h h' => h ((h_src_tgt v).mp h')
      by_cases hvu : v = u
      · -- v = u: not b or w', so outer if is false
        have : ¬(v = b ∨ v = w') := by push_neg; exact ⟨hvu ▸ hub, hvu ▸ huw⟩
        rw [if_neg (fun h' => this ((h_src_tgt v).mp h')), if_pos (Or.inl hvu), if_pos (Or.inl hvu)]
      · by_cases hvb : v = b
        · -- v = b: double flip cancels
          -- v = b: double-flip cancels. Need ((p+1)%2+1)%2 = p
          -- After rw [ih' v], we have two nested ifs.
          -- The goal should be about src e₁ / tgt e₁ and v = u / v = b
          -- Let's use convert and omega
          have hvw' : v ≠ w' := by
            intro hvw
            have hbw : b = w' := hvb.symm.trans hvw
            exact h_no_self e₁ (by
              rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact h1.trans (hbw.trans h2.symm)
              · exact h1.trans (hbw.symm.trans h2.symm))
          simp only [if_pos ((h_src_tgt v).mpr (Or.inl hvb)),
            show v = u ∨ v = b from Or.inr hvb, ite_true,
            show (v = u ∨ v = w') = False from propext ⟨fun h => h.elim hvu hvw', False.elim⟩,
            ite_false]
          rcases vertexParity_le_one _ _ src tgt β v with hp | hp <;> simp [hp]
        · by_cases hvw : v = w'
          · -- v = w': outer if true, inner if false (v≠u, v≠b), target if true
            rw [if_pos ((h_src_tgt v).mpr (Or.inr hvw)),
              if_neg (by push_neg; exact ⟨hvu, hvb⟩),
              if_pos (Or.inr hvw)]
          · -- v ≠ u,b,w': everything false
            have : ¬(v = b ∨ v = w') := by push_neg; exact ⟨hvb, hvw⟩
            rw [if_neg (fun h' => this ((h_src_tgt v).mp h')),
              if_neg (by push_neg; exact ⟨hvu, hvb⟩),
              if_neg (by push_neg; exact ⟨hvu, hvw⟩)]

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
  have h_dp := defect_parity n m src tgt h_no_self target h_even β
  have h_def2 : defect n m src tgt target β ≥ 2 := by omega
  -- Extract two distinct unsatisfied vertices
  set U := univ.filter fun v : Fin n =>
    vertexParity n m src tgt β v ≠ targetVal target v
  have hU_card : U.card = defect n m src tgt target β := rfl
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show U.card > 0 by omega)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show (U.erase u).card > 0 by
    rw [Finset.card_erase_of_mem hu]; omega)
  have hv_erase := (Finset.mem_erase.mp hv)
  have hne : u ≠ v := fun h => by subst h; exact hv_erase.1 rfl
  have hu_unsat := (Finset.mem_filter.mp hu).2
  have hv_unsat := (Finset.mem_filter.mp hv_erase.2).2
  -- Path flip from u to v
  obtain ⟨β', h_flip⟩ := path_flip_exists n m src tgt h_no_self β u v (h_conn u v) hne
  refine ⟨β', ?_⟩
  simp only [defect]
  -- u becomes satisfied after flip
  have hu_sat : vertexParity n m src tgt β' u = targetVal target u := by
    rw [h_flip u, if_pos (Or.inl rfl)]
    rcases vertexParity_le_one n m src tgt β u with hp | hp <;>
      simp only [targetVal] at hu_unsat ⊢ <;>
      split_ifs at hu_unsat ⊢ <;> simp_all <;> omega
  -- v becomes satisfied after flip
  have hv_sat : vertexParity n m src tgt β' v = targetVal target v := by
    rw [h_flip v, if_pos (Or.inr rfl)]
    rcases vertexParity_le_one n m src tgt β v with hp | hp <;>
      simp only [targetVal] at hv_unsat ⊢ <;>
      split_ifs at hv_unsat ⊢ <;> simp_all <;> omega
  -- Other vertices unchanged
  have h_other : ∀ w, w ≠ u → w ≠ v →
      (vertexParity n m src tgt β' w ≠ targetVal target w ↔
       vertexParity n m src tgt β w ≠ targetVal target w) := by
    intro w hw1 hw2
    rw [h_flip w, if_neg (by push_neg; exact ⟨hw1, hw2⟩)]
  -- New unsatisfied set is strictly smaller
  -- New unsatisfied ⊆ old unsatisfied, and u is no longer in it
  set U' := univ.filter fun w : Fin n =>
    vertexParity n m src tgt β' w ≠ targetVal target w
  have h_sub : U' ⊆ U := by
    intro w hw
    simp only [U', Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hw1 : w = u
    · subst hw1; exact absurd hu_sat hw
    · by_cases hw2 : w = v
      · subst hw2; exact absurd hv_sat hw
      · exact (h_other w hw1 hw2).mp hw
  have h_not : u ∉ U' := by
    simp only [U', Finset.mem_filter, Finset.mem_univ, true_and]
    push_neg; exact hu_sat
  exact Finset.card_lt_card (Finset.ssubset_iff_of_subset h_sub |>.mpr ⟨u, hu, h_not⟩)

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
