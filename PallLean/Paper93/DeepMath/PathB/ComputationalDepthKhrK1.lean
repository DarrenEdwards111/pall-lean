import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCbudgetConeBound

/-!
# K1 of the multiplicative-recurrence engine: Khrapchenko soundness

The new engine lives in the TREE measure (per the recorded design: in the DAG
measure fixed-gadget composition has a linear ceiling, and over the full binary
basis parity has linear formulas — so the measure is DeMorgan formula size):

* `DMTree` — DeMorgan formulas: literal leaves, `∧`/`∨` nodes, `lsize` = leaf
  count;
* `hamEdges` — the Hamming-distance-1 pairs between a 1-set and a 0-set;
* **`khrapchenko` (proved, K1)** — for every DeMorgan tree computing `f` and
  every `A ⊆ f⁻¹(1)`, `B ⊆ f⁻¹(0)`:
  `|E(A,B)|² ≤ lsize · |A| · |B|`.
  Leaf case: the edge relation is a partial matching.  Node case: partition the
  appropriate side, split the edges, and close with the cross-multiplied
  Cauchy–Schwarz step in ℕ (`khr_add`).

This is a RESTRICTED-model measure (DeMorgan formulas, the classical home of
Khrapchenko/Andreev/Håstad).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### DeMorgan formulas -/

/-- DeMorgan formulas: literals at the leaves, `∧`/`∨` at the nodes. -/
inductive DMTree (n : ℕ)
  | lit (i : Fin n) (b : Bool)
  | and (l r : DMTree n)
  | or (l r : DMTree n)

namespace DMTree

def eval {n : ℕ} : DMTree n → (Fin n → Bool) → Bool
  | .lit i b, x => x i == b
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

/-- Formula size: the number of leaves. -/
def lsize {n : ℕ} : DMTree n → ℕ
  | .lit _ _ => 1
  | .and l r => l.lsize + r.lsize
  | .or l r => l.lsize + r.lsize

end DMTree

/-! ### Hamming edges -/

/-- The Hamming-distance-1 pairs from `A` to `B`. -/
def hamEdges (n : ℕ) (A B : Finset (Fin n → Bool)) :
    Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (A ×ˢ B).filter
    (fun p => ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i)))

theorem mem_hamEdges {n : ℕ} {A B : Finset (Fin n → Bool)}
    {p : (Fin n → Bool) × (Fin n → Bool)} :
    p ∈ hamEdges n A B
      ↔ p.1 ∈ A ∧ p.2 ∈ B
        ∧ ∃ i : Fin n, p.2 = Function.update p.1 i (!(p.1 i)) := by
  rw [hamEdges, Finset.mem_filter, Finset.mem_product]
  tauto

/-- Splitting the zero side splits the edge count. -/
theorem hamEdges_card_split_right {n : ℕ} (A B : Finset (Fin n → Bool))
    (q : (Fin n → Bool) → Prop) [DecidablePred q] :
    (hamEdges n A B).card
      = (hamEdges n A (B.filter q)).card
        + (hamEdges n A (B.filter (fun x => ¬ q x))).card := by
  classical
  have hunion : hamEdges n A (B.filter q)
      ∪ hamEdges n A (B.filter (fun x => ¬ q x)) = hamEdges n A B := by
    ext p
    simp only [Finset.mem_union, mem_hamEdges, Finset.mem_filter]
    tauto
  have hdisj : Disjoint (hamEdges n A (B.filter q))
      (hamEdges n A (B.filter (fun x => ¬ q x))) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h₁ := (mem_hamEdges.mp hp₁).2.1
    have h₂ := (mem_hamEdges.mp hp₂).2.1
    exact (Finset.mem_filter.mp h₂).2 (Finset.mem_filter.mp h₁).2
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

/-- Splitting the one side splits the edge count. -/
theorem hamEdges_card_split_left {n : ℕ} (A B : Finset (Fin n → Bool))
    (q : (Fin n → Bool) → Prop) [DecidablePred q] :
    (hamEdges n A B).card
      = (hamEdges n (A.filter q) B).card
        + (hamEdges n (A.filter (fun x => ¬ q x)) B).card := by
  classical
  have hunion : hamEdges n (A.filter q) B
      ∪ hamEdges n (A.filter (fun x => ¬ q x)) B = hamEdges n A B := by
    ext p
    simp only [Finset.mem_union, mem_hamEdges, Finset.mem_filter]
    tauto
  have hdisj : Disjoint (hamEdges n (A.filter q) B)
      (hamEdges n (A.filter (fun x => ¬ q x)) B) := by
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h₁ := (mem_hamEdges.mp hp₁).1
    have h₂ := (mem_hamEdges.mp hp₂).1
    exact (Finset.mem_filter.mp h₂).2 (Finset.mem_filter.mp h₁).2
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

/-! ### The ℕ Cauchy–Schwarz step -/

theorem nat_two_mul_le_add_sq (a b : ℕ) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have he : 2 * (a * (a + d)) = 2 * a ^ 2 + 2 * (a * d) := by ring
    have he' : a ^ 2 + (a + d) ^ 2 = 2 * a ^ 2 + 2 * (a * d) + d ^ 2 := by ring
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have he : 2 * ((b + d) * b) = 2 * b ^ 2 + 2 * (b * d) := by ring
    have he' : (b + d) ^ 2 + b ^ 2 = 2 * b ^ 2 + 2 * (b * d) + d ^ 2 := by ring
    omega

/-- **The cross-multiplied Cauchy–Schwarz step (right form).** -/
theorem khr_add (e₁ e₂ L₁ L₂ a b₁ b₂ : ℕ)
    (h₁ : e₁ ^ 2 ≤ L₁ * a * b₁) (h₂ : e₂ ^ 2 ≤ L₂ * a * b₂) :
    (e₁ + e₂) ^ 2 ≤ (L₁ + L₂) * a * (b₁ + b₂) := by
  have hcross : (2 * (e₁ * e₂)) ^ 2 ≤ (L₁ * a * b₂ + L₂ * a * b₁) ^ 2 := by
    calc (2 * (e₁ * e₂)) ^ 2
        = 4 * (e₁ ^ 2 * e₂ ^ 2) := by ring
      _ ≤ 4 * ((L₁ * a * b₁) * (L₂ * a * b₂)) :=
          Nat.mul_le_mul (Nat.le_refl 4) (Nat.mul_le_mul h₁ h₂)
      _ = 2 * ((L₁ * a * b₂) * (L₂ * a * b₁))
          + 2 * ((L₁ * a * b₂) * (L₂ * a * b₁)) := by ring
      _ ≤ ((L₁ * a * b₂) ^ 2 + (L₂ * a * b₁) ^ 2)
          + 2 * ((L₁ * a * b₂) * (L₂ * a * b₁)) :=
          Nat.add_le_add_right (nat_two_mul_le_add_sq _ _) _
      _ = (L₁ * a * b₂ + L₂ * a * b₁) ^ 2 := by ring
  have hmid : 2 * (e₁ * e₂) ≤ L₁ * a * b₂ + L₂ * a * b₁ := by
    by_contra hlt
    push_neg at hlt
    have := Nat.pow_lt_pow_left hlt (by decide : (2:ℕ) ≠ 0)
    omega
  have hexp : (e₁ + e₂) ^ 2 = e₁ ^ 2 + 2 * (e₁ * e₂) + e₂ ^ 2 := by ring
  have hexp' : (L₁ + L₂) * a * (b₁ + b₂)
      = L₁ * a * b₁ + (L₁ * a * b₂ + L₂ * a * b₁) + L₂ * a * b₂ := by ring
  omega

/-- The left form: split on the one side. -/
theorem khr_add' (e₁ e₂ L₁ L₂ a₁ a₂ b : ℕ)
    (h₁ : e₁ ^ 2 ≤ L₁ * a₁ * b) (h₂ : e₂ ^ 2 ≤ L₂ * a₂ * b) :
    (e₁ + e₂) ^ 2 ≤ (L₁ + L₂) * (a₁ + a₂) * b := by
  have h₁' : e₁ ^ 2 ≤ L₁ * b * a₁ := h₁.trans_eq (by ring)
  have h₂' : e₂ ^ 2 ≤ L₂ * b * a₂ := h₂.trans_eq (by ring)
  exact (khr_add e₁ e₂ L₁ L₂ b a₁ a₂ h₁' h₂').trans_eq (by ring)

/-! ### K1: Khrapchenko soundness -/

/-- **KHRAPCHENKO SOUNDNESS (proved, K1)**: every DeMorgan tree separating
`A` from `B` has at least `|E(A,B)|²/(|A||B|)` leaves. -/
theorem khrapchenko {n : ℕ} (t : DMTree n) :
    ∀ (A B : Finset (Fin n → Bool)),
      (∀ x ∈ A, t.eval x = true) → (∀ x ∈ B, t.eval x = false) →
      (hamEdges n A B).card ^ 2 ≤ t.lsize * A.card * B.card := by
  induction t with
  | lit i b =>
    intro A B hA hB
    -- the edge relation is a partial matching: the flipped coordinate is i
    have hdet : ∀ p ∈ hamEdges n A B,
        p.2 = Function.update p.1 i (!(p.1 i)) := by
      intro p hp
      obtain ⟨hpA, hpB, j, hj⟩ := mem_hamEdges.mp hp
      have h1 := hA p.1 hpA
      have h2 := hB p.2 hpB
      by_cases hij : j = i
      · rw [hij] at hj
        exact hj
      · exfalso
        rw [hj] at h2
        have hne : i ≠ j := fun h => hij h.symm
        have hup : Function.update p.1 j (!(p.1 j)) i = p.1 i :=
          Function.update_of_ne hne (!(p.1 j)) p.1
        show False
        have h2' : (Function.update p.1 j (!(p.1 j)) i == b) = false := h2
        rw [hup] at h2'
        have h1' : (p.1 i == b) = true := h1
        rw [h1'] at h2'
        exact Bool.noConfusion h2'
    have hrec : ∀ p ∈ hamEdges n A B,
        p.1 = Function.update p.2 i (!(p.2 i)) := by
      intro p hp
      have h1 := hdet p hp
      rw [h1, Function.update_self, Bool.not_not, Function.update_idem,
        Function.update_eq_self]
    have hle1 : (hamEdges n A B).card ≤ A.card := by
      refine Finset.card_le_card_of_injOn Prod.fst
        (fun p hp => (mem_hamEdges.mp hp).1) ?_
      intro p hp q hq hfst
      have hp' := hdet p (Finset.mem_coe.mp hp)
      have hq' := hdet q (Finset.mem_coe.mp hq)
      refine Prod.ext_iff.mpr ⟨hfst, ?_⟩
      rw [hp', hq', hfst]
    have hle2 : (hamEdges n A B).card ≤ B.card := by
      refine Finset.card_le_card_of_injOn Prod.snd
        (fun p hp => (mem_hamEdges.mp hp).2.1) ?_
      intro p hp q hq hsnd
      have hp' := hrec p (Finset.mem_coe.mp hp)
      have hq' := hrec q (Finset.mem_coe.mp hq)
      refine Prod.ext_iff.mpr ⟨?_, hsnd⟩
      rw [hp', hq', hsnd]
    show (hamEdges n A B).card ^ 2 ≤ 1 * A.card * B.card
    rw [one_mul, pow_two]
    exact Nat.mul_le_mul hle1 hle2
  | and l r ihl ihr =>
    intro A B hA hB
    classical
    -- one side is jointly true; split the zero side on the left child
    have hAl : ∀ x ∈ A, l.eval x = true := fun x hx =>
      (Bool.and_eq_true _ _ |>.mp (hA x hx)).1
    have hAr : ∀ x ∈ A, r.eval x = true := fun x hx =>
      (Bool.and_eq_true _ _ |>.mp (hA x hx)).2
    have hB₁ : ∀ x ∈ B.filter (fun x => l.eval x = false),
        l.eval x = false := fun x hx => (Finset.mem_filter.mp hx).2
    have hB₂ : ∀ x ∈ B.filter (fun x => ¬ l.eval x = false),
        r.eval x = false := by
      intro x hx
      obtain ⟨hxB, hxl⟩ := Finset.mem_filter.mp hx
      have hand := hB x hxB
      cases hl : l.eval x with
      | false => exact absurd hl hxl
      | true =>
        show r.eval x = false
        have : (l.eval x && r.eval x) = false := hand
        rw [hl, Bool.true_and] at this
        exact this
    have h₁ := ihl A (B.filter (fun x => l.eval x = false)) hAl hB₁
    have h₂ := ihr A (B.filter (fun x => ¬ l.eval x = false)) hAr hB₂
    have hsplit := hamEdges_card_split_right A B (fun x => l.eval x = false)
    have hb : (B.filter (fun x => l.eval x = false)).card
        + (B.filter (fun x => ¬ l.eval x = false)).card = B.card :=
      Finset.card_filter_add_card_filter_not (fun x => l.eval x = false)
    show (hamEdges n A B).card ^ 2 ≤ (l.lsize + r.lsize) * A.card * B.card
    rw [hsplit, ← hb]
    exact khr_add _ _ _ _ _ _ _ h₁ h₂
  | or l r ihl ihr =>
    intro A B hA hB
    classical
    -- the zero side is jointly false; split the one side on the left child
    have hBl : ∀ x ∈ B, l.eval x = false := by
      intro x hx
      have hor := hB x hx
      cases hl : l.eval x with
      | false => rfl
      | true =>
        exfalso
        have : (l.eval x || r.eval x) = false := hor
        rw [hl, Bool.true_or] at this
        exact Bool.noConfusion this
    have hBr : ∀ x ∈ B, r.eval x = false := by
      intro x hx
      have hor := hB x hx
      cases hr : r.eval x with
      | false => rfl
      | true =>
        exfalso
        have : (l.eval x || r.eval x) = false := hor
        rw [hr, Bool.or_true] at this
        exact Bool.noConfusion this
    have hA₁ : ∀ x ∈ A.filter (fun x => l.eval x = true),
        l.eval x = true := fun x hx => (Finset.mem_filter.mp hx).2
    have hA₂ : ∀ x ∈ A.filter (fun x => ¬ l.eval x = true),
        r.eval x = true := by
      intro x hx
      obtain ⟨hxA, hxl⟩ := Finset.mem_filter.mp hx
      have hor := hA x hxA
      cases hl : l.eval x with
      | true => exact absurd hl hxl
      | false =>
        show r.eval x = true
        have : (l.eval x || r.eval x) = true := hor
        rw [hl, Bool.false_or] at this
        exact this
    have h₁ := ihl (A.filter (fun x => l.eval x = true)) B hA₁ hBl
    have h₂ := ihr (A.filter (fun x => ¬ l.eval x = true)) B hA₂ hBr
    have hsplit := hamEdges_card_split_left A B (fun x => l.eval x = true)
    have ha : (A.filter (fun x => l.eval x = true)).card
        + (A.filter (fun x => ¬ l.eval x = true)).card = A.card :=
      Finset.card_filter_add_card_filter_not (fun x => l.eval x = true)
    show (hamEdges n A B).card ^ 2 ≤ (l.lsize + r.lsize) * A.card * B.card
    rw [hsplit, ← ha]
    exact khr_add' _ _ _ _ _ _ _ h₁ h₂

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.khrapchenko
