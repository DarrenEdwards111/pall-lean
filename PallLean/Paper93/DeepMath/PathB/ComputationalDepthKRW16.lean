import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW15

/-!
# KRW brick 16: the fooling-set lower bound technique

The classical fooling-set method for communication complexity, formalized for the
universal-relation protocol model.  A *fooling set* is a set of pairs no two of
which can share a monochromatic leaf; a depth-`d` protocol has `≤ 2^d` leaves, so
a fooling set of size `m` forces cost `≥ log₂ m`.

* **`Valid2 i p q`** — the `2×2` rectangle of two pairs is monochromatic for
  coordinate `i`;
* **`Fooling S`** — no two distinct pairs of `S` are jointly `Valid2` at any `i`;
* **`fooling_card_le` (proved)** — `HasUProtocol A B d` ⇒ any fooling
  `S ⊆ A ×ˢ B` has `|S| ≤ 2^d` (the technique: induction splits the fooling set
  across the protocol tree, `≤ 1` per leaf);
* **`unitFool`** and **`uprotocol_fooling_lb` (proved)** — the `n` unit-vector
  pairs `(eⱼ, 0)` form a fooling set, so every `U`-protocol on `n` bits has
  `n ≤ 2^d`, i.e. cost `≥ log₂ n`.

HONEST NOTE.  The fooling-set technique lower-bounds NONdeterministic CC, which is
only `O(log n)` for `U_n`; so it yields just `Ω(log n)` here — EXPONENTIALLY weaker
than the linear `Θ(n)` of KRW14/15, which needs a deterministic-partition
(domination) argument.  The `n` unit vectors are essentially the largest fooling
set (`U_n`'s fooling number is `Θ(n)`).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

open scoped Classical

/-- The `2×2` rectangle of pairs `p, q` is monochromatic for coordinate `i`: every
distinct pair among the four differs at `i`. -/
def Valid2 {n : ℕ} (i : Fin n) (p q : (Fin n → Bool) × (Fin n → Bool)) : Prop :=
  (p.1 ≠ p.2 → p.1 i ≠ p.2 i) ∧ (q.1 ≠ q.2 → q.1 i ≠ q.2 i)
    ∧ (p.1 ≠ q.2 → p.1 i ≠ q.2 i) ∧ (q.1 ≠ p.2 → q.1 i ≠ p.2 i)

/-- A fooling set: no two distinct pairs are jointly monochromatic at any `i`. -/
def Fooling {n : ℕ} (S : Finset ((Fin n → Bool) × (Fin n → Bool))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ i : Fin n, ¬ Valid2 i p q

/-- **The fooling-set bound (proved)**: a depth-`d` protocol admits fooling sets of
size at most `2^d`. -/
theorem fooling_card_le {n : ℕ} {A B : Finset (Fin n → Bool)} {d : ℕ}
    (h : HasUProtocol A B d) :
    ∀ (S : Finset ((Fin n → Bool) × (Fin n → Bool))), S ⊆ A ×ˢ B → Fooling S →
      S.card ≤ 2 ^ d := by
  induction h with
  | leaf d i hlf =>
    intro S hS hF
    have : S.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro p hp q hq
      by_contra hpq
      refine hF p hp q hq hpq i ?_
      have hp1 := (Finset.mem_product.mp (hS hp)).1
      have hp2 := (Finset.mem_product.mp (hS hp)).2
      have hq1 := (Finset.mem_product.mp (hS hq)).1
      have hq2 := (Finset.mem_product.mp (hS hq)).2
      exact ⟨hlf p.1 hp1 p.2 hp2, hlf q.1 hq1 q.2 hq2,
             hlf p.1 hp1 q.2 hq2, hlf q.1 hq1 p.2 hp2⟩
    calc S.card ≤ 1 := this
      _ ≤ 2 ^ d := Nat.one_le_two_pow
  | bob pr h0 h1 ih0 ih1 =>
    rename_i A B d
    intro S hS hF
    have hsub0 : S.filter (fun p => pr p.2 = false)
        ⊆ A ×ˢ (B.filter (fun y => pr y = false)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpS := Finset.mem_product.mp (hS hp.1)
      exact Finset.mem_product.mpr ⟨hpS.1, Finset.mem_filter.mpr ⟨hpS.2, hp.2⟩⟩
    have hsub1 : S.filter (fun p => ¬ pr p.2 = false)
        ⊆ A ×ˢ (B.filter (fun y => pr y = true)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpS := Finset.mem_product.mp (hS hp.1)
      have hpt : pr p.2 = true := by
        cases hh : pr p.2 with | false => exact absurd hh hp.2 | true => rfl
      exact Finset.mem_product.mpr ⟨hpS.1, Finset.mem_filter.mpr ⟨hpS.2, hpt⟩⟩
    have hF0 : Fooling (S.filter (fun p => pr p.2 = false)) :=
      fun p hp q hq => hF p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    have hF1 : Fooling (S.filter (fun p => ¬ pr p.2 = false)) :=
      fun p hp q hq => hF p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    have hc0 := ih0 _ hsub0 hF0
    have hc1 := ih1 _ hsub1 hF1
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S) (p := fun p => pr p.2 = false)
    have hpow : (2 : ℕ) ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; ring
    omega
  | alice pr h0 h1 ih0 ih1 =>
    rename_i A B d
    intro S hS hF
    have hsub0 : S.filter (fun p => pr p.1 = false)
        ⊆ (A.filter (fun x => pr x = false)) ×ˢ B := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpS := Finset.mem_product.mp (hS hp.1)
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpS.1, hp.2⟩, hpS.2⟩
    have hsub1 : S.filter (fun p => ¬ pr p.1 = false)
        ⊆ (A.filter (fun x => pr x = true)) ×ˢ B := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpS := Finset.mem_product.mp (hS hp.1)
      have hpt : pr p.1 = true := by
        cases hh : pr p.1 with | false => exact absurd hh hp.2 | true => rfl
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpS.1, hpt⟩, hpS.2⟩
    have hF0 : Fooling (S.filter (fun p => pr p.1 = false)) :=
      fun p hp q hq => hF p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    have hF1 : Fooling (S.filter (fun p => ¬ pr p.1 = false)) :=
      fun p hp q hq => hF p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    have hc0 := ih0 _ hsub0 hF0
    have hc1 := ih1 _ hsub1 hF1
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S) (p := fun p => pr p.1 = false)
    have hpow : (2 : ℕ) ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; ring
    omega

/-! ### A concrete fooling set: the unit vectors -/

/-- The `j`-th unit vector. -/
def unitVec {n : ℕ} (j : Fin n) : Fin n → Bool := fun i => decide (i = j)

theorem unitVec_ne_const {n : ℕ} (j : Fin n) : unitVec j ≠ (fun _ => false) := by
  intro h; have := congrFun h j; simp [unitVec] at this

theorem unitVec_injective {n : ℕ} : Function.Injective (unitVec (n := n)) := by
  intro j j' h
  by_contra hne
  have h1 : unitVec j j = true := by simp [unitVec]
  have h2 : unitVec j' j = false := by simp [unitVec, hne]
  rw [h] at h1
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Two distinct unit-vector pairs are never jointly monochromatic. -/
theorem unit_not_valid2 {n : ℕ} (i j j' : Fin n) (hjj : j ≠ j') :
    ¬ Valid2 i (unitVec j, fun _ => false) (unitVec j', fun _ => false) := by
  rintro ⟨hA, -, -, hD⟩
  have huj : unitVec j i = true := by
    by_contra hc
    have hf : unitVec j i = false := by
      cases hh : unitVec j i with | false => rfl | true => exact absurd hh hc
    exact hA (unitVec_ne_const j) hf
  have huj' : unitVec j' i = true := by
    by_contra hc
    have hf : unitVec j' i = false := by
      cases hh : unitVec j' i with | false => rfl | true => exact absurd hh hc
    exact hD (unitVec_ne_const j') hf
  have h1 : i = j := of_decide_eq_true huj
  have h2 : i = j' := of_decide_eq_true huj'
  exact hjj (h1.symm.trans h2)

/-- The unit-vector fooling set `{(eⱼ, 0)}`. -/
noncomputable def unitFool (n : ℕ) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  Finset.univ.image (fun j : Fin n => (unitVec j, fun _ => false))

theorem unitFool_card (n : ℕ) : (unitFool n).card = n := by
  rw [unitFool, Finset.card_image_of_injective _ (fun j j' h =>
    unitVec_injective (Prod.ext_iff.mp h).1), Finset.card_univ, Fintype.card_fin]

theorem unitFool_fooling (n : ℕ) : Fooling (unitFool n) := by
  intro p hp q hq hpq i
  rw [unitFool, Finset.mem_image] at hp hq
  obtain ⟨j, _, rfl⟩ := hp
  obtain ⟨j', _, rfl⟩ := hq
  have hjj : j ≠ j' := by intro h; subst h; exact hpq rfl
  exact unit_not_valid2 i j j' hjj

theorem unitFool_subset (n : ℕ) :
    unitFool n ⊆ (Finset.univ : Finset (Fin n → Bool)) ×ˢ Finset.univ :=
  fun p _ => Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩

/-- **THE FOOLING-SET LOWER BOUND (proved)**: every `U`-protocol on `n` bits has
`n ≤ 2^d`, i.e. cost `≥ log₂ n`.  (Only `Ω(log n)` — see the honest note.) -/
theorem uprotocol_fooling_lb {n d : ℕ}
    (h : HasUProtocol (Finset.univ : Finset (Fin n → Bool)) Finset.univ d) :
    n ≤ 2 ^ d := by
  have := fooling_card_le h (unitFool n) (unitFool_subset n) (unitFool_fooling n)
  rwa [unitFool_card] at this

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.fooling_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.uprotocol_fooling_lb
