import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLangRankKill
import Mathlib.Data.Nat.Log

/-!
# Two-way communication: the fooling-set method and EQUALITY

A fresh line: *two-way* (interactive) deterministic communication complexity, which the
one-way / oblivious arc could not reach.  The technique is the **fooling set** — a lower bound
via the combinatorial-rectangle structure of any protocol, giving bounds that hold for
interactive protocols, not just one-way.

* `RectPartition f k` — the standard combinatorial model of a `⌈log₂ k⌉`-bit deterministic
  protocol: a leaf map whose classes are **monochromatic combinatorial rectangles** (any
  deterministic protocol induces one; this is the rectangle characterization).
* `FoolingSet f S b` — a set of `b`-valued inputs, no two of which can share a leaf.
* `fooling_card_le` — **the fooling bound**: `|S| ≤ k`.  Distinct fooling inputs land in
  distinct leaves, because a shared leaf would make both "off-diagonal" inputs `b`-valued, which
  the fooling condition forbids.
* `EQ`, `eq_twoway_ge` — EQUALITY (`x = y?`) has the size-`2^n` diagonal fooling set, so any
  protocol needs `≥ 2^n` leaves, i.e. `≥ n` bits of two-way communication.  A concrete
  interactive lower bound, unreachable by the one-way subfunction method.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoWayCommFooling

/-- The combinatorial model of a deterministic two-way protocol with `k` leaves: a leaf map
whose classes are **monochromatic rectangles** — if two inputs share a leaf, so do the two
"off-diagonal" inputs (rectangle), and the value is constant on a leaf (monochromatic). -/
structure RectPartition {α β : Type} (f : α → β → Bool) (k : ℕ) where
  /-- The leaf reached on `(u, v)`. -/
  leaf : α → β → Fin k
  /-- Rectangle property: a shared leaf closes to a rectangle. -/
  rect : ∀ u v u' v', leaf u v = leaf u' v' → leaf u v' = leaf u v ∧ leaf u' v = leaf u v
  /-- Monochromaticity: a leaf has a single output value. -/
  mono : ∀ u v u' v', leaf u v = leaf u' v' → f u v = f u' v'

/-- A fooling set (for value `b`): every element is `b`-valued, and for any two distinct
elements at least one "off-diagonal" crossing is not `b`. -/
def FoolingSet {α β : Type} (f : α → β → Bool) (S : Finset (α × β)) (b : Bool) : Prop :=
  (∀ p ∈ S, f p.1 p.2 = b)
    ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ¬ (f p.1 q.2 = b ∧ f q.1 p.2 = b)

/-- **The fooling bound.**  A protocol with `k` leaves computing `f` cannot have fewer leaves
than any fooling set: distinct fooling inputs occupy distinct leaves. -/
theorem fooling_card_le {α β : Type} (f : α → β → Bool) (k : ℕ)
    (R : RectPartition f k) (S : Finset (α × β)) (b : Bool) (hS : FoolingSet f S b) :
    S.card ≤ k := by
  obtain ⟨hval, hfool⟩ := hS
  have hinj : ∀ p ∈ S, ∀ q ∈ S, R.leaf p.1 p.2 = R.leaf q.1 q.2 → p = q := by
    intro p hp q hq hleaf
    by_contra hpq
    obtain ⟨hr1, hr2⟩ := R.rect p.1 p.2 q.1 q.2 hleaf
    have h1 : f p.1 q.2 = b := by
      rw [R.mono p.1 q.2 p.1 p.2 hr1]; exact hval p hp
    have h2 : f q.1 p.2 = b := by
      rw [R.mono q.1 p.2 q.1 q.2 (by rw [hr2, hleaf])]; exact hval q hq
    exact hfool p hp q hq hpq ⟨h1, h2⟩
  calc S.card
      = (S.image fun p => R.leaf p.1 p.2).card :=
        (Finset.card_image_of_injOn (fun p hp q hq h => hinj p hp q hq h)).symm
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = k := by simp

/-! ## EQUALITY -/

/-- The EQUALITY function: Alice and Bob each hold an `n`-bit string; output whether they are
equal. -/
def EQ (n : ℕ) : (Fin n → Bool) → (Fin n → Bool) → Bool := fun x y => decide (x = y)

/-- The diagonal fooling set of EQUALITY. -/
def diagFool (n : ℕ) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  Finset.univ.image fun x => (x, x)

theorem diagFool_card (n : ℕ) : (diagFool n).card = 2 ^ n := by
  rw [diagFool, Finset.card_image_of_injective _ fun a b h => congrArg Prod.fst h,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The diagonal is a fooling set for EQUALITY (value `true`). -/
theorem diagFool_isFooling (n : ℕ) : FoolingSet (EQ n) (diagFool n) true := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [diagFool, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨x, rfl⟩ := hp
    simp [EQ]
  · intro p hp q hq hpq
    simp only [diagFool, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    have hxy : x ≠ y := fun h => hpq (by rw [h])
    simp only [EQ, decide_eq_true_eq, not_and]
    intro h
    exact absurd h hxy

/-- **EQUALITY needs `≥ 2^n` leaves.**  Any deterministic two-way protocol computing `EQ n` has
at least `2^n` leaves. -/
theorem eq_leaves_ge (n k : ℕ) (R : RectPartition (EQ n) k) : 2 ^ n ≤ k := by
  have := fooling_card_le (EQ n) k R (diagFool n) true (diagFool_isFooling n)
  rwa [diagFool_card] at this

/-- **EQUALITY has two-way communication complexity `≥ n`.**  Any protocol uses messages of
total length `≥ n` (`≥ log₂` of `2^n` leaves) — a linear interactive lower bound. -/
theorem eq_twoway_ge (n k : ℕ) (R : RectPartition (EQ n) k) : n ≤ Nat.log 2 k := by
  have hk : 2 ^ n ≤ k := eq_leaves_ge n k R
  calc n = Nat.log 2 (2 ^ n) := (Nat.log_pow (Nat.one_lt_two) n).symm
    _ ≤ Nat.log 2 k := Nat.log_mono_right hk

end PallLean.Paper93.DeepMath.PathB.TwoWayCommFooling
