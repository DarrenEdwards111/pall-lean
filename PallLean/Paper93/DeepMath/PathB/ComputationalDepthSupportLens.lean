import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# A real lens, built and capped: the support-count measure

`TransformationSocket` asked for a real lens `μ ≤ cbudget` for the SAT tower.  This file *builds* one — in
a genuine formula model — proves it is a valid lower bound, proves it is **superadditive** on the tower,
and then proves exactly where it **caps**.

The lens is the **support count**: `μ(f) = |{variables f depends on}|`.  A formula computing `f` must have
a leaf for each variable, so `μ` under-approximates the size.

## What is proved

* **`leaves_eq_gates_succ`** — a binary formula with `g` gates has `g+1` leaves.
* **`support_le_leaves`** — `|support| ≤ leaves`: every relevant variable is a distinct leaf.
* **`support_lens`** — **the lens is valid**: `|support t| ≤ gates t + 1`.  So `μ = |support|` is a genuine
  lower bound on formula size (`gates ≥ μ − 1`).
* **`support_doubles`** — **the lens is superadditive**: on a composition of two variable-disjoint copies
  (the tower step), `|support| = |support a| + |support b|`.  So `μ(T₍d+1₎) = 2·μ(Tₐ)` — it survives the
  composition, exactly the Transformation property.
* **`support_lens_caps`** — **and here is the wall**: `|support t| ≤ n`.  The support of a function on `n`
  variables is at most `n`, so this lens can *never* exceed `n`.  On the tower, `μ = 2^d = ` the input
  size, so the bound is **linear in `n`** — trivial.

## The honest lesson

The lens is *real* (valid, `support_lens`) and *superadditive* (`support_doubles`) — it has the
Transformation property for free.  Yet it proves nothing, because `support_lens_caps` pins it at `n`:
counting inputs cannot see complexity beyond the input size.  The tower's `2^d` is just its input size;
super-polynomial in `n` is what's needed, and support caps at `n`.

To beat the cap a lens must see **structure beyond input count** — Khrapchenko counts *pairs* of inputs
(→ `n²`), shrinkage tracks random restrictions (→ `n^{5/2}`) — and those cap too.  This is the concrete
face of the frontier: superadditivity is *easy* (support has it); a lens that is superadditive **and**
uncapped is what no one has.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SupportLens

/-- A binary formula over `n` variables (the formula/tree model). -/
inductive F (n : ℕ) where
  | var : Fin n → F n
  | node : F n → F n → F n

/-- Number of gates (internal nodes). -/
def gates {n : ℕ} : F n → ℕ
  | .var _ => 0
  | .node a b => gates a + gates b + 1

/-- Number of leaves. -/
def leaves {n : ℕ} : F n → ℕ
  | .var _ => 1
  | .node a b => leaves a + leaves b

/-- The variables the formula mentions (its support). -/
def support {n : ℕ} : F n → Finset (Fin n)
  | .var i => {i}
  | .node a b => support a ∪ support b

/-- **A binary formula with `g` gates has `g+1` leaves (proved).** -/
theorem leaves_eq_gates_succ {n : ℕ} (t : F n) : leaves t = gates t + 1 := by
  induction t with
  | var i => rfl
  | node a b iha ihb =>
    show leaves a + leaves b = gates a + gates b + 1 + 1
    rw [iha, ihb]; omega

/-- **`|support| ≤ leaves` (proved).**  Every relevant variable is a distinct leaf. -/
theorem support_le_leaves {n : ℕ} (t : F n) : (support t).card ≤ leaves t := by
  induction t with
  | var i => simp [support, leaves]
  | node a b iha ihb =>
    show (support a ∪ support b).card ≤ leaves a + leaves b
    calc (support a ∪ support b).card ≤ (support a).card + (support b).card :=
          Finset.card_union_le _ _
      _ ≤ leaves a + leaves b := Nat.add_le_add iha ihb

/-- **The lens is valid (proved).**  `|support t| ≤ gates t + 1`: the support count is a genuine lower
bound on formula size (`gates ≥ μ − 1`). -/
theorem support_lens {n : ℕ} (t : F n) : (support t).card ≤ gates t + 1 := by
  rw [← leaves_eq_gates_succ]; exact support_le_leaves t

/-- **The lens is superadditive (proved).**  On a composition of two variable-disjoint copies (the tower
step), the support count adds: `|support (node a b)| = |support a| + |support b|`.  So `μ(T₍d+1₎) =
2·μ(Tₐ)` — the lens has the Transformation property for free. -/
theorem support_doubles {n : ℕ} (a b : F n) (hdisj : Disjoint (support a) (support b)) :
    (support (F.node a b)).card = (support a).card + (support b).card := by
  show (support a ∪ support b).card = (support a).card + (support b).card
  exact Finset.card_union_of_disjoint hdisj

/-- **The wall — the lens caps at `n` (proved).**  The support of a function on `n` variables is at most
`n`, so this lens can never exceed `n`.  On the tower `μ = 2^d = ` the input size, so the bound is only
linear in `n` — trivial.  Counting inputs cannot see complexity beyond the input size. -/
theorem support_lens_caps {n : ℕ} (t : F n) : (support t).card ≤ n := by
  calc (support t).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

end PallLean.Paper93.DeepMath.PathB.SupportLens

#print axioms PallLean.Paper93.DeepMath.PathB.SupportLens.support_lens
#print axioms PallLean.Paper93.DeepMath.PathB.SupportLens.support_doubles
#print axioms PallLean.Paper93.DeepMath.PathB.SupportLens.support_lens_caps
