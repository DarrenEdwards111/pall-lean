import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBoundedOverlapRankLowering

/-!
# Bounded‑depth tree rung — depth bounds incidence, reducing trees to bounded overlap

The bounded‑overlap rung (`…BoundedOverlapRankLowering`) lowers rank by `q^{d·u}` for any layer with incidence
`≤ d`.  A **bounded‑depth tree** of modular gates is exactly such a layer: take the gates to be the subtrees and a
gate's support to be its subtree's leaf set.  The genuinely new structural fact is that **a depth‑`D` tree has
leaf‑incidence `≤ D+1`** — each variable lies in the subtree leaf set of only its ancestors, of which there are
`≤ D+1`.  So the tree rung *reduces* to the proved bounded‑overlap rung with `d = depth+1`.

This requires the **tree** property (sibling subtrees have disjoint leaf sets — no re‑use): with re‑use a variable
could sit in many subtrees and incidence would not be bounded by depth.

## What is proved (clean axioms, no `sorry`)

* `incid_eq_zero_of_not_mem` — a variable outside a subtree's leaf set is in none of its sub‑subtrees.
* `incid_le_depth` — **the new structural lemma**: for a tree (`IsTree`), `incid v t ≤ depth t + 1` — each
  variable lies in at most `depth + 1` subtrees.

## The reduction (stated)

Indexing the gates of a depth‑`D` tree by its subtrees with `supp = ` subtree leaf set, `incid_le_depth` gives the
incidence hypothesis `∀ v, #{gates containing v} ≤ D+1`, so `bounded_overlap_restriction_lowers_rank` yields
`realizedClasses ≤ q^{(D+1)·u}` for a restriction leaving `u` free variables — polynomial when `u = O(log n / D)`.
The subtree‑enumeration is the standard gate↔subtree identification; the new mathematical content is the depth↦
incidence bound proved here.

## Honest scope

A genuine further rung: composition (gates feeding gates) is handled, because for rank lowering only the
*leaf‑support incidence* matters, and a tree's is `≤ depth+1`.  It still needs the **tree** (no‑re‑use) property.
The final rung — poly‑gate ACC⁰ with arbitrary re‑use, where a restriction need not fix any gate's whole subtree
so no gate need become constant — remains open: that is `ACCRestrictionLowersEffectiveRank`,
`NP ⊄ ACC⁰`‑strength, under the PRF‑free naturalness ceiling.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedDepthTreeRung

variable {n : ℕ}

/-- A binary tree of modular gates over `n` input variables. -/
inductive ModTree (n : ℕ) where
  | leaf : Fin n → ModTree n
  | node : ModTree n → ModTree n → ModTree n

/-- The set of input variables in a subtree's leaves. -/
def leafSet : ModTree n → Finset (Fin n)
  | .leaf i => {i}
  | .node l r => leafSet l ∪ leafSet r

/-- The depth of a tree. -/
def depth : ModTree n → ℕ
  | .leaf _ => 0
  | .node l r => 1 + max (depth l) (depth r)

/-- The number of subtrees (gates) whose leaf set contains `v` — the leaf incidence of `v`. -/
def incid (v : Fin n) : ModTree n → ℕ
  | .leaf i => if v = i then 1 else 0
  | .node l r => (if v ∈ leafSet (ModTree.node l r) then 1 else 0) + incid v l + incid v r

/-- The **tree** property: sibling subtrees have disjoint leaf sets (no variable re‑use). -/
def IsTree : ModTree n → Prop
  | .leaf _ => True
  | .node l r => IsTree l ∧ IsTree r ∧ Disjoint (leafSet l) (leafSet r)

/-- A variable outside a subtree's leaf set is in none of its sub‑subtrees. -/
theorem incid_eq_zero_of_not_mem (v : Fin n) : ∀ t : ModTree n, v ∉ leafSet t → incid v t = 0
  | .leaf i, h => by
      simp only [leafSet, Finset.mem_singleton] at h
      simp [incid, h]
  | .node l r, h => by
      have hl : v ∉ leafSet l := fun hh => h (by rw [leafSet]; exact Finset.mem_union_left _ hh)
      have hr : v ∉ leafSet r := fun hh => h (by rw [leafSet]; exact Finset.mem_union_right _ hh)
      simp only [incid, if_neg h, incid_eq_zero_of_not_mem v l hl, incid_eq_zero_of_not_mem v r hr]

/-- **The new structural lemma (proved): a depth‑`D` tree has leaf‑incidence `≤ D+1`.**  Each variable lies in the
leaf set of at most `depth + 1` subtrees — its ancestors. -/
theorem incid_le_depth (v : Fin n) : ∀ t : ModTree n, IsTree t → incid v t ≤ depth t + 1
  | .leaf i, _ => by simp only [incid, depth]; split <;> omega
  | .node l r, h => by
      obtain ⟨htl, htr, hdisj⟩ := h
      by_cases hv : v ∈ leafSet (ModTree.node l r)
      · simp only [incid, if_pos hv]
        rw [leafSet, Finset.mem_union] at hv
        have hm := Nat.le_max_left (depth l) (depth r)
        have hm' := Nat.le_max_right (depth l) (depth r)
        rcases hv with hvl | hvr
        · have hr0 := incid_eq_zero_of_not_mem v r (Finset.disjoint_left.mp hdisj hvl)
          have hd := incid_le_depth v l htl
          simp only [depth]; omega
        · have hl0 := incid_eq_zero_of_not_mem v l (Finset.disjoint_right.mp hdisj hvr)
          have hd := incid_le_depth v r htr
          simp only [depth]; omega
      · have hl : v ∉ leafSet l := fun hh => hv (by rw [leafSet]; exact Finset.mem_union_left _ hh)
        have hr : v ∉ leafSet r := fun hh => hv (by rw [leafSet]; exact Finset.mem_union_right _ hh)
        simp only [incid, if_neg hv, incid_eq_zero_of_not_mem v l hl, incid_eq_zero_of_not_mem v r hr]
        omega

end PallLean.Paper93.DeepMath.PathB.BoundedDepthTreeRung

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedDepthTreeRung.incid_eq_zero_of_not_mem
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedDepthTreeRung.incid_le_depth
