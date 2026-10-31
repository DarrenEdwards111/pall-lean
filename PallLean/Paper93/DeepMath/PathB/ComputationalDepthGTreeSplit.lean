import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMTwoFinale

/-!
# Brick A of the ∀m `SlackComposes` campaign: general trees and their split theorem

The ∀m argument extracts circuit unwindings from *arbitrary* circuits — no
gate-elimination normalization.  `GTree` absorbs every gate shape (variable,
constant, unary, binary), and the count-based split theorem extends:

* `GTree` — general unwinding trees, with `eval`, `leaves`, `cnt`;
* **`gtree_split_cnt` (proved)** — a general tree in which three distinct
  variables each occur in exactly one leaf splits at one of the three under any
  completion: constants are vacuous (count 0), unary nodes transfer splits by
  post-composition (`split*_comp`), binary nodes are the eight-way bash of
  `rot_split_cnt`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- General unwinding trees: every gate shape absorbed. -/
inductive GTree (n : ℕ) : Type where
  | leaf : Fin n → GTree n
  | cst : Bool → GTree n
  | un : (Bool → Bool) → GTree n → GTree n
  | node : (Bool → Bool → Bool) → GTree n → GTree n → GTree n

namespace GTree

def eval : GTree n → (Fin n → Bool) → Bool
  | leaf i, x => x i
  | cst b, _ => b
  | un op t, x => op (t.eval x)
  | node op l r, x => op (l.eval x) (r.eval x)

def leaves : GTree n → Finset (Fin n)
  | leaf i => {i}
  | cst _ => ∅
  | un _ t => t.leaves
  | node _ l r => l.leaves ∪ r.leaves

def cnt : GTree n → Fin n → ℕ
  | leaf j, i => if j = i then 1 else 0
  | cst _, _ => 0
  | un _ t, i => t.cnt i
  | node _ l r, i => l.cnt i + r.cnt i

theorem eval_update_of_not_leaf (t : GTree n) (i : Fin n) (hi : i ∉ t.leaves)
    (x : Fin n → Bool) (b : Bool) :
    t.eval (Function.update x i b) = t.eval x := by
  induction t with
  | leaf j =>
    have hj : j ≠ i := by
      intro he
      exact hi (by rw [leaves, Finset.mem_singleton, he])
    show Function.update x i b j = x j
    exact Function.update_of_ne hj b x
  | cst b' => rfl
  | un op t iht =>
    have ht : i ∉ t.leaves := hi
    show op (t.eval (Function.update x i b)) = op (t.eval x)
    rw [iht ht]
  | node op l r ihl ihr =>
    have hl : i ∉ l.leaves := fun h => hi (by rw [leaves, Finset.mem_union]; exact Or.inl h)
    have hr : i ∉ r.leaves := fun h => hi (by rw [leaves, Finset.mem_union]; exact Or.inr h)
    show op (l.eval (Function.update x i b)) (r.eval (Function.update x i b))
      = op (l.eval x) (r.eval x)
    rw [ihl hl, ihr hr]

end GTree

theorem gtree_cnt_zero_not_leaf {n : ℕ} (t : GTree n) (i : Fin n) (h : t.cnt i = 0) :
    i ∉ t.leaves := by
  induction t with
  | leaf j =>
    intro hmem
    have hji : i = j := Finset.mem_singleton.mp hmem
    rw [show GTree.cnt (GTree.leaf j) i = if j = i then 1 else 0 from rfl,
      if_pos hji.symm] at h
    omega
  | cst b =>
    intro hmem
    exact absurd hmem (by simp [GTree.leaves])
  | un op t iht =>
    intro hmem
    exact iht h hmem
  | node op l r ihl ihr =>
    intro hmem
    have hsum : l.cnt i + r.cnt i = 0 := h
    rcases Finset.mem_union.mp hmem with hm | hm
    · exact ihl (by omega) hm
    · exact ihr (by omega) hm

/-- **THE GENERAL-TREE SPLIT THEOREM (proved).** -/
theorem gtree_split_cnt {n : ℕ} (t : GTree n) (i₁ i₂ i₃ : Fin n)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (z : Fin n → Bool) :
    t.cnt i₁ = 1 → t.cnt i₂ = 1 → t.cnt i₃ = 1 →
    Split1 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
    ∨ Split2 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
    ∨ Split3 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) := by
  have hb1 : ∀ (s : GTree n), i₁ ∉ s.leaves → ∀ a a' b c,
      s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
        = s.eval (Function.update (Function.update (Function.update z i₁ a') i₂ b) i₃ c) := by
    intro s hs a a' b c
    have hc : ∀ v : Bool,
        Function.update (Function.update (Function.update z i₁ v) i₂ b) i₃ c
          = Function.update
            (Function.update (Function.update z i₂ b) i₃ c) i₁ v := by
      intro v
      rw [Function.update_comm h12, Function.update_comm h13]
    rw [hc a, hc a', GTree.eval_update_of_not_leaf s i₁ hs,
      GTree.eval_update_of_not_leaf s i₁ hs]
  have hb2 : ∀ (s : GTree n), i₂ ∉ s.leaves → ∀ a b b' c,
      s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
        = s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b') i₃ c) := by
    intro s hs a b b' c
    have hc : ∀ v : Bool,
        Function.update (Function.update (Function.update z i₁ a) i₂ v) i₃ c
          = Function.update
            (Function.update (Function.update z i₁ a) i₃ c) i₂ v := by
      intro v
      rw [Function.update_comm h23]
    rw [hc b, hc b', GTree.eval_update_of_not_leaf s i₂ hs,
      GTree.eval_update_of_not_leaf s i₂ hs]
  have hb3 : ∀ (s : GTree n), i₃ ∉ s.leaves → ∀ a b c c',
      s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
        = s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c') := by
    intro s hs a b c c'
    rw [GTree.eval_update_of_not_leaf s i₃ hs, GTree.eval_update_of_not_leaf s i₃ hs]
  induction t with
  | leaf j =>
    intro hc1 hc2 _
    exfalso
    by_cases hj1 : j = i₁
    · by_cases hj2 : j = i₂
      · exact h12 (hj1.symm.trans hj2)
      · rw [show GTree.cnt (GTree.leaf j) i₂ = if j = i₂ then 1 else 0 from rfl,
          if_neg hj2] at hc2
        omega
    · rw [show GTree.cnt (GTree.leaf j) i₁ = if j = i₁ then 1 else 0 from rfl,
        if_neg hj1] at hc1
      omega
  | cst b =>
    intro hc1 _ _
    exact absurd hc1 (by simp [GTree.cnt])
  | un op t iht =>
    intro hc1 hc2 hc3
    rcases iht hc1 hc2 hc3 with hs | hs | hs
    · exact Or.inl (split1_comp op hs (fun a b c => rfl))
    · exact Or.inr (Or.inl (split2_comp op hs (fun a b c => rfl)))
    · exact Or.inr (Or.inr (split3_comp op hs (fun a b c => rfl)))
  | node op l r ihl ihr =>
    intro hc1 hc2 hc3
    have hs1 : (l.cnt i₁ = 1 ∧ r.cnt i₁ = 0) ∨ (l.cnt i₁ = 0 ∧ r.cnt i₁ = 1) := by
      have hsum : l.cnt i₁ + r.cnt i₁ = 1 := hc1
      omega
    have hs2 : (l.cnt i₂ = 1 ∧ r.cnt i₂ = 0) ∨ (l.cnt i₂ = 0 ∧ r.cnt i₂ = 1) := by
      have hsum : l.cnt i₂ + r.cnt i₂ = 1 := hc2
      omega
    have hs3 : (l.cnt i₃ = 1 ∧ r.cnt i₃ = 0) ∨ (l.cnt i₃ = 0 ∧ r.cnt i₃ = 1) := by
      have hsum : l.cnt i₃ + r.cnt i₃ = 1 := hc3
      omega
    rcases hs1 with ⟨hl1, hr1⟩ | ⟨hl1, hr1⟩
    · rcases hs2 with ⟨hl2, hr2⟩ | ⟨hl2, hr2⟩
      · rcases hs3 with ⟨hl3, hr3⟩ | ⟨hl3, hr3⟩
        · -- LLL: recurse left
          have hfr : ∀ a b c,
              r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                = r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true) := by
            intro a b c
            rw [hb1 r (gtree_cnt_zero_not_leaf r i₁ hr1) a true b c,
              hb2 r (gtree_cnt_zero_not_leaf r i₂ hr2) true b true c,
              hb3 r (gtree_cnt_zero_not_leaf r i₃ hr3) true true c true]
          have he : ∀ a b c,
              (GTree.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                = (fun w => op w (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)))
                  (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) := by
            intro a b c
            show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
              = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true))
            rw [hfr]
          rcases ihl hl1 hl2 hl3 with hs | hs | hs
          · exact Or.inl (split1_comp
              (fun w => op w (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true))) hs he)
          · exact Or.inr (Or.inl (split2_comp
              (fun w => op w (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true))) hs he))
          · exact Or.inr (Or.inr (split3_comp
              (fun w => op w (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true))) hs he))
        · -- LLR: split at c
          refine Or.inr (Or.inr ⟨fun cv y => op y (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ cv)),
            fun a b => l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true), fun a b c => ?_⟩)
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ c))
          rw [hb3 l (gtree_cnt_zero_not_leaf l i₃ hl3) a b c true,
            hb1 r (gtree_cnt_zero_not_leaf r i₁ hr1) a true b c,
            hb2 r (gtree_cnt_zero_not_leaf r i₂ hr2) true b true c]
      · rcases hs3 with ⟨hl3, hr3⟩ | ⟨hl3, hr3⟩
        · -- LRL: split at b
          refine Or.inr (Or.inl ⟨fun bv y => op y (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ bv) i₃ true)),
            fun a c => l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c), fun a b c => ?_⟩)
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ true))
          rw [hb2 l (gtree_cnt_zero_not_leaf l i₂ hl2) a b true c,
            hb1 r (gtree_cnt_zero_not_leaf r i₁ hr1) a true b c,
            hb3 r (gtree_cnt_zero_not_leaf r i₃ hr3) true b c true]
        · -- LRR: split at a
          refine Or.inl ⟨fun av y => op (l.eval (Function.update (Function.update (Function.update z i₁ av) i₂ true) i₃ true)) y,
            fun b c => r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c), fun a b c => ?_⟩
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c))
          rw [hb2 l (gtree_cnt_zero_not_leaf l i₂ hl2) a b true c,
            hb3 l (gtree_cnt_zero_not_leaf l i₃ hl3) a true c true,
            hb1 r (gtree_cnt_zero_not_leaf r i₁ hr1) a true b c]
    · rcases hs2 with ⟨hl2, hr2⟩ | ⟨hl2, hr2⟩
      · rcases hs3 with ⟨hl3, hr3⟩ | ⟨hl3, hr3⟩
        · -- RLL: split at a
          refine Or.inl ⟨fun av y => op y (r.eval (Function.update (Function.update (Function.update z i₁ av) i₂ true) i₃ true)),
            fun b c => l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c), fun a b c => ?_⟩
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ true))
          rw [hb1 l (gtree_cnt_zero_not_leaf l i₁ hl1) a true b c,
            hb2 r (gtree_cnt_zero_not_leaf r i₂ hr2) a b true c,
            hb3 r (gtree_cnt_zero_not_leaf r i₃ hr3) a true c true]
        · -- RLR: split at b
          refine Or.inr (Or.inl ⟨fun bv y => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ bv) i₃ true)) y,
            fun a c => r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c), fun a b c => ?_⟩)
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c))
          rw [hb1 l (gtree_cnt_zero_not_leaf l i₁ hl1) a true b c,
            hb3 l (gtree_cnt_zero_not_leaf l i₃ hl3) true b c true,
            hb2 r (gtree_cnt_zero_not_leaf r i₂ hr2) a b true c]
      · rcases hs3 with ⟨hl3, hr3⟩ | ⟨hl3, hr3⟩
        · -- RRL: split at c
          refine Or.inr (Or.inr ⟨fun cv y => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ cv)) y,
            fun a b => r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true), fun a b c => ?_⟩)
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true))
          rw [hb1 l (gtree_cnt_zero_not_leaf l i₁ hl1) a true b c,
            hb2 l (gtree_cnt_zero_not_leaf l i₂ hl2) true b true c,
            hb3 r (gtree_cnt_zero_not_leaf r i₃ hr3) a b c true]
        · -- RRR: recurse right
          have hfl : ∀ a b c,
              l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                = l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true) := by
            intro a b c
            rw [hb1 l (gtree_cnt_zero_not_leaf l i₁ hl1) a true b c,
              hb2 l (gtree_cnt_zero_not_leaf l i₂ hl2) true b true c,
              hb3 l (gtree_cnt_zero_not_leaf l i₃ hl3) true true c true]
          have he : ∀ a b c,
              (GTree.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                = (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w)
                  (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) := by
            intro a b c
            show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
              = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            rw [hfl]
          rcases ihr hr1 hr2 hr3 with hs | hs | hs
          · exact Or.inl (split1_comp
              (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w) hs he)
          · exact Or.inr (Or.inl (split2_comp
              (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w) hs he))
          · exact Or.inr (Or.inr (split3_comp
              (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w) hs he))

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.gtree_split_cnt
