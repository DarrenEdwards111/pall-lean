import PallLean.Paper93.DeepMath.PathB.ComputationalDepthROTSplit

/-!
# Brick 3a of the `SlackComposes` m = 2 attack: the count-based split theorem

`rot_split` needed full read-once-ness.  For the read-twice trees extracted from
the `TwelveShape` anatomy, only the *triple* variables need single occurrence:

* `ROT.cnt` — leaf-occurrence counts;
* **`rot_split_cnt` (proved)** — a tree in which three distinct variables each
  occur in exactly one leaf splits at one of the three, under any completion.
  The other variables may occur arbitrarily often.  Same eight-way structure as
  `rot_split`, with count-zero blindness replacing disjointness; the leaf case
  is now vacuous (a single leaf cannot carry two distinct count-1 variables).

This is what kills every 12-gate shape whose shared subtree misses one of the
two `AEm 2` gadgets: that gadget's triple has all counts 1 in the extracted
tree, so its `allEq3` restriction would split — refuted by `allEq3_no_split`.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

namespace ROT

/-- Leaf-occurrence count of a variable. -/
def cnt : ROT n → Fin n → ℕ
  | leaf j, i => if j = i then 1 else 0
  | node _ l r, i => l.cnt i + r.cnt i

end ROT

/-- Count zero means the variable is not a leaf. -/
theorem cnt_zero_not_leaf {n : ℕ} (t : ROT n) (i : Fin n) (h : t.cnt i = 0) :
    i ∉ t.leaves := by
  induction t with
  | leaf j =>
    intro hmem
    have hji : i = j := Finset.mem_singleton.mp hmem
    rw [show ROT.cnt (ROT.leaf j) i = if j = i then 1 else 0 from rfl,
      if_pos hji.symm] at h
    omega
  | node op l r ihl ihr =>
    intro hmem
    have hsum : l.cnt i + r.cnt i = 0 := h
    rcases Finset.mem_union.mp hmem with hm | hm
    · exact ihl (by omega) hm
    · exact ihr (by omega) hm

/-- **THE COUNT-BASED SPLIT THEOREM (proved).**  If three distinct variables each
occur in exactly one leaf, the tree splits at one of them under any completion. -/
theorem rot_split_cnt {n : ℕ} (t : ROT n) (i₁ i₂ i₃ : Fin n)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (z : Fin n → Bool) :
    t.cnt i₁ = 1 → t.cnt i₂ = 1 → t.cnt i₃ = 1 →
    Split1 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
    ∨ Split2 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
    ∨ Split3 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) := by
  have hb1 : ∀ (s : ROT n), i₁ ∉ s.leaves → ∀ a a' b c,
      s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
        = s.eval (Function.update (Function.update (Function.update z i₁ a') i₂ b) i₃ c) := by
    intro s hs a a' b c
    have hc : ∀ v : Bool,
        Function.update (Function.update (Function.update z i₁ v) i₂ b) i₃ c
          = Function.update
            (Function.update (Function.update z i₂ b) i₃ c) i₁ v := by
      intro v
      rw [Function.update_comm h12, Function.update_comm h13]
    rw [hc a, hc a', ROT.eval_update_of_not_leaf s i₁ hs,
      ROT.eval_update_of_not_leaf s i₁ hs]
  have hb2 : ∀ (s : ROT n), i₂ ∉ s.leaves → ∀ a b b' c,
      s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
        = s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b') i₃ c) := by
    intro s hs a b b' c
    have hc : ∀ v : Bool,
        Function.update (Function.update (Function.update z i₁ a) i₂ v) i₃ c
          = Function.update
            (Function.update (Function.update z i₁ a) i₃ c) i₂ v := by
      intro v
      rw [Function.update_comm h23]
    rw [hc b, hc b', ROT.eval_update_of_not_leaf s i₂ hs,
      ROT.eval_update_of_not_leaf s i₂ hs]
  have hb3 : ∀ (s : ROT n), i₃ ∉ s.leaves → ∀ a b c c',
      s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
        = s.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c') := by
    intro s hs a b c c'
    rw [ROT.eval_update_of_not_leaf s i₃ hs, ROT.eval_update_of_not_leaf s i₃ hs]
  induction t with
  | leaf j =>
    intro hc1 hc2 _
    exfalso
    by_cases hj1 : j = i₁
    · by_cases hj2 : j = i₂
      · exact h12 (hj1.symm.trans hj2)
      · rw [show ROT.cnt (ROT.leaf j) i₂ = if j = i₂ then 1 else 0 from rfl,
          if_neg hj2] at hc2
        omega
    · rw [show ROT.cnt (ROT.leaf j) i₁ = if j = i₁ then 1 else 0 from rfl,
        if_neg hj1] at hc1
      omega
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
            rw [hb1 r (cnt_zero_not_leaf r i₁ hr1) a true b c,
              hb2 r (cnt_zero_not_leaf r i₂ hr2) true b true c,
              hb3 r (cnt_zero_not_leaf r i₃ hr3) true true c true]
          have he : ∀ a b c,
              (ROT.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
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
          rw [hb3 l (cnt_zero_not_leaf l i₃ hl3) a b c true,
            hb1 r (cnt_zero_not_leaf r i₁ hr1) a true b c,
            hb2 r (cnt_zero_not_leaf r i₂ hr2) true b true c]
      · rcases hs3 with ⟨hl3, hr3⟩ | ⟨hl3, hr3⟩
        · -- LRL: split at b
          refine Or.inr (Or.inl ⟨fun bv y => op y (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ bv) i₃ true)),
            fun a c => l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c), fun a b c => ?_⟩)
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ true))
          rw [hb2 l (cnt_zero_not_leaf l i₂ hl2) a b true c,
            hb1 r (cnt_zero_not_leaf r i₁ hr1) a true b c,
            hb3 r (cnt_zero_not_leaf r i₃ hr3) true b c true]
        · -- LRR: split at a
          refine Or.inl ⟨fun av y => op (l.eval (Function.update (Function.update (Function.update z i₁ av) i₂ true) i₃ true)) y,
            fun b c => r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c), fun a b c => ?_⟩
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c))
          rw [hb2 l (cnt_zero_not_leaf l i₂ hl2) a b true c,
            hb3 l (cnt_zero_not_leaf l i₃ hl3) a true c true,
            hb1 r (cnt_zero_not_leaf r i₁ hr1) a true b c]
    · rcases hs2 with ⟨hl2, hr2⟩ | ⟨hl2, hr2⟩
      · rcases hs3 with ⟨hl3, hr3⟩ | ⟨hl3, hr3⟩
        · -- RLL: split at a
          refine Or.inl ⟨fun av y => op y (r.eval (Function.update (Function.update (Function.update z i₁ av) i₂ true) i₃ true)),
            fun b c => l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c), fun a b c => ?_⟩
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ true))
          rw [hb1 l (cnt_zero_not_leaf l i₁ hl1) a true b c,
            hb2 r (cnt_zero_not_leaf r i₂ hr2) a b true c,
            hb3 r (cnt_zero_not_leaf r i₃ hr3) a true c true]
        · -- RLR: split at b
          refine Or.inr (Or.inl ⟨fun bv y => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ bv) i₃ true)) y,
            fun a c => r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c), fun a b c => ?_⟩)
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c))
          rw [hb1 l (cnt_zero_not_leaf l i₁ hl1) a true b c,
            hb3 l (cnt_zero_not_leaf l i₃ hl3) true b c true,
            hb2 r (cnt_zero_not_leaf r i₂ hr2) a b true c]
      · rcases hs3 with ⟨hl3, hr3⟩ | ⟨hl3, hr3⟩
        · -- RRL: split at c
          refine Or.inr (Or.inr ⟨fun cv y => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ cv)) y,
            fun a b => r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true), fun a b c => ?_⟩)
          show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
            = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true))
          rw [hb1 l (cnt_zero_not_leaf l i₁ hl1) a true b c,
            hb2 l (cnt_zero_not_leaf l i₂ hl2) true b true c,
            hb3 r (cnt_zero_not_leaf r i₃ hr3) a b c true]
        · -- RRR: recurse right
          have hfl : ∀ a b c,
              l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                = l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true) := by
            intro a b c
            rw [hb1 l (cnt_zero_not_leaf l i₁ hl1) a true b c,
              hb2 l (cnt_zero_not_leaf l i₂ hl2) true b true c,
              hb3 l (cnt_zero_not_leaf l i₃ hl3) true true c true]
          have he : ∀ a b c,
              (ROT.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
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

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rot_split_cnt
