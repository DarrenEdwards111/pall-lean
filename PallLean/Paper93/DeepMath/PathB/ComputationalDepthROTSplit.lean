import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSlackComposition

/-!
# Read-once trees: the split theorem and the SAT-side non-realizability

The tree half of the general floor-attainment structure theorem, complete:

* `ROT` — read-once trees (leaves = variables, nodes = arbitrary binary ops), with
  `ReadOnce` demanding disjoint leaf-sets at every node;
* **`rot_split` (proved, tree induction)**: for any read-once tree, any three
  distinct variables, and any completion, the induced three-variable function
  splits at one of the three — the general form of what refuted the 5-gate
  `AllEqual₃` circuit;
* **`AEm_not_ROT` (proved)**: no read-once tree computes `AEm m` for any `m ≥ 1` —
  gadget 0 under the all-true completion is `AllEqual₃`, which splits nowhere;
* `FloorRealizesROT` — the named remaining circuit half: floor circuits realize
  read-once trees (census + fanout are proved; the recursive cone-disjointness
  extraction is the open formalization);
* **`AEm_above_floor_of_extraction` (proved, conditional)**: given the extraction,
  `6m ≤ cbudget (AEm m)` at every `m` — the one-above-floor datapoint.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- Read-once trees: variable leaves, arbitrary binary ops. -/
inductive ROT (n : ℕ) : Type where
  | leaf : Fin n → ROT n
  | node : (Bool → Bool → Bool) → ROT n → ROT n → ROT n

namespace ROT

def eval : ROT n → (Fin n → Bool) → Bool
  | leaf i, x => x i
  | node op l r, x => op (l.eval x) (r.eval x)

def leaves : ROT n → Finset (Fin n)
  | leaf i => {i}
  | node _ l r => l.leaves ∪ r.leaves

def ReadOnce : ROT n → Prop
  | leaf _ => True
  | node _ l r => Disjoint l.leaves r.leaves ∧ ReadOnce l ∧ ReadOnce r

theorem eval_update_of_not_leaf (t : ROT n) (i : Fin n) (hi : i ∉ t.leaves)
    (x : Fin n → Bool) (b : Bool) :
    t.eval (Function.update x i b) = t.eval x := by
  induction t with
  | leaf j =>
    have hj : j ≠ i := by
      intro he
      exact hi (by rw [leaves, Finset.mem_singleton, he])
    show Function.update x i b j = x j
    exact Function.update_of_ne hj b x
  | node op l r ihl ihr =>
    have hl : i ∉ l.leaves := fun h => hi (by rw [leaves, Finset.mem_union]; exact Or.inl h)
    have hr : i ∉ r.leaves := fun h => hi (by rw [leaves, Finset.mem_union]; exact Or.inr h)
    show op (l.eval (Function.update x i b)) (r.eval (Function.update x i b))
      = op (l.eval x) (r.eval x)
    rw [ihl hl, ihr hr]

end ROT

/-- Split of a three-variable function at its first, second, third argument. -/
def Split1 (F : Bool → Bool → Bool → Bool) : Prop :=
  ∃ op g : Bool → Bool → Bool, ∀ a b c, F a b c = op a (g b c)

def Split2 (F : Bool → Bool → Bool → Bool) : Prop :=
  ∃ op g : Bool → Bool → Bool, ∀ a b c, F a b c = op b (g a c)

def Split3 (F : Bool → Bool → Bool → Bool) : Prop :=
  ∃ op g : Bool → Bool → Bool, ∀ a b c, F a b c = op c (g a b)

/-- Splits survive unary post-composition. -/
theorem split1_comp {F F' : Bool → Bool → Bool → Bool} (h : Bool → Bool)
    (hs : Split1 F') (he : ∀ a b c, F a b c = h (F' a b c)) : Split1 F := by
  obtain ⟨op, g, hop⟩ := hs
  exact ⟨fun x y => h (op x y), g, fun a b c => by rw [he, hop]⟩

theorem split2_comp {F F' : Bool → Bool → Bool → Bool} (h : Bool → Bool)
    (hs : Split2 F') (he : ∀ a b c, F a b c = h (F' a b c)) : Split2 F := by
  obtain ⟨op, g, hop⟩ := hs
  exact ⟨fun x y => h (op x y), g, fun a b c => by rw [he, hop]⟩

theorem split3_comp {F F' : Bool → Bool → Bool → Bool} (h : Bool → Bool)
    (hs : Split3 F') (he : ∀ a b c, F a b c = h (F' a b c)) : Split3 F := by
  obtain ⟨op, g, hop⟩ := hs
  exact ⟨fun x y => h (op x y), g, fun a b c => by rw [he, hop]⟩

/-- **THE READ-ONCE SPLIT THEOREM (proved).**  Any read-once tree, restricted to any
three distinct variables under any completion, splits at one of the three. -/
theorem rot_split {n : ℕ} (t : ROT n) (hro : ROT.ReadOnce t) (i₁ i₂ i₃ : Fin n)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) (z : Fin n → Bool) :
    Split1 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
    ∨ Split2 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
    ∨ Split3 (fun a b c => t.eval
        (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) := by
  -- blindness helpers, one per variable, valid for any subtree missing that leaf
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
  have hval : ∀ (j : Fin n) (a b c : Bool),
      (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c) j
        = if j = i₃ then c else if j = i₂ then b else if j = i₁ then a else z j := by
    intro j a b c
    by_cases h3 : j = i₃
    · rw [if_pos h3, h3, Function.update_self]
    · have e3 : Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c j
          = Function.update (Function.update z i₁ a) i₂ b j :=
        Function.update_of_ne h3 c (Function.update (Function.update z i₁ a) i₂ b)
      rw [if_neg h3, e3]
      by_cases h2 : j = i₂
      · rw [if_pos h2, h2, Function.update_self]
      · have e2 : Function.update (Function.update z i₁ a) i₂ b j
            = Function.update z i₁ a j :=
          Function.update_of_ne h2 b (Function.update z i₁ a)
        rw [if_neg h2, e2]
        by_cases h1 : j = i₁
        · rw [if_pos h1, h1, Function.update_self]
        · have e1 : Function.update z i₁ a j = z j := Function.update_of_ne h1 a z
          rw [if_neg h1, e1]
  revert hro
  induction t with
  | leaf j =>
    intro _
    by_cases h3 : j = i₃
    · refine Or.inr (Or.inr ⟨fun cv _ => cv, fun _ _ => false, fun a b c => ?_⟩)
      show (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c) j = c
      rw [hval, if_pos h3]
    · by_cases h2 : j = i₂
      · refine Or.inr (Or.inl ⟨fun bv _ => bv, fun _ _ => false, fun a b c => ?_⟩)
        show (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c) j = b
        rw [hval, if_neg h3, if_pos h2]
      · by_cases h1 : j = i₁
        · refine Or.inl ⟨fun av _ => av, fun _ _ => false, fun a b c => ?_⟩
          show (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c) j = a
          rw [hval, if_neg h3, if_neg h2, if_pos h1]
        · refine Or.inl ⟨fun _ y => y, fun _ _ => z j, fun a b c => ?_⟩
          show (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c) j = z j
          rw [hval, if_neg h3, if_neg h2, if_neg h1]
  | node op l r ihl ihr =>
    intro hro
    obtain ⟨hdisj, hl, hr⟩ := hro
    by_cases m1 : i₁ ∈ (ROT.node op l r).leaves
    · by_cases m2 : i₂ ∈ (ROT.node op l r).leaves
      · by_cases m3 : i₃ ∈ (ROT.node op l r).leaves
        · rcases Finset.mem_union.mp m1 with m1l | m1r
          · rcases Finset.mem_union.mp m2 with m2l | m2r
            · rcases Finset.mem_union.mp m3 with m3l | m3r
              · -- LLL: recurse left
                have hfr : ∀ a b c,
                    r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                      = r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true) := by
                  intro a b c
                  rw [hb1 r (Finset.disjoint_left.mp hdisj m1l) a true b c,
                    hb2 r (Finset.disjoint_left.mp hdisj m2l) true b true c,
                    hb3 r (Finset.disjoint_left.mp hdisj m3l) true true c true]
                have he : ∀ a b c,
                    (ROT.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                      = (fun w => op w (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)))
                        (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) := by
                  intro a b c
                  show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                    = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true))
                  rw [hfr]
                rcases ihl hl with hs | hs | hs
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
                rw [hb3 l (Finset.disjoint_right.mp hdisj m3r) a b c true,
                  hb1 r (Finset.disjoint_left.mp hdisj m1l) a true b c,
                  hb2 r (Finset.disjoint_left.mp hdisj m2l) true b true c]
            · rcases Finset.mem_union.mp m3 with m3l | m3r
              · -- LRL: split at b
                refine Or.inr (Or.inl ⟨fun bv y => op y (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ bv) i₃ true)),
                  fun a c => l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c), fun a b c => ?_⟩)
                show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                  = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ true))
                rw [hb2 l (Finset.disjoint_right.mp hdisj m2r) a b true c,
                  hb1 r (Finset.disjoint_left.mp hdisj m1l) a true b c,
                  hb3 r (Finset.disjoint_left.mp hdisj m3l) true b c true]
              · -- LRR: split at a
                refine Or.inl ⟨fun av y => op (l.eval (Function.update (Function.update (Function.update z i₁ av) i₂ true) i₃ true)) y,
                  fun b c => r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c), fun a b c => ?_⟩
                show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                  = op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c))
                rw [hb2 l (Finset.disjoint_right.mp hdisj m2r) a b true c,
                  hb3 l (Finset.disjoint_right.mp hdisj m3r) a true c true,
                  hb1 r (Finset.disjoint_left.mp hdisj m1l) a true b c]
          · rcases Finset.mem_union.mp m2 with m2l | m2r
            · rcases Finset.mem_union.mp m3 with m3l | m3r
              · -- RLL: split at a
                refine Or.inl ⟨fun av y => op y (r.eval (Function.update (Function.update (Function.update z i₁ av) i₂ true) i₃ true)),
                  fun b c => l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c), fun a b c => ?_⟩
                show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                  = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ true))
                rw [hb1 l (Finset.disjoint_right.mp hdisj m1r) a true b c,
                  hb2 r (Finset.disjoint_left.mp hdisj m2l) a b true c,
                  hb3 r (Finset.disjoint_left.mp hdisj m3l) a true c true]
              · -- RLR: split at b
                refine Or.inr (Or.inl ⟨fun bv y => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ bv) i₃ true)) y,
                  fun a c => r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c), fun a b c => ?_⟩)
                show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                  = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c))
                rw [hb1 l (Finset.disjoint_right.mp hdisj m1r) a true b c,
                  hb3 l (Finset.disjoint_right.mp hdisj m3r) true b c true,
                  hb2 r (Finset.disjoint_left.mp hdisj m2l) a b true c]
            · rcases Finset.mem_union.mp m3 with m3l | m3r
              · -- RRL: split at c
                refine Or.inr (Or.inr ⟨fun cv y => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ cv)) y,
                  fun a b => r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true), fun a b c => ?_⟩)
                show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                  = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true))
                rw [hb1 l (Finset.disjoint_right.mp hdisj m1r) a true b c,
                  hb2 l (Finset.disjoint_right.mp hdisj m2r) true b true c,
                  hb3 r (Finset.disjoint_left.mp hdisj m3l) a b c true]
              · -- RRR: recurse right
                have hfl : ∀ a b c,
                    l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                      = l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true) := by
                  intro a b c
                  rw [hb1 l (Finset.disjoint_right.mp hdisj m1r) a true b c,
                    hb2 l (Finset.disjoint_right.mp hdisj m2r) true b true c,
                    hb3 l (Finset.disjoint_right.mp hdisj m3r) true true c true]
                have he : ∀ a b c,
                    (ROT.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)
                      = (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w)
                        (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) := by
                  intro a b c
                  show op (l.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                    = op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) (r.eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c))
                  rw [hfl]
                rcases ihr hr with hs | hs | hs
                · exact Or.inl (split1_comp
                    (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w) hs he)
                · exact Or.inr (Or.inl (split2_comp
                    (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w) hs he))
                · exact Or.inr (Or.inr (split3_comp
                    (fun w => op (l.eval (Function.update (Function.update (Function.update z i₁ true) i₂ true) i₃ true)) w) hs he))
        · refine Or.inr (Or.inr ⟨fun _ y => y,
            fun a b => (ROT.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ true),
            fun a b c => ?_⟩)
          exact hb3 (ROT.node op l r) m3 a b c true
      · refine Or.inr (Or.inl ⟨fun _ y => y,
          fun a c => (ROT.node op l r).eval (Function.update (Function.update (Function.update z i₁ a) i₂ true) i₃ c),
          fun a b c => ?_⟩)
        exact hb2 (ROT.node op l r) m2 a b true c
    · refine Or.inl ⟨fun _ y => y,
        fun b c => (ROT.node op l r).eval (Function.update (Function.update (Function.update z i₁ true) i₂ b) i₃ c),
        fun a b c => ?_⟩
      exact hb1 (ROT.node op l r) m1 a true b c

/-! ### The SAT side: `AEm` is not read-once realizable -/

/-- Gadget 0 under the all-true completion is exactly `AllEqual₃`. -/
theorem AEm_gadget_allEq3 (m : ℕ) (h0 : (0:ℕ) < 3 * m) (h1 : (1:ℕ) < 3 * m)
    (h2 : (2:ℕ) < 3 * m) :
    (fun a b c => AEm m (Function.update (Function.update (Function.update
        (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ c))
      = allEq3 := by
  funext a b c
  have hval3 : ∀ (t : ℕ) (h : t < 3 * m),
      (Function.update (Function.update (Function.update
        (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ c) ⟨t, h⟩
      = if t = 2 then c else if t = 1 then b else if t = 0 then a else true := by
    intro t h
    by_cases ht2 : t = 2
    · rw [if_pos ht2]
      have he : (⟨t, h⟩ : Fin (3*m)) = ⟨2, h2⟩ := Fin.ext ht2
      rw [he, Function.update_self]
    · have hne2 : (⟨t, h⟩ : Fin (3*m)) ≠ ⟨2, h2⟩ := fun he => ht2 (congrArg Fin.val he)
      have e2 : (Function.update (Function.update (Function.update
          (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ c) ⟨t, h⟩
          = (Function.update (Function.update
            (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨t, h⟩ :=
        Function.update_of_ne hne2 c (Function.update (Function.update
          (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b)
      rw [if_neg ht2, e2]
      by_cases ht1 : t = 1
      · rw [if_pos ht1]
        have he : (⟨t, h⟩ : Fin (3*m)) = ⟨1, h1⟩ := Fin.ext ht1
        rw [he, Function.update_self]
      · have hne1 : (⟨t, h⟩ : Fin (3*m)) ≠ ⟨1, h1⟩ := fun he => ht1 (congrArg Fin.val he)
        have e1 : (Function.update (Function.update
            (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨t, h⟩
            = (Function.update (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨t, h⟩ :=
          Function.update_of_ne hne1 b
            (Function.update (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a)
        rw [if_neg ht1, e1]
        by_cases ht0 : t = 0
        · rw [if_pos ht0]
          have he : (⟨t, h⟩ : Fin (3*m)) = ⟨0, h0⟩ := Fin.ext ht0
          rw [he, Function.update_self]
        · have hne0 : (⟨t, h⟩ : Fin (3*m)) ≠ ⟨0, h0⟩ := fun he => ht0 (congrArg Fin.val he)
          have e0 : (Function.update (fun _ : Fin (3*m) => true) ⟨0, h0⟩ a) ⟨t, h⟩
              = true :=
            Function.update_of_ne hne0 a (fun _ : Fin (3*m) => true)
          rw [if_neg ht0, e0]
  have h0m : 0 < m := by omega
  show ((List.finRange m).all _) = allEq3 a b c
  cases hv : allEq3 a b c
  · refine Bool.eq_false_iff.mpr ?_
    intro hall
    rw [List.all_eq_true] at hall
    have hg := hall ⟨0, h0m⟩ (List.mem_finRange _)
    rw [hval3, hval3, hval3] at hg
    rw [show ((⟨0, h0m⟩ : Fin m) : ℕ) = 0 from rfl] at hg
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_pos (by omega), if_pos (by omega)] at hg
    rw [hv] at hg
    exact absurd hg (by decide)
  · rw [List.all_eq_true]
    intro j _
    by_cases hj0 : j.val = 0
    · rw [hval3, hval3, hval3,
        if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      exact hv
    · rw [hval3, hval3, hval3,
        if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl

/-- **`AEm` is not read-once realizable (proved)**: gadget 0 is an unsplittable
triple. -/
theorem AEm_not_ROT (m : ℕ) (hm : 1 ≤ m) :
    ¬ ∃ t : ROT (3 * m), ROT.ReadOnce t ∧ t.eval = AEm m := by
  rintro ⟨t, hro, hev⟩
  have h0 : (0:ℕ) < 3 * m := by omega
  have h1 : (1:ℕ) < 3 * m := by omega
  have h2 : (2:ℕ) < 3 * m := by omega
  have hsp := rot_split t hro ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩
    (by intro he; simp at he) (by intro he; simp at he) (by intro he; simp at he)
    (fun _ => true)
  rw [hev, AEm_gadget_allEq3 m h0 h1 h2] at hsp
  rcases hsp with h | h | h
  · exact allEq3_no_split_a h
  · exact allEq3_no_split_b h
  · exact allEq3_no_split_c h

/-! ### The named circuit half and the conditional cash-out -/

/-- **The remaining circuit half, named**: floor circuits realize read-once trees.
Census and fanout are proved; the recursive cone-disjointness extraction is the
open formalization. -/
def FloorRealizesROT : Prop := ∀ (n : ℕ) (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)), computes c f → c.length + 1 = 2 * (depSet f).card →
    ∃ t : ROT n, ROT.ReadOnce t ∧ t.eval = f

/-- **The `6m` datapoint, conditional on the extraction (proved)**: one above the
floor at every `m`. -/
theorem AEm_above_floor_of_extraction (hext : FloorRealizesROT) (m : ℕ)
    (hm : 1 ≤ m) : 6 * m ≤ cbudget (AEm m) := by
  rcases Nat.lt_or_ge (cbudget (AEm m)) (6 * m) with h | h
  · exfalso
    obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty (AEm m))
    have hclen' : c.length = cbudget (AEm m) := hclen
    have hfloor := cbudget_AEm_floor m hm
    have hlen : c.length + 1 = 2 * (depSet (AEm m)).card := by
      rw [depSet_AEm, Finset.card_univ, Fintype.card_fin]
      omega
    exact AEm_not_ROT m hm (hext (3 * m) (AEm m) c hcomp hlen)
  · exact h

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.rot_split
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_not_ROT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_above_floor_of_extraction
