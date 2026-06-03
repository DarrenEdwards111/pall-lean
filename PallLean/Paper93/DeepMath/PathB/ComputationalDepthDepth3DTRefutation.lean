import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivation

/-!
# Gate 2 core: decision tree ⟹ `LDeriv` resolution refutation

This file discharges the **DT → `LDeriv`** construction flagged as open in
`ComputationalDepthDepth3SwitchingBridge` ("a shallow decision tree for the restricted refuting
circuit yields a resolution refutation of the Tseitin axioms — one clause per leaf, resolved up
the tree").  It is the genuine proof-complexity content of gate 2: the *tree-like resolution*
translation of a refuting decision tree.

The object is a **clause-labeled refutation tree** `DTRef`: each leaf carries an axiom clause that
is *falsified by the root-to-leaf path*, and each internal node branches on a literal `ℓ` (the
`t0` child is the `ℓ`-false branch, the `t1` child the `ℓ`-true branch).  This is exactly the
decision tree of the switching argument with its leaves relabelled by the axiom each path
violates.

The translation, by recursion on the tree:

* `head` — the clause derived at the root of a subtree.  At a leaf it is the axiom; at a node it
  is the **resolvent** of the two children's heads on the branch literal `ℓ`.  Crucially
  `LDeriv`'s resolvent justification is *purely syntactic* (no "pivot present" side condition), so
  this step is always a valid derivation step — the only thing to prove is the *subset invariant*.
* `toList` — the derivation list (head clause first, then the two sub-derivations).
* `head_subset` — **the invariant**: under `Refutes compl t F` (leaves' axioms ⊆ their path's
  false-literal set `F`), `head compl t ⊆ F`.  The two erases in the resolvent peel off exactly
  the two branch literals `ℓ` and `compl ℓ`, dropping the path set back to `F`.
* `dtRef_to_ldderiv` — **the theorem**: a refuting `DTRef` over `Axiom` yields an `LDeriv compl
  Axiom` list that (1) is a valid derivation, (2) contains the empty clause (the root head is `⊆ ∅`
  hence `= ∅`), (3) has length `< 2^(depth+1)`, and (4) every clause has width `≤ depth`.

(4) is the payoff for the switching → lower bound contradiction: a depth-`d` refuting tree gives a
**width-`d`** resolution refutation.  Composed with a width *lower* bound on the Tseitin axioms,
small `d` is a contradiction — the shape of the AC⁰/depth-3 separation at the restricted level.

What this file does **not** do (honest scope): it does not relabel the canonical Boolean decision
tree `BoolDecisionTree` (Bool leaves, `Fin n` queries) into a `DTRef` over Tseitin literals — that
variable↦literal relabelling (turning each `false` leaf into the axiom its path falsifies) is the
remaining bookkeeping bridge, separate from this proof-complexity core.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.RestrictionClauseAlgebra

variable {Lit : Type*} [DecidableEq Lit]

/-- A clause-labeled refutation tree: leaves carry an axiom clause (to be falsified by the
root-to-leaf path), internal nodes branch on a literal `ℓ` — `t0` is the `ℓ`-false branch, `t1`
the `ℓ`-true branch. -/
inductive DTRef (Lit : Type*) where
  | leaf : ResolutionClause Lit → DTRef Lit
  | node : Lit → DTRef Lit → DTRef Lit → DTRef Lit

namespace DTRef

variable {compl : Lit → Lit}

/-- The clause derived at the root of a subtree: the axiom at a leaf, the resolvent of the two
children's heads on the branch literal at a node. -/
def head (compl : Lit → Lit) : DTRef Lit → ResolutionClause Lit
  | leaf C => C
  | node ℓ t0 t1 => ResolutionClause.resolvent compl (head compl t0) (head compl t1) ℓ

/-- The derivation list: head clause first, then the two sub-derivations. -/
def toList (compl : Lit → Lit) : DTRef Lit → List (ResolutionClause Lit)
  | leaf C => [C]
  | node ℓ t0 t1 => head compl (node ℓ t0 t1) :: (toList compl t0 ++ toList compl t1)

/-- Number of leaves. -/
def leaves : DTRef Lit → ℕ
  | leaf _ => 1
  | node _ t0 t1 => t0.leaves + t1.leaves

/-- Tree depth. -/
def depth : DTRef Lit → ℕ
  | leaf _ => 0
  | node _ t0 t1 => max t0.depth t1.depth + 1

/-- Every leaf clause satisfies the axiom predicate. -/
def Labeled (Axiom : ResolutionClause Lit → Prop) : DTRef Lit → Prop
  | leaf C => Axiom C
  | node _ t0 t1 => Labeled Axiom t0 ∧ Labeled Axiom t1

/-- **The refutation condition.**  Relative to the set `F` of literals already forced *false* by
the path above, every leaf's axiom clause is `⊆ F` (falsified by the path); descending the `ℓ`
branch adds `ℓ` to `F`, the `compl ℓ` branch adds `compl ℓ`. -/
def Refutes (compl : Lit → Lit) : DTRef Lit → ResolutionClause Lit → Prop
  | leaf C, F => C ⊆ F
  | node ℓ t0 t1, F => Refutes compl t0 (insert ℓ F) ∧ Refutes compl t1 (insert (compl ℓ) F)

/-- `(insert a s).erase a ⊆ s` — erasing a freshly inserted element drops back into `s`. -/
theorem erase_insert_subset (a : Lit) (s : Finset Lit) : (insert a s).erase a ⊆ s := by
  intro x hx
  rw [Finset.mem_erase] at hx
  rcases Finset.mem_insert.mp hx.2 with h | h
  · exact absurd h hx.1
  · exact h

/-- **The subset invariant.**  Under `Refutes compl t F`, the head clause derived at `t` is
`⊆ F`.  At a node, the resolvent's two erases remove exactly the branch literals `ℓ` and
`compl ℓ` that the children added to `F`, returning the derived clause to `F`. -/
theorem head_subset (t : DTRef Lit) {F : ResolutionClause Lit}
    (h : Refutes compl t F) : head compl t ⊆ F := by
  induction t generalizing F with
  | leaf C => exact h
  | node ℓ t0 t1 ih0 ih1 =>
    obtain ⟨h0, h1⟩ := h
    rw [head, ResolutionClause.resolvent]
    refine Finset.union_subset ?_ ?_
    · exact (Finset.erase_subset_erase ℓ (ih0 h0)).trans (erase_insert_subset ℓ F)
    · exact (Finset.erase_subset_erase (compl ℓ) (ih1 h1)).trans (erase_insert_subset (compl ℓ) F)

/-- The head clause is the first element of the derivation list. -/
theorem head_mem_toList (t : DTRef Lit) : head compl t ∈ toList compl t := by
  cases t with
  | leaf C => simp [head, toList]
  | node ℓ t0 t1 => simp [toList]

/-- **`LDeriv` is closed under concatenation.**  Each clause keeps its justification because
membership in the (smaller) tail lifts to membership in the appended list. -/
theorem ldderiv_append {Axiom : ResolutionClause Lit → Prop}
    {L1 L2 : List (ResolutionClause Lit)}
    (h1 : LDeriv compl Axiom L1) (h2 : LDeriv compl Axiom L2) :
    LDeriv compl Axiom (L1 ++ L2) := by
  induction h1 with
  | nil => simpa using h2
  | @cons C L just _ ih =>
    refine LDeriv.cons ?_ ih
    rcases just with hax | ⟨D, E, p, hD, hE, heq⟩ | ⟨D, hD, hsub⟩
    · exact Or.inl hax
    · exact Or.inr (Or.inl ⟨D, E, p, List.mem_append_left _ hD, List.mem_append_left _ hE, heq⟩)
    · exact Or.inr (Or.inr ⟨D, List.mem_append_left _ hD, hsub⟩)

/-- **The derivation is valid.**  A labelled refutation tree produces an `LDeriv` over `Axiom`:
leaves are axioms, each node's head is the syntactic resolvent of its two children's heads (which
sit in the appended tail). -/
theorem ldderiv_toList {Axiom : ResolutionClause Lit → Prop} (t : DTRef Lit)
    (hlab : Labeled Axiom t) : LDeriv compl Axiom (toList compl t) := by
  induction t with
  | leaf C =>
    refine LDeriv.cons (Or.inl hlab) LDeriv.nil
  | node ℓ t0 t1 ih0 ih1 =>
    obtain ⟨hl0, hl1⟩ := hlab
    have hrest : LDeriv compl Axiom (toList compl t0 ++ toList compl t1) :=
      ldderiv_append (ih0 hl0) (ih1 hl1)
    rw [toList]
    refine LDeriv.cons ?_ hrest
    refine Or.inr (Or.inl ⟨head compl t0, head compl t1, ℓ, ?_, ?_, ?_⟩)
    · exact List.mem_append_left _ (head_mem_toList t0)
    · exact List.mem_append_right _ (head_mem_toList t1)
    · rfl

/-- Derivation length: one clause per node, so `length + 1 ≤ 2·leaves`. -/
theorem length_toList_succ_le (t : DTRef Lit) :
    (toList compl t).length + 1 ≤ 2 * t.leaves := by
  induction t with
  | leaf C => simp [toList, leaves]
  | node ℓ t0 t1 ih0 ih1 =>
    simp only [toList, leaves, List.length_cons, List.length_append]
    omega

/-- A depth-`d` refutation tree has at most `2^d` leaves. -/
theorem leaves_le_two_pow_depth (t : DTRef Lit) : t.leaves ≤ 2 ^ t.depth := by
  induction t with
  | leaf C => simp [leaves, depth]
  | node ℓ t0 t1 ih0 ih1 =>
    simp only [leaves, depth]
    calc t0.leaves + t1.leaves
        ≤ 2 ^ t0.depth + 2 ^ t1.depth := Nat.add_le_add ih0 ih1
      _ ≤ 2 ^ (max t0.depth t1.depth) + 2 ^ (max t0.depth t1.depth) :=
          Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
            (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      _ = 2 ^ (max t0.depth t1.depth + 1) := by rw [pow_succ]; ring

/-- **The width bound.**  Under `Refutes compl t F`, every clause of the derivation has width
`≤ F.card + depth t`.  (The path set grows by one per level but the residual depth shrinks, so
the total stays `≤ F.card + depth`.) -/
theorem width_toList_le (t : DTRef Lit) {F : ResolutionClause Lit}
    (h : Refutes compl t F) :
    ∀ C ∈ toList compl t, C.width ≤ F.card + t.depth := by
  induction t generalizing F with
  | leaf C =>
    intro D hD
    simp only [toList, List.mem_singleton] at hD
    subst hD
    have hsub : D ⊆ F := h
    have := Finset.card_le_card hsub
    simp only [depth, ResolutionClause.width]; omega
  | node ℓ t0 t1 ih0 ih1 =>
    obtain ⟨h0, h1⟩ := h
    intro D hD
    rw [toList, List.mem_cons, List.mem_append] at hD
    rcases hD with rfl | hD0 | hD1
    · have hsub : head compl (node ℓ t0 t1) ⊆ F := head_subset (node ℓ t0 t1) ⟨h0, h1⟩
      have := Finset.card_le_card hsub
      simp only [ResolutionClause.width] at this ⊢; omega
    · have hw := ih0 h0 D hD0
      have hc : (insert ℓ F).card ≤ F.card + 1 := Finset.card_insert_le _ _
      have hm : t0.depth ≤ max t0.depth t1.depth := le_max_left _ _
      simp only [depth]; omega
    · have hw := ih1 h1 D hD1
      have hc : (insert (compl ℓ) F).card ≤ F.card + 1 := Finset.card_insert_le _ _
      have hm : t1.depth ≤ max t0.depth t1.depth := le_max_right _ _
      simp only [depth]; omega

/-- **Gate 2 core: a refuting decision tree yields a short, narrow `LDeriv` resolution
refutation.**  Given a clause-labelled tree `t` whose leaves are axioms (`Labeled`) and whose
every root-to-leaf path falsifies its leaf axiom (`Refutes … ∅`), the derivation list
`toList compl t`:

1. is a valid `LDeriv` over `Axiom`;
2. contains the empty clause (the root head is `⊆ ∅`, hence `= ∅`) — i.e. it is a *refutation*;
3. has length `< 2^(depth+1)`;
4. every clause has width `≤ depth`.

This is the switching → lower-bound contradiction shape: a depth-`d` refuting tree forces a
width-`d` resolution refutation of the axioms. -/
theorem dtRef_to_ldderiv {Axiom : ResolutionClause Lit → Prop} (t : DTRef Lit)
    (hlab : Labeled Axiom t) (href : Refutes compl t (∅ : ResolutionClause Lit)) :
    LDeriv compl Axiom (toList compl t) ∧
      (∅ : ResolutionClause Lit) ∈ toList compl t ∧
      (toList compl t).length < 2 ^ (t.depth + 1) ∧
      (∀ C ∈ toList compl t, C.width ≤ t.depth) := by
  refine ⟨ldderiv_toList t hlab, ?_, ?_, ?_⟩
  · -- empty clause present: the root head is ⊆ ∅, hence ∅
    have hsub : head compl t ⊆ (∅ : ResolutionClause Lit) := head_subset t href
    have hempty : head compl t = (∅ : ResolutionClause Lit) := Finset.subset_empty.mp hsub
    have := head_mem_toList (compl := compl) t
    rwa [hempty] at this
  · -- length bound
    have hL := length_toList_succ_le (compl := compl) t
    have hLe := leaves_le_two_pow_depth t
    have hpow : (2 : ℕ) ^ (t.depth + 1) = 2 * 2 ^ t.depth := by rw [pow_succ]; ring
    omega
  · -- width bound: at root F = ∅
    intro C hC
    have := width_toList_le t href C hC
    simpa using this

end DTRef

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.DTRef.head_subset
#print axioms PallLean.Paper93.DeepMath.PathB.DTRef.dtRef_to_ldderiv
