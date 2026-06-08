import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Circuit

/-!
# Block-DT model, foundation 16: one formal depth-reduction theorem `d → d-1` over `Circ` (branch only)

The headline of the AC⁰ depth-reduction pipeline, stated and proved on the concrete circuit datatype:

> Under a good restriction (already applied: every bottom gate is a shallow decision tree of depth `≤ w`),
> a depth-3 fragment `AND` over those gates is equivalent to a depth-2 CNF circuit whose every bottom
> `OR`-clause has fan-in `≤ w`.

This is one switching round in datatype form: swap (each shallow DT ↦ its width-`≤ w` CNF) + collapse
(`AND`-of-`AND`s flattens the gate layer into the top `AND`).  The result is *one alternation level
shallower* with *controlled bottom width* — exactly `depth d → d-1`.

* `cnfToCirc` / `cnfToCirc_eval` — a width-list CNF as a `Circ`, eval = `cnfSat`.
* `Circ.foldr_max_le`, `height_cnfToCirc_le` — the CNF circuit has alternation height `≤ 2`.
* `and_trees_depth_reduction` — **the theorem**: `AND` of shallow-DT gates ≡ one bounded-width CNF.
* `and_trees_cnf_width` / `and_trees_height_le` — controlled bottom width `≤ w` and height `≤ 2`.

Iterating (with a fresh good restriction per round, supplied by `circuit_collapse_exists`) drives the
depth down level by level.  Clean, no `sorry`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

namespace DTree

variable {n : ℕ}

/-- A width-list CNF (`∀` clauses, each an `∃` over literals) as an alternating circuit. -/
def cnfToCirc (cs : List (List (Lit n))) : Circ n :=
  Circ.and (cs.map (fun c => Circ.or (c.map (fun p => Circ.lit p.1 p.2))))

/-- `cnfToCirc` computes the CNF it encodes. -/
theorem cnfToCirc_eval (cs : List (List (Lit n))) (x : Fin n → Bool) :
    Circ.eval x (cnfToCirc cs) = true ↔ cnfSat x cs := by
  rw [cnfToCirc, Circ.eval_and_iff, cnfSat]
  constructor
  · intro h c hc
    have hor := h (Circ.or (c.map (fun p => Circ.lit p.1 p.2))) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    rw [Circ.eval_or_iff] at hor
    obtain ⟨b, hb, hev⟩ := hor
    rw [List.mem_map] at hb
    obtain ⟨p, hp, rfl⟩ := hb
    exact ⟨p, hp, of_decide_eq_true hev⟩
  · intro h c' hc'
    rw [List.mem_map] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    rw [Circ.eval_or_iff]
    obtain ⟨p, hp, hpx⟩ := h c hc
    exact ⟨Circ.lit p.1 p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, decide_eq_true hpx⟩

/-- `toCirc` is `cnfToCirc` of the rejecting-path CNF. -/
theorem toCirc_eq_cnfToCirc (t : DTree n) : t.toCirc = cnfToCirc t.toCNF := rfl

end DTree

namespace Circ

variable {n : ℕ}

/-- An `OR` of literals has alternation height `1`. -/
theorem height_or_lits (c : List (DTree.Lit n)) :
    height (or (c.map (fun p => lit p.1 p.2))) = 1 := by
  have hz : heightList (c.map (fun p => lit p.1 p.2)) = 0 := by
    apply Nat.le_zero.mp
    apply heightList_le
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨p, _, rfl⟩ := ha
    simp [height]
  show heightList (c.map (fun p => lit p.1 p.2)) + 1 = 1
  rw [hz]

/-- The CNF circuit has alternation height `≤ 2`. -/
theorem height_cnfToCirc_le (cs : List (List (DTree.Lit n))) :
    height (DTree.cnfToCirc cs) ≤ 2 := by
  show heightList (cs.map (fun c => or (c.map (fun p => lit p.1 p.2)))) + 1 ≤ 2
  have hb : heightList (cs.map (fun c => or (c.map (fun p => lit p.1 p.2)))) ≤ 1 := by
    apply heightList_le
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨c, _, rfl⟩ := ha
    rw [height_or_lits]
  omega

end Circ

namespace DTree

variable {n : ℕ}

/-- **One depth-reduction step `d → d-1` over `Circ`.**  An `AND` of shallow decision-tree gates (each
realised as its CNF circuit `toCirc`) is equivalent to a *single* CNF circuit over the concatenated
clauses — the gate `AND`-layer absorbed into the top `AND` via the swap + associativity collapse. -/
theorem and_trees_depth_reduction (ts : List (DTree n)) (x : Fin n → Bool) :
    Circ.eval x (Circ.and (ts.map toCirc)) = true
      ↔ Circ.eval x (cnfToCirc (ts.flatMap toCNF)) = true := by
  rw [Circ.eval_and_iff, cnfToCirc_eval, ← bigAnd_eq_cnf]
  constructor
  · intro h t ht
    have := h t.toCirc (List.mem_map.mpr ⟨t, ht, rfl⟩)
    rwa [toCirc_eval] at this
  · intro h c' hc'
    rw [List.mem_map] at hc'
    obtain ⟨t, ht, rfl⟩ := hc'
    rw [toCirc_eval]
    exact h t ht

/-- **Controlled bottom width.**  If every gate has depth `≤ w`, every `OR`-clause of the reduced CNF
circuit has fan-in `≤ w`. -/
theorem and_trees_cnf_width (ts : List (DTree n)) (w : ℕ) (hw : ∀ t ∈ ts, t.depth ≤ w) :
    ∀ c ∈ ts.flatMap toCNF, (c.map (fun p => Circ.lit p.1 p.2)).length ≤ w := by
  intro c hc
  rw [List.length_map]
  exact bigAndCNF_width ts w hw c hc

/-- **Depth dropped.**  The reduced circuit has alternation height `≤ 2` (vs height `3` for the
`AND`-of-CNF-gates it replaces). -/
theorem and_trees_height_le (ts : List (DTree n)) :
    Circ.height (cnfToCirc (ts.flatMap toCNF)) ≤ 2 :=
  Circ.height_cnfToCirc_le _

end DTree

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.cnfToCirc_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.and_trees_depth_reduction
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.DTree.and_trees_height_le
