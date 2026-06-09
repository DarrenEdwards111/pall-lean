import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Layered

/-!
# Tight switching, step 54: the bottom-gate extractor and size predicate (branch `razborov-recoverRho-wip`)

The structural carrier of the width-aware invariant.  `bottomGates C` collects the clause-lists at the
bottom of an alternating tower (`dnf cs`/`cnf cs ↦ [cs]`, internal `gAnd`/`gOr` recurse through children), and
`BottomBounded w M C` asserts every bottom gate has width `≤ w` and clause-count `≤ M`.  These are the gates a
survivor restriction must shallow (`G = bottomGates C`) and whose post-switch size the clause-count/width
bounds (steps 1/2/53) control, so the terminal `DNF` meets the survivor budget and `hterm` fires on the
*actual* collapsed gate.

* `bottomGates` / `bottomGatesList` — the bottom clause-lists of a tower.
* `bottomGatesList_eq` — the list version is the pointwise flatten.
* `BottomBounded` — width `≤ w` and clause-count `≤ M` on every bottom gate.
* `BottomBounded_dnf` — at a bottom `DNF`, the predicate is exactly the survivor budget's `hw`/`hm`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

-- The clause-lists at the bottom of an alternating tower (mutual with the list version).
mutual
def bottomGates : Layered n → List (List (Clause n))
  | dnf cs => [cs]
  | cnf cs => [cs]
  | gAnd gs => bottomGatesList gs
  | gOr gs => bottomGatesList gs
def bottomGatesList : List (Layered n) → List (List (Clause n))
  | [] => []
  | g :: gs => bottomGates g ++ bottomGatesList gs
end

/-- The list extractor is the pointwise `bottomGates`, flattened. -/
theorem bottomGatesList_eq (gs : List (Layered n)) :
    bottomGatesList gs = (gs.map bottomGates).flatten := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [bottomGatesList, List.map_cons, List.flatten_cons, ih]

/-- **The width/clause-count invariant.**  Every bottom gate of `C` has width `≤ w` and `≤ M` clauses. -/
def BottomBounded (w M : ℕ) (C : Layered n) : Prop :=
  ∀ cs ∈ bottomGates C, (∀ T ∈ cs, T.lits.length ≤ w) ∧ cs.length ≤ M

/-- At a bottom `DNF`, `BottomBounded` is exactly the survivor budget's width (`hw`) and clause-count (`hm`)
hypotheses on that `DNF`. -/
theorem BottomBounded_dnf {w M : ℕ} {cs : List (Clause n)}
    (h : BottomBounded w M (dnf cs)) :
    (∀ T ∈ cs, T.lits.length ≤ w) ∧ cs.length ≤ M :=
  h cs (by simp [bottomGates])

/-- Dual: at a bottom `CNF`, `BottomBounded` gives the width/clause-count bounds on that `CNF`. -/
theorem BottomBounded_cnf {w M : ℕ} {cs : List (Clause n)}
    (h : BottomBounded w M (cnf cs)) :
    (∀ T ∈ cs, T.lits.length ≤ w) ∧ cs.length ≤ M :=
  h cs (by simp [bottomGates])

/-- `BottomBounded` lifts from each child to a `gOr` node (the bottoms of `gOr gs` are the union of the
children's bottoms). -/
theorem BottomBounded_gOr {w M : ℕ} {gs : List (Layered n)}
    (h : ∀ g ∈ gs, BottomBounded w M g) : BottomBounded w M (gOr gs) := by
  intro cs hcs
  rw [bottomGates, bottomGatesList_eq, List.mem_flatten] at hcs
  obtain ⟨l, hl, hcsl⟩ := hcs
  rw [List.mem_map] at hl
  obtain ⟨g, hg, rfl⟩ := hl
  exact h g hg cs hcsl

/-- Dual lift to a `gAnd` node. -/
theorem BottomBounded_gAnd {w M : ℕ} {gs : List (Layered n)}
    (h : ∀ g ∈ gs, BottomBounded w M g) : BottomBounded w M (gAnd gs) := by
  intro cs hcs
  rw [bottomGates, bottomGatesList_eq, List.mem_flatten] at hcs
  obtain ⟨l, hl, hcsl⟩ := hcs
  rw [List.mem_map] at hl
  obtain ⟨g, hg, rfl⟩ := hl
  exact h g hg cs hcsl

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.bottomGatesList_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.BottomBounded_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.BottomBounded_gOr
