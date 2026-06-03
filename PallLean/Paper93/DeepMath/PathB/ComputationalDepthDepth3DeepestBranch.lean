import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthReplayTie

/-!
# The deepest branch: concretizing the object the depth-count must encode

Bounding `{ρ : (canonicalDT cs (stars ρ) ρ).depth ≥ s}` (the tight `depth ≤ s` direction) requires
encoding the *deepest* root-to-leaf branch — the switching count for tree depth.  The first step is
to make that branch concrete.

* `deepestPath` — the canonical deepest branch: at each query node, descend into whichever child is
  deeper (ties to the falsify/`false` side), recording `(litVar ℓ, bit)` per step.
* `deepestPath_length_eq_depth` — **`(deepestPath cs fuel σ).length = (canonicalDT cs fuel σ).depth`**:
  the deepest branch realises the depth exactly.  Proved by induction, the node case picking the
  `max`-depth child (`Nat.max_eq_left`/`_right`).

So the depth is a *concrete canonical path length*, and `{depth ≥ s}` is `{deepestPath.length ≥ s}`.

## The remaining irreducible core (honest)

Bounding `{ρ : deepestPath.length ≥ s}` by `|Short|·(2w)^s` needs: encode the deepest path's `s`
steps as a `(2w)^s` label (position-in-active-clause + bit), and a decoder recovering the path's
selected variables from the end-state (the deepest leaf's restriction) plus that label.  Unlike the
*falsify* path — where every queried variable carries a *false* literal, so the selected set is read
off the end-state with no label (`decodedSel_eq_replaySel`, the discharged `hdec` for the
nothing-falsified regime) — a general branch's queried variables need not be false literals (a `true`
step satisfies, not falsifies), so the label is genuinely needed and the decoder faces the
active-clause-identification core.

`deepestPath` + `deepestPath_length_eq_depth` provide the object; its `(2w)^s` decoder for general
(non-falsify) branches is the irreducible deepest-branch switching lemma, **not** discharged here and
**not** faked.  `canonicalDT_depth_ge_replay` (the falsify branch realises a *lower* bound on depth)
plus this (the deepest branch realises depth *exactly*) bracket precisely what is and isn't proved.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The canonical **deepest branch** of `canonicalDT`: descend into the deeper child at each query
node (ties to the `false`/falsify side), recording `(litVar ℓ, bit)`. -/
def deepestPath (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (Fin n × Bool)
  | 0, _ => []
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then []
    else match SwitchingCounting.activeTerm cs σ with
      | none => []
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => []
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then (litVar ℓ, false) :: deepestPath cs fuel (fixVar σ (litVar ℓ) false)
          else (litVar ℓ, true) :: deepestPath cs fuel (fixVar σ (litVar ℓ) true)

/-- **The deepest branch realises the depth.**  `(deepestPath cs fuel σ).length = depth`. -/
theorem deepestPath_length_eq_depth (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool),
      (deepestPath cs fuel σ).length = (canonicalDT cs fuel σ).depth := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ
    rw [deepestPath, canonicalDT]
    split <;> simp [BoolDecisionTree.depth]
  | succ fuel ih =>
    intro σ
    rw [deepestPath]
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [canonicalDT]; simp [hany, BoolDecisionTree.depth]
    | false =>
      simp only [hany, Bool.false_eq_true, if_false]
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => rw [canonicalDT]; simp [hany, hact, BoolDecisionTree.depth]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => rw [canonicalDT]; simp [hany, hact, hh, BoolDecisionTree.depth]
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          rw [canonicalDT_branch hany hatl]
          simp only [hh, BoolDecisionTree.depth]
          split
          · rename_i hle
            rw [List.length_cons, ih, Nat.max_eq_left hle]
          · rename_i hlt
            rw [List.length_cons, ih, Nat.max_eq_right (le_of_lt (Nat.lt_of_not_le hlt))]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestPath_length_eq_depth
