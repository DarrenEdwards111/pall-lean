import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestBranch

/-!
# The `(2w)^depth` label of the full deepest branch — concretizing `canonicalDT.depth = s`

`deepestPath_length_eq_depth` shows the depth is a concrete branch length:
`(deepestPath cs fuel σ).length = (canonicalDT cs fuel σ).depth`.  But `deepestPath` records
`(litVar ℓ, bit)` per step — variable *names* over `Fin n`, which carry no `(2w)^s` bound.  The
switching count needs each step labelled by the *position* of the queried literal inside its active
clause (`< w`), plus the descent bit: a `(2w)`-valued label per step.

This file builds that label for the **full** deepest branch (both satisfy- and falsify-steps,
unlike the satisfy-only `deepestSatSeq`), and proves the two facts that make `{ρ : depth = s}`
a `(2w)^s`-labelable set:

* `deepestPathLabel` — per step, `(idxOf ℓ in the active clause, descent bit)`.
* `deepestPathLabel_length_eq_depth` — its length **equals the depth** (so `{depth = s}` is exactly
  `{deepestPathLabel.length = s}`).
* `deepestPathLabel_idx_lt` — every recorded position is `< w` (clause width `≤ w`), so the label
  lives in `(Fin w × Bool)^s`, of cardinality `(2w)^s`.

## The remaining irreducible core (honest)

These give the *correct object* for the tight `depth ≤ s` count: the deepest branch, labelled into
`(2w)^s`.  What is **not** done here (and **not** faked) is the **decoder/injectivity**: recovering
`ρ` from the deepest leaf's end-state plus this label.  A falsify-step's variable is read off the
end-state (it carries a false literal), but a **satisfy-step**'s variable need not be — so the
decoder must *identify the active clause at each step* from the end-state, which is Håstad's forward
reconstruction (the same wall isolated as `hdec` in `replay_switching_count`).  Lower bound
(`canonicalDT_depth_ge_replay`: the falsify branch realises `depth ≥ s`) plus this label
(`depth = deepestPathLabel.length`, indices `< w`) bracket exactly what is and isn't proved.  The
identity `canonicalDT.depth = s` is thus reduced to that single decoder, with the count's label
space now provably `(2w)^s`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The **position/bit label of the deepest branch**: parallel to `deepestPath`, but recording the
*index of the queried literal inside its active clause* (the `Fin w` component) together with the
descent bit, instead of the variable name. -/
def deepestPathLabel (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (ℕ × Bool)
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
          then (T.lits.idxOf ℓ, false) :: deepestPathLabel cs fuel (fixVar σ (litVar ℓ) false)
          else (T.lits.idxOf ℓ, true) :: deepestPathLabel cs fuel (fixVar σ (litVar ℓ) true)

/-- **The deepest-branch label realises the depth.**  `(deepestPathLabel cs fuel σ).length = depth`.
Same control flow as `deepestPath`; the recorded first component (position vs variable) does not
affect the length.  So `{depth = s}` is exactly `{deepestPathLabel.length = s}`. -/
theorem deepestPathLabel_length_eq_depth (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool),
      (deepestPathLabel cs fuel σ).length = (canonicalDT cs fuel σ).depth := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ
    rw [deepestPathLabel, canonicalDT]
    split <;> simp [BoolDecisionTree.depth]
  | succ fuel ih =>
    intro σ
    rw [deepestPathLabel]
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

/-- **Width feasibility of the deepest-branch label.**  Every recorded position is `< w` when each
clause has width `≤ w`: the queried literal is the head of the active clause's free literals, hence a
member of the clause, so its index is below the clause length `≤ w`.  Thus the label lands in
`(Fin w × Bool)^s` (cardinality `(2w)^s`). -/
theorem deepestPathLabel_idx_lt (cs : List (Clause n)) {w : ℕ}
    (hw : ∀ C ∈ cs, C.lits.length ≤ w) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool), ∀ p ∈ deepestPathLabel cs fuel σ, p.1 < w := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ p hp
    rw [deepestPathLabel] at hp
    exact absurd hp (by simp)
  | succ fuel ih =>
    intro σ p hp
    rw [deepestPathLabel] at hp
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp only [hany, if_true] at hp; exact absurd hp (by simp)
    | false =>
      simp only [hany, Bool.false_eq_true, if_false] at hp
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => simp only [hact] at hp; exact absurd hp (by simp)
      | some T =>
        simp only [hact] at hp
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp only [hh] at hp; exact absurd hp (by simp)
        | some ℓ =>
          have hℓT : ℓ ∈ T.lits :=
            (List.mem_filter.mp (List.mem_of_mem_head? hh)).1
          have hTmem : T ∈ cs := by
            have hf : cs.find?
                (fun T => !SwitchingCounting.termFalsified σ T &&
                  decide (0 < (SwitchingCounting.freeLits σ T).length)) = some T := by
              unfold SwitchingCounting.activeTerm at hact
              simpa [hany] using hact
            exact List.mem_of_find?_eq_some hf
          have hidx : T.lits.idxOf ℓ < w :=
            lt_of_lt_of_le (List.idxOf_lt_length_of_mem hℓT) (hw T hTmem)
          simp only [hh] at hp
          split at hp <;>
          · rcases List.mem_cons.mp hp with hpe | hpr
            · rw [hpe]; exact hidx
            · exact ih _ _ hpr

/-- **The depth-bad set is the deepest-branch label-length set.**  For the canonical fuel
`= stars ρ`, `{ρ : depth = s}` is exactly `{ρ : (deepestPathLabel cs (stars ρ) ρ).length = s}`.  So
the set the collapse must bound is, on the nose, a *label-length* set over the concrete `(2w)^s`
label space — the remaining gap being solely the injective decoder for that label. -/
theorem depthBad_eq_labelLenBad (cs : List (Clause n)) (s : ℕ) :
    Finset.univ.filter (fun ρ : Restriction n =>
        (canonicalDT cs (SwitchingCounting.stars ρ) ρ).depth = s)
      = Finset.univ.filter (fun ρ : Restriction n =>
        (deepestPathLabel cs (SwitchingCounting.stars ρ) ρ).length = s) := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [deepestPathLabel_length_eq_depth]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestPathLabel_length_eq_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestPathLabel_idx_lt
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.depthBad_eq_labelLenBad
