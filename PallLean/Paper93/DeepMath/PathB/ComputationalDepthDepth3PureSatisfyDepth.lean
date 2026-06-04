import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestBranch

/-!
# Pure-satisfy regime: the position count is the tree depth

The pure-satisfy switching count is phrased via the number of satisfy positions
`(deepestSatPos cs F ρ).length`.  In the pure-satisfy regime *every* deepest-branch step is a satisfy
step, so this equals the full branch length `(deepestPath cs F ρ).length`, which is exactly the
canonical decision-tree depth `(canonicalDT cs F ρ).depth` (`deepestPath_length_eq_depth`).

So the count becomes a genuine **depth** switching bound — the form that feeds the collapse pipeline
(`widthBad` / G1-core): `{pure-satisfy ρ : depth = s}` has cardinality `≤ |Short|·(2w)^s`.

* `deepestSatPos_length_eq_deepestPath_length` — in the pure-satisfy regime, the satisfy-position
  count equals the full branch length.
* `deepestSatPos_length_eq_depth` — hence equals the canonical decision-tree depth.
* `pure_satisfy_switching_count_depth` — the tight `(2w)^s` count with the size condition written as
  `(canonicalDT cs F ρ).depth = s`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **In the pure-satisfy regime, every step is recorded.**  With no falsify step, the satisfy-position
list and the full deepest-branch path have the same length. -/
theorem deepestSatPos_length_eq_deepestPath_length (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      deepestFalSel cs F σ = ∅ →
      (deepestSatPos cs F σ).length = (deepestPath cs F σ).length := by
  intro F
  induction F with
  | zero => intro σ _; rfl
  | succ F ih =>
    intro σ hfal
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [deepestSatPos, deepestPath, hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => simp [deepestSatPos, deepestPath, hany, hact]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp [deepestSatPos, deepestPath, hany, hact, hh]
        | some ℓ =>
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · rw [deepestFalSel] at hfal
            simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hfal
            rw [if_pos hd] at hfal
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ = true
            · rw [if_pos hf] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp), id_eq] at hfal
              rw [deepestSatPos, deepestPath]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh]
              rw [if_pos hd, if_pos hd, if_neg (by rw [hf]; simp)]
              simp only [List.length_cons]
              rw [ih (fixVar σ (litVar ℓ) false) hfal]
          · rw [deepestFalSel] at hfal
            simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hfal
            rw [if_neg hd] at hfal
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ = true
            · rw [if_pos hf] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp), id_eq] at hfal
              rw [deepestSatPos, deepestPath]
              simp only [hany, Bool.false_eq_true, if_false, hact, hh]
              rw [if_neg hd, if_neg hd, if_neg (by rw [hf]; simp)]
              simp only [List.length_cons]
              rw [ih (fixVar σ (litVar ℓ) true) hfal]

/-- **The satisfy-position count is the tree depth (pure-satisfy regime).** -/
theorem deepestSatPos_length_eq_depth (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    (hpure : deepestFalSel cs F σ = ∅) :
    (deepestSatPos cs F σ).length = (canonicalDT cs F σ).depth := by
  rw [deepestSatPos_length_eq_deepestPath_length cs F σ hpure, deepestPath_length_eq_depth]

/-- **The tight `(2w)^s` switching count for the pure-satisfy regime, by depth.**  The size condition
is written directly as `(canonicalDT cs F ρ).depth = s`: a pure-satisfy bad set whose canonical
decision-tree depth is exactly `s` and whose deepest end-states land in `Short` has
`|Bad| ≤ |Short|·(2w)^s`. -/
theorem pure_satisfy_switching_count_depth {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hact : ∀ ρ ∈ Bad, ∃ T, SwitchingCounting.activeTerm cs ρ = some T ∧ CleanClause T)
    (hpure : ∀ ρ ∈ Bad, deepestFalSel cs F ρ = ∅)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hdepth : ∀ ρ ∈ Bad, (canonicalDT cs F ρ).depth = s)
    (hlt : ∀ ρ ∈ Bad, ∀ p ∈ deepestSatPos cs F ρ, p < w) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  pure_satisfy_switching_count hmem hnf hact hpure hleaf
    (fun ρ hρ => by
      rw [deepestSatPos_length_eq_depth cs F ρ (hpure ρ hρ)]; exact hdepth ρ hρ) hlt

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatPos_length_eq_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pure_satisfy_switching_count_depth
