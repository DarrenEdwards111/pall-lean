import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDnfCount

/-!
# The reconstruction-correctness invariant: precise statement, and that it suffices

This file states the **one remaining open target** of the depth-3 switching arc — the
reconstruction-correctness of the forward-scan decoder for the deepest branch — as a clean `Prop`
(`ReconstructionCorrect`), with no `sorry`, and proves that it **suffices** for the tight depth count
(`deepest_switching_count_of_reconstruction`).  Everything around the invariant is proved here; only
the invariant's *truth* is left open, isolated as a named definition for a focused proof effort.

## The objects

* `deepestEnd` / `deepestSel` — the end-state and selected-variable set of the canonical deepest
  branch (mirroring `deepestPath`'s descent into the deeper child).
* `freeOn_deepestEnd` — **recovery**: `freeOn (deepestEnd cs F ρ) (deepestSel cs F ρ) = ρ` (re-freeing
  the selected variables inverts the path; each step fixes a free variable, `freeOn_fixVar_free`).
* `deepestEnd_inj` — hence the end-state together with the selected set determines `ρ`.

## The invariant (the open target)

`ReconstructionCorrect cs w s F Bad` :  there is a `(2w)^s` label `lab` and a decoder `D` such that
for every bad `ρ`, `D (deepestEnd cs F ρ) (lab ρ) = deepestSel cs F ρ` — i.e. the selected set is
recoverable from the end-state and the compact label.  This is exactly Håstad's forward-scan decoding
for general (non-falsify) branches; it is **not proved** (and not faked) — it is the named research
target.

## It suffices

`deepest_switching_count_of_reconstruction` : `ReconstructionCorrect` (plus `deepestEnd` landing in
`Short`) gives `|Bad| ≤ |Short|·(2w)^s` — the tight depth count, via `card_bad_le_label_card`
(cardinality `(2w)^s`) and `deepestEnd_inj` (injectivity).  So proving `ReconstructionCorrect` for the
depth-bad set is precisely the last step to the tight `depth ≤ s`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Freeing the empty set is the identity. -/
theorem freeOn_empty (ρ : Fin n → Option Bool) : SwitchingCounting.freeOn ρ ∅ = ρ := by
  funext i; simp [SwitchingCounting.freeOn]

/-- Freeing a set splits off one element: `freeOn ρ (insert v S) = freeOn (freeOn ρ S) {v}`. -/
theorem freeOn_insert (ρ : Fin n → Option Bool) (v : Fin n) (S : Finset (Fin n)) :
    SwitchingCounting.freeOn ρ (insert v S)
      = SwitchingCounting.freeOn (SwitchingCounting.freeOn ρ S) {v} := by
  funext i
  simp only [SwitchingCounting.freeOn, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : i = v
  · simp [h1]
  · by_cases h2 : i ∈ S <;> simp [h1, h2]

/-- The end-state of the canonical deepest branch (descend into the deeper child each step). -/
def deepestEnd (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → (Fin n → Option Bool)
  | 0, σ => σ
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then σ
    else match SwitchingCounting.activeTerm cs σ with
      | none => σ
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => σ
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then deepestEnd cs fuel (fixVar σ (litVar ℓ) false)
          else deepestEnd cs fuel (fixVar σ (litVar ℓ) true)

/-- The selected variables of the canonical deepest branch. -/
def deepestSel (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → Finset (Fin n)
  | 0, _ => ∅
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then ∅
    else match SwitchingCounting.activeTerm cs σ with
      | none => ∅
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => ∅
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then insert (litVar ℓ) (deepestSel cs fuel (fixVar σ (litVar ℓ) false))
          else insert (litVar ℓ) (deepestSel cs fuel (fixVar σ (litVar ℓ) true))

/-- **Recovery.**  Re-freeing the deepest branch's selected variables from its end-state recovers
`ρ`: `freeOn (deepestEnd cs F ρ) (deepestSel cs F ρ) = ρ`. -/
theorem freeOn_deepestEnd (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool),
      SwitchingCounting.freeOn (deepestEnd cs fuel σ) (deepestSel cs fuel σ) = σ := by
  intro fuel
  induction fuel with
  | zero => intro σ; exact freeOn_empty σ
  | succ fuel ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      rw [deepestEnd, deepestSel]; simp only [hany, if_true]; exact freeOn_empty σ
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestEnd, deepestSel]
        simp only [hany, Bool.false_eq_true, if_false, hact]; exact freeOn_empty σ
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestEnd, deepestSel]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]; exact freeOn_empty σ
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          rw [deepestEnd, deepestSel]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          split
          · rw [freeOn_insert, ih, freeOn_fixVar_free hfree]
          · rw [freeOn_insert, ih, freeOn_fixVar_free hfree]

/-- **Injectivity.**  `ρ` is determined by its deepest-branch end-state and selected set. -/
theorem deepestEnd_inj (cs : List (Clause n)) (F : ℕ) {ρ σ : Fin n → Option Bool}
    (hE : deepestEnd cs F ρ = deepestEnd cs F σ) (hS : deepestSel cs F ρ = deepestSel cs F σ) :
    ρ = σ := by
  rw [← freeOn_deepestEnd cs F ρ, ← freeOn_deepestEnd cs F σ, hE, hS]

/-- **The reconstruction-correctness invariant (the open target).**  There is a `(2w)^s` label `lab`
and a decoder `D` recovering the deepest branch's selected set from the end-state and the label.  This
is Håstad's forward-scan decoding for general branches — stated precisely, **not** proved here. -/
def ReconstructionCorrect (cs : List (Clause n)) (w s F : ℕ) (Bad : Finset (Restriction n)) : Prop :=
  ∃ (lab : Restriction n → PathLabel w s) (D : Restriction n → PathLabel w s → Finset (Fin n)),
    ∀ ρ ∈ Bad, D (deepestEnd cs F ρ) (lab ρ) = deepestSel cs F ρ

/-- **Reconstruction ⟹ the tight depth count.**  If the deepest end-state lands in `Short` and the
reconstruction invariant holds, then `|Bad| ≤ |Short|·(2w)^s`: the end-state + `(2w)^s` label
determine `ρ` (`deepestEnd_inj`), so `card_bad_le_label_card` applies.  Hence proving
`ReconstructionCorrect` is exactly the last step to the tight `depth ≤ s`. -/
theorem deepest_switching_count_of_reconstruction {w s F : ℕ} {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hrec : ReconstructionCorrect cs w s F Bad) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  obtain ⟨lab, D, hdec⟩ := hrec
  refine card_bad_le_label_card (deepestEnd cs F) lab ?_ hmem ?_
  · exact (card_pathLabels w s).le
  · intro ρ hρ σ hσ hE hlab
    have h1 : D (deepestEnd cs F ρ) (lab ρ) = D (deepestEnd cs F σ) (lab σ) := by rw [hE, hlab]
    rw [hdec ρ hρ, hdec σ hσ] at h1
    exact deepestEnd_inj cs F hE h1

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.freeOn_deepestEnd
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_switching_count_of_reconstruction
