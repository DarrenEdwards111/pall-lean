import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessReconstruct
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree

/-!
# Tight switching, step 29: length and bounds of the deepest witness sequence (branch `razborov-recoverRho-wip`)

The structural facts needed to package `deepestWitSeq` (step 28) into the `Fintype` `WitLabel w s m`:

* its length equals the canonical tree depth (it shares `deepestFullSeq`'s control flow step for step), so on
  the bad set `{depth = s}` it has length exactly `s`;
* each entry `(position, clause-index)` is in range: `position < w` (the active term has width `≤ w`) and
  `clause-index < cs.length`.

These are exactly the bounds that let the witness sequence be reindexed as a `Fin s → (Fin w × Bool × Fin m)`
label for the `(2wm)^s` count.

* `deepestWitSeq_length`, `deepestWitSeq_length_eq_depth` — length `= deepestFullSeq` length `= depth`.
* `deepestWitSeq_bounds` — entry positions `< w`, clause-indices `< cs.length`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `deepestWitSeq` has the same length as `deepestFullSeq` — identical control flow, step for step. -/
theorem deepestWitSeq_length (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Restriction n),
      (deepestWitSeq cs F σ).length = (deepestFullSeq cs F σ).length := by
  intro F
  induction F with
  | zero => intro σ; rfl
  | succ F ih =>
    intro σ
    by_cases hsat : anyTermSat cs σ = true
    · simp only [deepestWitSeq, deepestFullSeq, if_pos hsat, List.length_nil]
    · cases hT : activeTerm cs σ with
      | none => simp only [deepestWitSeq, deepestFullSeq, if_neg hsat, hT, List.length_nil]
      | some T =>
        cases hh : (freeLits σ T).head? with
        | none => simp only [deepestWitSeq, deepestFullSeq, if_neg hsat, hT, hh, List.length_nil]
        | some ℓ =>
          by_cases hcmp : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · simp only [deepestWitSeq, deepestFullSeq, if_neg hsat, hT, hh, if_pos hcmp,
              List.length_cons, ih (fixVar σ (litVar ℓ) false)]
          · simp only [deepestWitSeq, deepestFullSeq, if_neg hsat, hT, hh, if_neg hcmp,
              List.length_cons, ih (fixVar σ (litVar ℓ) true)]

/-- The witness sequence's length is the canonical tree depth. -/
theorem deepestWitSeq_length_eq_depth (cs : List (Clause n)) (F : ℕ) (σ : Restriction n) :
    (deepestWitSeq cs F σ).length = (canonicalDT cs F σ).depth :=
  (deepestWitSeq_length cs F σ).trans (deepestFullSeq_length_eq_depth cs F σ)

/-- Every witness entry is in range: position `< w` (active term width `≤ w`), clause-index `< cs.length`. -/
theorem deepestWitSeq_bounds (cs : List (Clause n)) {w : ℕ}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) :
    ∀ (F : ℕ) (σ : Restriction n), ∀ pc ∈ deepestWitSeq cs F σ,
      pc.1 < w ∧ pc.2 < cs.length := by
  intro F
  induction F with
  | zero => intro σ pc hpc; simp only [deepestWitSeq, List.not_mem_nil] at hpc
  | succ F ih =>
    intro σ pc hpc
    by_cases hsat : anyTermSat cs σ = true
    · simp only [deepestWitSeq, if_pos hsat, List.not_mem_nil] at hpc
    · cases hT : activeTerm cs σ with
      | none => simp only [deepestWitSeq, if_neg hsat, hT, List.not_mem_nil] at hpc
      | some T =>
        cases hh : (freeLits σ T).head? with
        | none => simp only [deepestWitSeq, if_neg hsat, hT, hh, List.not_mem_nil] at hpc
        | some ℓ =>
          by_cases hcmp : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · simp only [deepestWitSeq, if_neg hsat, hT, hh, if_pos hcmp, List.mem_cons] at hpc
            rcases hpc with rfl | hpc
            · exact ⟨lt_of_lt_of_le (freeLitPos_lt hh) (hw T (activeTerm_mem hT)),
                activeTermIdx_lt hT⟩
            · exact ih (fixVar σ (litVar ℓ) false) pc hpc
          · simp only [deepestWitSeq, if_neg hsat, hT, hh, if_neg hcmp, List.mem_cons] at hpc
            rcases hpc with rfl | hpc
            · exact ⟨lt_of_lt_of_le (freeLitPos_lt hh) (hw T (activeTerm_mem hT)),
                activeTermIdx_lt hT⟩
            · exact ih (fixVar σ (litVar ℓ) true) pc hpc

/-- The genuine deepest-branch witness may repeat a term index at many query steps, but the set of
indices it uses is bounded by the number of DNF terms.  This is the first compression invariant:
term identity is block data, not an independent `m`-way choice at every depth position. -/
theorem deepestWitSeq_termIndices_card_le (cs : List (Clause n)) {w : ℕ}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (F : ℕ) (σ : Restriction n) :
    ((deepestWitSeq cs F σ).map Prod.snd).toFinset.card ≤ cs.length := by
  let inds := ((deepestWitSeq cs F σ).map Prod.snd).toFinset
  have hsub : inds ⊆ Finset.range cs.length := by
    intro i hi
    simp only [inds, List.mem_toFinset, List.mem_map] at hi
    obtain ⟨pc, hpc, rfl⟩ := hi
    exact Finset.mem_range.mpr (deepestWitSeq_bounds cs hw F σ pc hpc).2
  exact le_trans (Finset.card_le_card hsub) (by simp)

/-- The same compression invariant with an external term bound `m`, matching the quantitative
switching API. -/
theorem deepestWitSeq_termIndices_card_le_bound (cs : List (Clause n)) {w m : ℕ}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (F : ℕ) (σ : Restriction n) :
    ((deepestWitSeq cs F σ).map Prod.snd).toFinset.card ≤ m :=
  (deepestWitSeq_termIndices_card_le cs hw F σ).trans hm

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_length_eq_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_bounds
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_termIndices_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_termIndices_card_le_bound
