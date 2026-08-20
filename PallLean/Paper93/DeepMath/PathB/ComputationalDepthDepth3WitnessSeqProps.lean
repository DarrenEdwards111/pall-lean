import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessReconstruct
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqContiguity

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

/-- The stored index of an active term is its actual position in a duplicate-free DNF list. -/
theorem activeTermIdx_eq_idxOf {cs : List (Clause n)} (hnd : cs.Nodup)
    {σ : Restriction n} {T : Clause n} (hact : activeTerm cs σ = some T) :
    activeTermIdx cs σ = cs.idxOf T := by
  have hidx := hnd.idxOf_getElem (activeTermIdx cs σ) (activeTermIdx_lt hact)
  rw [getElem_activeTermIdx hact] at hidx
  exact hidx.symm

/-- Every term index recorded later on the deepest witness belongs to the current active suffix.
This is the multi-step form of active-clause non-backtracking. -/
theorem deepestWitSeq_index_mem_activeSuffix (cs : List (Clause n)) (hnd : cs.Nodup) :
    ∀ (F : ℕ) (σ : Restriction n) (pc : ℕ × ℕ), pc ∈ deepestWitSeq cs F σ →
      ∃ T ∈ activeSuffix cs σ, pc.2 = cs.idxOf T := by
  intro F
  induction F with
  | zero =>
      intro σ pc hpc
      simp only [deepestWitSeq, List.not_mem_nil] at hpc
  | succ F ih =>
      intro σ pc hpc
      by_cases hsat : anyTermSat cs σ = true
      · simp only [deepestWitSeq, if_pos hsat, List.not_mem_nil] at hpc
      · cases hT : activeTerm cs σ with
        | none => simp only [deepestWitSeq, if_neg hsat, hT, List.not_mem_nil] at hpc
        | some T =>
          cases hh : (freeLits σ T).head? with
          | none => simp only [deepestWitSeq, if_neg hsat, hT, hh, List.not_mem_nil] at hpc
          | some ell =>
            have hellmem : ell ∈ freeLits σ T := List.mem_of_mem_head? hh
            have hv : σ (litVar ell) = none := by
              have hfree : litFree σ ell = true := (List.mem_filter.mp hellmem).2
              rw [litFree_var] at hfree
              cases hs : σ (litVar ell) with
              | none => rfl
              | some b => rw [hs] at hfree; simp at hfree
            have hTmem : T ∈ activeSuffix cs σ := by
              have hhead := head?_activeSuffix (cs := cs) (σ := σ) (by
                exact Bool.eq_false_of_not_eq_true hsat)
              rw [hT] at hhead
              exact List.mem_of_mem_head? hhead
            have finish (b : Bool)
                (hp : pc = (freeLitPos σ T, activeTermIdx cs σ) ∨
                  pc ∈ deepestWitSeq cs F (fixVar σ (litVar ell) b)) :
                ∃ U ∈ activeSuffix cs σ, pc.2 = cs.idxOf U := by
              rcases hp with rfl | hp
              · exact ⟨T, hTmem, activeTermIdx_eq_idxOf hnd hT⟩
              · obtain ⟨U, hU, hidx⟩ := ih (fixVar σ (litVar ell) b) pc hp
                exact ⟨U, (activeSuffix_fixVar_suffix hv).subset hU, hidx⟩
            by_cases hcmp : (canonicalDT cs F (fixVar σ (litVar ell) true)).depth ≤
                (canonicalDT cs F (fixVar σ (litVar ell) false)).depth
            · simp only [deepestWitSeq, if_neg hsat, hT, hh, if_pos hcmp,
                List.mem_cons] at hpc
              exact finish false hpc
            · simp only [deepestWitSeq, if_neg hsat, hT, hh, if_neg hcmp,
                List.mem_cons] at hpc
              exact finish true hpc

/-- **Deepest-witness non-backtracking.**  For a duplicate-free DNF, the term-index stream stored
by the genuine max-depth witness is pairwise nondecreasing.  Hence each term occupies one
contiguous run and can be named once per run instead of once per queried variable. -/
theorem deepestWitSeq_termIndices_pairwise (cs : List (Clause n)) (hnd : cs.Nodup) :
    ∀ (F : ℕ) (σ : Restriction n),
      List.Pairwise (· ≤ ·) ((deepestWitSeq cs F σ).map Prod.snd) := by
  intro F
  induction F with
  | zero => intro σ; simp [deepestWitSeq]
  | succ F ih =>
      intro σ
      by_cases hsat : anyTermSat cs σ = true
      · simp [deepestWitSeq, hsat]
      · cases hT : activeTerm cs σ with
        | none => simp [deepestWitSeq, hsat, hT]
        | some T =>
          cases hh : (freeLits σ T).head? with
          | none => simp [deepestWitSeq, hsat, hT, hh]
          | some ell =>
            have hns : anyTermSat cs σ = false := Bool.eq_false_of_not_eq_true hsat
            have hhead : activeTermIdx cs σ = cs.idxOf T :=
              activeTermIdx_eq_idxOf hnd hT
            have finish (b : Bool) :
                List.Pairwise (· ≤ ·)
                  (((freeLitPos σ T, activeTermIdx cs σ) ::
                    deepestWitSeq cs F (fixVar σ (litVar ell) b)).map Prod.snd) := by
              simp only [List.map_cons]
              refine List.Pairwise.cons ?_ (ih (fixVar σ (litVar ell) b))
              intro i hi
              rw [List.mem_map] at hi
              obtain ⟨pc, hpc, rfl⟩ := hi
              obtain ⟨U, hU, hidx⟩ :=
                deepestWitSeq_index_mem_activeSuffix cs hnd F
                  (fixVar σ (litVar ell) b) pc hpc
              have hellmem : ell ∈ freeLits σ T := List.mem_of_mem_head? hh
              have hv : σ (litVar ell) = none := by
                have hfree : litFree σ ell = true := (List.mem_filter.mp hellmem).2
                rw [litFree_var] at hfree
                cases hs : σ (litVar ell) with
                | none => rfl
                | some q => rw [hs] at hfree; simp at hfree
              have hU' : U ∈ activeSuffix cs σ :=
                (activeSuffix_fixVar_suffix hv).subset hU
              rw [hhead, hidx]
              exact idxOf_activeTerm_le_of_mem_activeSuffix hnd hns hT hU'
            by_cases hcmp : (canonicalDT cs F (fixVar σ (litVar ell) true)).depth ≤
                (canonicalDT cs F (fixVar σ (litVar ell) false)).depth
            · rw [deepestWitSeq]
              simp only [hsat, Bool.false_eq_true, if_false, hT, hh, if_pos hcmp]
              exact finish false
            · rw [deepestWitSeq]
              simp only [hsat, Bool.false_eq_true, if_false, hT, hh, if_neg hcmp]
              exact finish true

/-- A nondecreasing natural-number stream is uniquely determined by its multiplicity table. -/
theorem pairwise_le_eq_of_count_eq {a b : List ℕ}
    (ha : List.Pairwise (· ≤ ·) a) (hb : List.Pairwise (· ≤ ·) b)
    (hc : ∀ i, a.count i = b.count i) : a = b := by
  have hp : a.Perm b := List.perm_iff_count.mpr hc
  exact hp.eq_of_pairwise' ha hb

/-- Consequently, two genuine deepest witnesses for the same duplicate-free DNF have identical
term-index streams as soon as their per-term run counts agree.  This is the decoder uniqueness
fact used by the compact multiplicity label. -/
theorem deepestWitSeq_termIndices_eq_of_count_eq (cs : List (Clause n)) (hnd : cs.Nodup)
    (F : ℕ) (ρ σ : Restriction n)
    (hc : ∀ i,
      ((deepestWitSeq cs F ρ).map Prod.snd).count i =
        ((deepestWitSeq cs F σ).map Prod.snd).count i) :
    (deepestWitSeq cs F ρ).map Prod.snd =
      (deepestWitSeq cs F σ).map Prod.snd :=
  pairwise_le_eq_of_count_eq
    (deepestWitSeq_termIndices_pairwise cs hnd F ρ)
    (deepestWitSeq_termIndices_pairwise cs hnd F σ) hc

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_length_eq_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_bounds
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_termIndices_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_termIndices_card_le_bound
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTermIdx_eq_idxOf
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_index_mem_activeSuffix
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestWitSeq_termIndices_pairwise
