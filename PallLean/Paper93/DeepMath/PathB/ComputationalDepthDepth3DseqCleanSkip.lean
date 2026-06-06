import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DseqNoSkip
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EmptySkipWall

/-!
# `Dseq` correctness in the clean-skip regime (branch `razborov-recoverRho-wip`)

The **clean-skip** regime allows *interior empty blocks*, but each is exactly a leaf clause that is
**falsified at the leaf** (`hskip`: empty block ⟺ falsified-at-leaf).  The tight label
`ungroupBlocks (replayLabel …)` drops the empty blocks (`ungroupBlocks_filter_invariant`), so the plain
`Dseq` (which walks *every* leaf clause) would mis-consume tokens there.

The refinement `DseqSkip` consults the end-state: it walks only the leaf clauses **not falsified at the
leaf** (`!termFalsified σ_end`).  Under `hskip` these are exactly the nonempty-block clauses, so the
no-skip round-trip (`replayBlocksFlat_ungroup_pairs`) applies and `DseqSkip` reproduces `deepestSatSeq`.

* `DseqSkip` — the empty-skip-aware decoder (legal data only: `σ_end`, the label, `cs`).
* `Dseq_correct_clean_skip` — the result.

This is the `σ_end`-driven empty-block skip.  It does **not** resolve the confound (a clause falsified
at the leaf that *also* got satisfy steps, i.e. a nonempty block on a falsified clause): there `DseqSkip`
would wrongly skip it.  That remains the genuine Håstad crux (`Dseq_correct_general`).

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-! ## Two list helpers -/

/-- Filtering commutes with mapping (pulling the predicate through `f`). -/
theorem filter_map_comm {α β : Type*} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).filter p = (l.filter (fun a => p (f a))).map f := by
  induction l with
  | nil => rfl
  | cons a t ih => by_cases h : p (f a) <;> simp [List.map_cons, h, ih]

/-- A `flatMap` is unchanged by filtering out elements whose image is empty. -/
theorem flatMap_filter_eq {α β : Type*} (g : α → List β) (p : α → Bool) (l : List α)
    (h : ∀ a ∈ l, p a = false → g a = []) :
    (l.filter p).flatMap g = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons]
    by_cases ha : p a
    · rw [if_pos ha, List.flatMap_cons, List.flatMap_cons,
        ih (fun b hb => h b (List.mem_cons_of_mem a hb))]
    · rw [if_neg ha, List.flatMap_cons, ih (fun b hb => h b (List.mem_cons_of_mem a hb)),
        h a List.mem_cons_self (by simpa using ha), List.nil_append]

/-! ## The empty-skip-aware decoder -/

/-- **The clean-skip decoder.**  Walk only the leaf clauses *not* falsified at the end-state — under
clean-skip these are exactly the nonempty-block clauses — then run the no-skip block decoder. -/
def DseqSkip {w s : ℕ} (cs : List (Clause n)) (σ_end : Fin n → Option Bool)
    (lbl : SwitchingCounting.PathLabel w s) : List (Clause n × ℕ) :=
  replayBlocksFlat ((leafClauses cs σ_end).filter (fun C => !SwitchingCounting.termFalsified σ_end C))
    (List.ofFn lbl)

/-! ## Clean-skip correctness -/

/-- **`DseqSkip` reproduces `deepestSatSeq` in the clean-skip regime.**  Empty blocks coincide with
falsified-at-leaf clauses (`hskip`); positions `< w` (`hlt`); label length `s` (`hlen`); and
`deepestSatSeq` is the concatenation of all leaf-clause blocks (`hseq` — empty blocks contribute
nothing).  Then the refined decoder recovers `deepestSatSeq`. -/
theorem Dseq_correct_clean_skip {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {ρ : Fin n → Option Bool}
    (hskip : ∀ C ∈ leafClauses cs (deepestEnd cs F ρ),
      (deepestSatPositions cs F ρ C = []
        ↔ SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = true))
    (hlt : ∀ C ∈ leafClauses cs (deepestEnd cs F ρ), ∀ p ∈ deepestSatPositions cs F ρ C, p < w)
    (hlen : (ungroupBlocks (replayLabel cs F ρ)).length = s)
    (hseq : deepestSatSeq cs F ρ
      = (leafClauses cs (deepestEnd cs F ρ)).flatMap
          (fun C => (deepestSatPositions cs F ρ C).map (fun p => (C, p)))) :
    DseqSkip cs (deepestEnd cs F ρ)
        (SwitchingCounting.flatToLabel
            (toFinW w (ungroupBlocks (replayLabel cs F ρ))) : SwitchingCounting.PathLabel w s)
      = deepestSatSeq cs F ρ := by
  set fc := (leafClauses cs (deepestEnd cs F ρ)).filter
    (fun C => !SwitchingCounting.termFalsified (deepestEnd cs F ρ) C) with hfc
  set pairs := fc.map (fun C => (C, deepestSatPositions cs F ρ C)) with hpairs
  -- the filtered clauses all carry nonempty blocks
  have hfcmem : ∀ C ∈ fc, SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = false ∧
      C ∈ leafClauses cs (deepestEnd cs F ρ) := by
    intro C hC
    rw [hfc, List.mem_filter] at hC
    exact ⟨by simpa using hC.2, hC.1⟩
  have hpf : pairs.map Prod.fst = fc := by
    rw [hpairs, List.map_map,
      show (Prod.fst ∘ fun C : Clause n => (C, deepestSatPositions cs F ρ C)) = id from rfl,
      List.map_id]
  have hps : pairs.map Prod.snd = fc.map (deepestSatPositions cs F ρ) := by
    rw [hpairs, List.map_map,
      show (Prod.snd ∘ fun C : Clause n => (C, deepestSatPositions cs F ρ C))
        = deepestSatPositions cs F ρ from rfl]
  have hne : ∀ cb ∈ pairs, cb.2 ≠ [] := by
    intro cb hcb
    rw [hpairs, List.mem_map] at hcb
    obtain ⟨C, hC, rfl⟩ := hcb
    obtain ⟨hfal, hmem⟩ := hfcmem C hC
    exact fun hh => by rw [(hskip C hmem).mp hh] at hfal; exact absurd hfal (by simp)
  have hlt' : ∀ cb ∈ pairs, ∀ p ∈ cb.2, p < w := by
    intro cb hcb
    rw [hpairs, List.mem_map] at hcb
    obtain ⟨C, hC, rfl⟩ := hcb
    exact hlt C (hfcmem C hC).2
  have key := replayBlocksFlat_ungroup_pairs pairs hne hlt'
  rw [hpf, hps] at key
  -- the encoder's ungrouped label drops empty blocks ↦ nonempty (= non-falsified) blocks
  have hug : ungroupBlocks (replayLabel cs F ρ)
      = ungroupBlocks (fc.map (deepestSatPositions cs F ρ)) := by
    rw [← ungroupBlocks_filter_invariant (replayLabel cs F ρ)]
    congr 1
    show (replayLabel cs F ρ).filter (fun b => !b.isEmpty) = fc.map (deepestSatPositions cs F ρ)
    rw [show replayLabel cs F ρ
          = (leafClauses cs (deepestEnd cs F ρ)).map (deepestSatPositions cs F ρ) from rfl,
        filter_map_comm]
    congr 1
    rw [hfc]
    apply List.filter_congr
    intro C hC
    by_cases ht : SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = true
    · simp [(hskip C hC).mpr ht, ht]
    · rw [Bool.not_eq_true] at ht
      have hne2 : deepestSatPositions cs F ρ C ≠ [] := by
        intro hh; rw [(hskip C hC).mp hh] at ht; exact absurd ht (by simp)
      simp [ht, List.isEmpty_eq_false_iff.mpr hne2]
  -- the skipped (falsified) clauses contribute nothing to the flatMap
  have hflat : fc.flatMap (fun C => (deepestSatPositions cs F ρ C).map (fun p => (C, p)))
      = (leafClauses cs (deepestEnd cs F ρ)).flatMap
          (fun C => (deepestSatPositions cs F ρ C).map (fun p => (C, p))) := by
    rw [hfc]
    apply flatMap_filter_eq
    intro C hC hfal
    have ht : SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = true := by simpa using hfal
    rw [(hskip C hC).mpr ht, List.map_nil]
  rw [DseqSkip, ofFn_flatToLabel (by rw [toFinW, List.length_map]; exact hlen), hug, key, hpairs,
      List.flatMap_map, hflat]
  exact hseq.symm

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Dseq_correct_clean_skip
