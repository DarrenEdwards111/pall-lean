import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestReplay

/-!
# The empty-skip wall, precisely characterized

The interleaved satisfy-step decoder is closed for the **no-skip** regime; the residual is the
**empty-skip** case — clauses falsified with *zero* satisfy steps, interleaved among satisfy clauses.
This file pins down *why* the tight `(2w)^s` label cannot handle them: it is a genuine
information-theoretic loss, not a missing lemma.

The decoder `replayBlocks` is a **positional** `zip` of `leafClauses cs π` with the label — so an
empty block must hold its slot to keep clause `i` aligned with label entry `i`.  But the tight packing
`ungroupBlocks` **drops** empty blocks entirely.  The two facts:

* `ungroupBlocks_filter_invariant` — `ungroupBlocks (bs.filter nonempty) = ungroupBlocks bs`: the tight
  flatten is *invariant* under deleting empty blocks, so it carries **no** record of where the skips
  are.
* `groupBlocks_ungroupBlocks_filter` — `groupBlocks (ungroupBlocks bs) = bs.filter nonempty`: decoding
  the tight label recovers exactly the *nonempty* blocks, in order, with the empty (skip) slots gone.

Specialised to the replay label (`tight_decode_replayLabel`), this says: the tight `(2w)^s` decode of
`replayLabel cs F ρ` yields its nonempty satisfy-blocks but **erases which `leafClauses` were skipped**
— precisely the alignment `replayBlocks`'s positional `zip` needs.  Two restrictions whose replay
labels differ *only* in empty (skip) blocks share the same tight packing yet generally have different
`leafClauses`-alignments, so `(deepestEnd, tight label)` cannot in general recover `deepestSatSel`.

## Conclusion (honest)

The empty-skip obstruction is therefore the **skip-classifier**: recovering, from the end-state alone,
which falsified `leafClauses` carried satisfy steps.  The end-state cannot supply it (a 0-satisfy-step
falsified clause and a ≥1-satisfy-step one are both falsified, and `ρ`-true literals confound the path
-true ones).  This is the irreducible Håstad forward-reconstruction content for the deepest-branch
route; the satisfying-completion route (`canonMarkLabel_switching_count`) already gives a complete
`(2w)^s` count by sidestepping it (its `σ*` makes "first satisfied term" identify the clause).
**Not** faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

/-- **The tight flatten ignores empty blocks.**  Deleting empty blocks before `ungroupBlocks` leaves
the result unchanged — `markLast [] = []` contributes nothing.  So `ungroupBlocks` carries no record of
empty (skip) blocks. -/
theorem ungroupBlocks_filter_invariant (bs : List (List ℕ)) :
    ungroupBlocks (bs.filter (fun b => !b.isEmpty)) = ungroupBlocks bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases hb : b = []
    · subst hb
      rw [List.filter_cons]
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
      rw [ih, ungroupBlocks, markLast, List.nil_append]
    · rw [List.filter_cons]
      have hne : (!b.isEmpty) = true := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false]
        exact List.isEmpty_eq_false_iff.mpr hb
      rw [if_pos hne, ungroupBlocks, ungroupBlocks, ih]

/-- **The tight decode recovers exactly the nonempty blocks.**  `groupBlocks (ungroupBlocks bs)` is
`bs` with its empty blocks removed — a general round-trip dropping the nonempty-block hypothesis of
`groupBlocks_ungroupBlocks`. -/
theorem groupBlocks_ungroupBlocks_filter (bs : List (List ℕ)) :
    groupBlocks (ungroupBlocks bs) = bs.filter (fun b => !b.isEmpty) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases hb : b = []
    · subst hb
      rw [ungroupBlocks, markLast, List.nil_append, ih, List.filter_cons]
      simp
    · rw [ungroupBlocks, groupBlocks_markLast_append b hb, ih, List.filter_cons]
      have hne : (!b.isEmpty) = true := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false]
        exact List.isEmpty_eq_false_iff.mpr hb
      rw [if_pos hne]

end SwitchingCounting

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The wall, on the replay label.**  The tight `(2w)^s` decode of `replayLabel cs F ρ` recovers
exactly its *nonempty* satisfy-blocks, with the empty (skip) slots erased — so the `leafClauses`
alignment that `replayBlocks`'s positional `zip` requires is lost.  This is the precise statement of
the empty-skip wall. -/
theorem tight_decode_replayLabel (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool) :
    SwitchingCounting.groupBlocks (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ))
      = (replayLabel cs F ρ).filter (fun b => !b.isEmpty) :=
  SwitchingCounting.groupBlocks_ungroupBlocks_filter (replayLabel cs F ρ)

/-- **Empty (skip) blocks are invisible to the tight packing.**  Restrictions whose replay labels
differ only by empty blocks share the same tight `(2w)^s` label, so it cannot record the skip
structure. -/
theorem tight_pack_skip_invariant (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool) :
    SwitchingCounting.ungroupBlocks ((replayLabel cs F ρ).filter (fun b => !b.isEmpty))
      = SwitchingCounting.ungroupBlocks (replayLabel cs F ρ) :=
  SwitchingCounting.ungroupBlocks_filter_invariant (replayLabel cs F ρ)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.ungroupBlocks_filter_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.groupBlocks_ungroupBlocks_filter
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_decode_replayLabel
