import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ReconstructionReadOnce
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder

/-!
# `ReconstructionCorrect` closed when the deepest branch is the falsify path

When the deepest branch takes **no satisfy-step** — i.e. its end-state and selected set coincide with
the falsify (replay) path's — the reconstruction is label-free, via the proved end-state decoder
`decodedSel_eq_replaySel` (every queried variable carries a false literal, read off the end-state).
So `ReconstructionCorrect` holds outright in that regime:

* `reconstruction_of_deepest_eq_replay` — if `ρ` falsifies no term, and the deepest end-state /
  selected set equal the replay path / selected set (`deepestEnd = replayPath`,
  `deepestSel = replaySel`), then `ReconstructionCorrect` holds (constant label, `D = decodedSel`).

This is the genuinely-closed half of `ReconstructionCorrect`: whenever the deepest branch is the
all-falsify branch (no `true`-step satisfies along it), there is no satisfied clause and the `(2w)^s`
label is unnecessary.  The remaining open case is exactly when the deepest branch *does* contain a
satisfy-step — there the satisfied clause's true-set variables carry no false literal and the label is
needed; not discharged here, not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **`ReconstructionCorrect` when the deepest branch is the falsify path.**  If `ρ` falsifies no
term and the deepest branch coincides with the replay (falsify) path on its end-state and selected
set, then the selected set is recoverable from the end-state alone (`decodedSel`), so the
reconstruction invariant holds with no label. -/
theorem reconstruction_of_deepest_eq_replay {w s F : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad : Finset (Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (heq_end : ∀ ρ ∈ Bad, deepestEnd cs F ρ = SwitchingCounting.replayPath cs ρ F)
    (heq_sel : ∀ ρ ∈ Bad, deepestSel cs F ρ = SwitchingCounting.replaySel cs ρ F) :
    ReconstructionCorrect cs w s F Bad := by
  refine reconstruction_of_labelfree (SwitchingCounting.decodedSel cs) ?_
  intro ρ hρ
  rw [heq_end ρ hρ, SwitchingCounting.decodedSel_eq_replaySel (hnf ρ hρ) F]
  exact (heq_sel ρ hρ).symm

/-- The tight depth count, closed in the falsify-deepest regime: combining the above with
`deepest_switching_count_of_reconstruction`. -/
theorem deepest_count_of_falsify_deepest {w s F : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (heq_end : ∀ ρ ∈ Bad, deepestEnd cs F ρ = SwitchingCounting.replayPath cs ρ F)
    (heq_sel : ∀ ρ ∈ Bad, deepestSel cs F ρ = SwitchingCounting.replaySel cs ρ F)
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  deepest_switching_count_of_reconstruction hmem
    (reconstruction_of_deepest_eq_replay hnf heq_end heq_sel)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_of_deepest_eq_replay
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_count_of_falsify_deepest
