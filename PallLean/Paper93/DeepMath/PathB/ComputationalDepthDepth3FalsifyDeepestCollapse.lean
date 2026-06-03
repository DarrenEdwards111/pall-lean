import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ReconstructionFalsify
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseBothRoutes

/-!
# Collapse in the falsify-deepest regime

Assembling the falsify-deepest tight count (`deepest_count_of_falsify_deepest`, the regime where
`ReconstructionCorrect` is closed label-free) with the pigeonhole (`exists_good_of_count`): under the
parameter inequality, a good restriction (outside the bad set) exists.

* `exists_good_falsify_deepest` — given the falsify-deepest hypotheses (`ρ` falsifies nothing, the
  deepest branch coincides with the falsify path, end-state lands in `Short`) and the parameter
  inequality `|Short|·(2w)^s < 3^n`, there is a restriction `ρ ∉ Bad`.

So in the falsify-deepest regime the whole collapse step goes through *unconditionally* (the tight
count is proved, not assumed): the squeeze's collapse side closes, with the width side
(`dtRef_refuting_depth_ge` / `depth3_master_squeeze`) already proved.  The only regime not covered is
where the deepest branch contains a satisfy-step (the satisfy-variable label encoding, the open core).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Good restriction exists in the falsify-deepest regime.**  The falsify-deepest tight count plus
the parameter inequality `|Short|·(2w)^s < 3^n` give a restriction outside the bad set — the collapse
step, unconditional in this regime (the count is proved via `decodedSel`, no label). -/
theorem exists_good_falsify_deepest {w s F : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (heq_end : ∀ ρ ∈ Bad, deepestEnd cs F ρ = SwitchingCounting.replayPath cs ρ F)
    (heq_sel : ∀ ρ ∈ Bad, deepestSel cs F ρ = SwitchingCounting.replaySel cs ρ F)
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hlt : Short.card * (2 * w) ^ s < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ρ ∉ Bad :=
  SwitchingCounting.exists_good_of_count
    (deepest_count_of_falsify_deepest hnf heq_end heq_sel hmem) hlt

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_good_falsify_deepest
