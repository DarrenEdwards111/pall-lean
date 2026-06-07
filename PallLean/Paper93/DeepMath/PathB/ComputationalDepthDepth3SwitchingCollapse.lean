import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseBothRoutes

/-!
# From the full-path switching count to the collapse seed — branch only

`fullpath_switching_count` bounds the deep-tree (bad) restrictions: `|Bad| ≤ |Short|·(2w)^s`.  Feeding
it into the generic counting-collapse `SwitchingCounting.exists_good_of_count` gives the **collapse
seed**: in the Håstad regime (`|Short|·(2w)^s < 2^n`, the count below the total), some restriction is
**not** bad — i.e. its canonical tree is shallow.  This is the existence step the depth-3 collapse
consumes.

* `exists_good_fullpath` — a good (non-deep) restriction exists once the full-path count is sub-total.

Clean, no `sorry`.  `Depth3CollapseModel.collapse` (the structural collapse interface) and P≠NP remain
untouched — this is the count→existence bridge, one ingredient.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The collapse seed from the full-path switching count.**  If the bad (deep-path) restrictions have
their leaves in `Short`, with full paths of length `s` and positions `< w`, and the count
`|Short|·(2w)^s` is below the total number of restrictions, then some restriction is **not** bad. -/
theorem exists_good_fullpath (cs : List (Clause n)) (w s F : ℕ) [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hlen : ∀ ρ ∈ Bad, (deepestFullSeq cs F ρ).length = s)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ deepestFullSeq cs F ρ, p.1 < w)
    (hlt : Short.card * (2 * w) ^ s
      < (Finset.univ : Finset (SwitchingCounting.Restriction n)).card) :
    ∃ ρ : SwitchingCounting.Restriction n, ρ ∉ Bad :=
  SwitchingCounting.exists_good_of_count
    (fullpath_switching_count cs w s F hmem hnf hleaf hlen hpos) hlt

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_good_fullpath
