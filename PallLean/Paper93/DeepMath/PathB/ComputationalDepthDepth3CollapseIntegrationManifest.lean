import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WidthBadCollapseReplay
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyDepth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefutation

/-!
# Switching → collapse integration: manifest

A machine-checked index of how the depth-3 switching counts feed the collapse pipeline.  Every
`#check` is a proved theorem (clean axioms, no `sorry`); the two genuinely-open proof-complexity gates
are stated as such and **not** claimed.

## The switching counts (two routes + the closed special case)

* `SwitchingCounting.canonMarkLabel_switching_count` — the **encLits / satisfying-completion** route:
  `|Bad| ≤ |Short| · (2w)^s` via the canonical first-claim label.
* `Depth3.deepest_noskip_tight_count_depth` — the **deepest-branch replay** route, rebased on the
  decision-tree depth: `|Bad| ≤ |Short| · (2w)^D` under the no-skip structural conditions.
* `Depth3.pure_satisfy_switching_count_depth` — the **pure-satisfy** special case, fully closed
  end-to-end (`canonicalDT.depth = s`).

## The count → collapse arc (completion-agnostic)

* `SwitchingCounting.exists_good_restriction` — pigeonhole: `|widthBad| ≤ |Short|·(2w)^s <
  #restrictions ⟹ ∃ ρ ∉ widthBad`.
* `SwitchingCounting.residual_width_le_of_not_widthBad` — outside `widthBad`, residual width `≤`
  budget.
* `SwitchingCounting.good_restriction_yields_short_dt` / `widthBad_yields_short_dt` — a good restriction
  yields a depth-`≤budget` decision tree computing `D` on its subcube.
* `DTRef.leaves_le_two_pow_depth` — a depth-`d` refutation tree has `≤ 2^d` leaves (the collapsed
  refutation-length bound).

## Both routes reach collapse

* `SwitchingCounting.widthBad_collapse_dt` — collapse via the encLits route count.
* `SwitchingCounting.widthBad_collapse_dt_replay` — collapse via the deepest-branch replay count.

Both consume the same pigeonhole + DT extraction, differing only in which `(2w)^s` count and completion
they use.

## The two open gates (NOT claimed)

* **G1-core (`hincl : widthBad ⊆ Bad`).**  That a large-residual-width restriction lies in the
  recoverable (switching) bad set — the structural switching-lemma content relating residual width to
  the canonical path/depth.  Taken as a hypothesis in both `widthBad_collapse_dt(_replay)`; **open**.
* **G2 (DT → LDeriv).**  The construction turning a shallow decision tree for the restricted refuting
  circuit into a resolution refutation of the Tseitin axioms (`leaves_le_two_pow_depth` bounds its
  length; the construction itself is **open**).

Everything around these two gates is proved.  Ceiling: AC⁰/depth-3; `Depth3CollapseModel.collapse` and
P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- The switching counts.
#check @SwitchingCounting.canonMarkLabel_switching_count
#check @Depth3.deepest_noskip_tight_count_depth
#check @Depth3.pure_satisfy_switching_count_depth

-- The count → collapse arc (completion-agnostic).
#check @SwitchingCounting.exists_good_restriction
#check @SwitchingCounting.residual_width_le_of_not_widthBad
#check @SwitchingCounting.good_restriction_yields_short_dt
#check @SwitchingCounting.widthBad_yields_short_dt
#check @DTRef.leaves_le_two_pow_depth

-- Both routes reach collapse.
#check @SwitchingCounting.widthBad_collapse_dt
#check @SwitchingCounting.widthBad_collapse_dt_replay

end PallLean.Paper93.DeepMath.PathB
