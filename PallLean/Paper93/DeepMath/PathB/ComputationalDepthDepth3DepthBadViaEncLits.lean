import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge

/-!
# Bounding the depth-bad set via the encLits route

The deepest-branch route's tight count is blocked at the empty-skip wall (an information-theoretic
loss in the tight packing).  The **encLits / satisfying-completion route**
(`canonMarkLabel_switching_count`, `canon_count_pathLenBad`, `pathLenBadGt_card_le`) is *complete* —
it sidesteps the wall because its completion `σ*` makes "first satisfied term" identify the active
clause.  This file uses that complete route to bound the depth-bad set and extract a good restriction.

The encLits route controls `canonLabelLen ρ cs` — the length of the **single satisfying-completion
path**.  `pathLenBadGt_card_le` bounds `{ρ : canonLabelLen ρ cs > budget}` by the geometric sum
`∑_{budget<s≤maxLen} |Short s|·(2w)^s`.  Feeding that through the pigeonhole:

* `exists_good_canonLabelLen` — if the geometric sum is `< #restrictions`, there is a restriction
  with `canonLabelLen ρ cs ≤ budget`: the encLits depth-bad set is bounded and a good restriction
  exists, entirely via the complete (wall-free) route.

## Honest scope

`canonLabelLen` is the **single satisfying-completion path** length, one branch of the canonical tree;
the max-branch `canonicalDT.depth` satisfies `canonLabelLen ≤ depth` (`TightDepth`), and a
depth-`≤budget` *decision tree* computing `D|ρ` needs the **max** depth `≤ budget`.  So this good
restriction is `canonLabelLen`-good, not necessarily `canonicalDT.depth`-good — closing that gap is
the deepest-branch switching content (the empty-skip wall), **not** claimed here.  What is delivered:
the encLits route bounds *its* depth measure and yields a good restriction with no wall in the way.
AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **A good restriction for the encLits depth measure.**  The encLits geometric-sum count
(`pathLenBadGt_card_le`) bounds the canonLabelLen-bad set; if that bound is below the total number of
restrictions, the pigeonhole yields a restriction whose satisfying-completion path is short
(`canonLabelLen ρ cs ≤ budget`).  The whole argument runs through the complete encLits route — the
empty-skip wall never appears. -/
theorem exists_good_canonLabelLen {w : ℕ} [NeZero w] {cs : List (Clause n)}
    {Short : ℕ → Finset (Restriction n)} {budget maxLen : ℕ}
    (hcs : ∀ T ∈ cs, (T.lits.map litVar).Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hmax : ∀ ρ : Restriction n, canonLabelLen ρ cs ≤ maxLen)
    (hne : ∀ s : ℕ, ∀ ρ ∈ pathLenBad cs s, ∀ b ∈ canonPosBlocks (encLits ρ cs) ∅
        (cs.filter (termSat (complete ρ (encLits ρ cs)))), b ≠ [])
    (hmem : ∀ s : ℕ, ∀ ρ ∈ pathLenBad cs s, complete ρ (encLits ρ cs) ∈ Short s)
    (hlt : (∑ s ∈ (Finset.range (maxLen + 1)).filter (fun s => budget < s),
              (Short s).card * (2 * w) ^ s)
            < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, canonLabelLen ρ cs ≤ budget := by
  have hcount := pathLenBadGt_card_le hcs hwidth hmax hne hmem (budget := budget)
  have hbad : (Finset.univ.filter (fun ρ : Restriction n => budget < canonLabelLen ρ cs)).card
      < (Finset.univ : Finset (Restriction n)).card := lt_of_le_of_lt hcount hlt
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset (Restriction n))
      ⊆ Finset.univ.filter (fun ρ : Restriction n => budget < canonLabelLen ρ cs) := by
    intro ρ _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ ρ, h ρ⟩
  exact absurd (Finset.card_le_card hsub) (not_le.mpr hbad)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_good_canonLabelLen
