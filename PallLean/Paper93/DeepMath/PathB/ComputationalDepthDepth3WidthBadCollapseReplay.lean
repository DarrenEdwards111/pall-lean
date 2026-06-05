import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NoSkipReplayToDepthBound

/-!
# Threading the replay depth-bound count into the collapse pipeline

The collapse pipeline's pigeonhole and DT-extraction (`exists_good_restriction`,
`widthBad_yields_short_dt`) are *completion-agnostic*: they need only `|widthBad| ≤ |Short|·(2w)^s <
#restrictions`.  So the deepest-branch replay count (`deepest_noskip_tight_count_depth`) can feed them
directly — an alternative to the `encLits`/`complete` route used by `widthBad_collapse_dt`.

* `widthBad_collapse_dt_replay` — under the replay route's (structural) conditions on `Bad` and a
  decision-tree depth budget, a restriction outside `widthBad` exists and yields a short decision tree
  computing `D`.

This wires the replay arc into collapse with the deepest end-state `deepestEnd` as the completion: the
count bounds `widthBad` (via `hincl`), pigeonhole gives a good `ρ`, and `widthBad_yields_short_dt`
extracts the tree.  The structural inclusion `hincl : widthBad ⊆ Bad` (residual width ⟹ membership in
the recoverable bad set) remains the open G1-core gate, identical to the `encLits` route; **not** faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Collapse via the replay depth-bound count.**  For the replay route's recoverable bad set `Bad`
(falsifies nothing, unsatisfied deepest leaf, no-skip, `s` satisfy steps with `s ≤ depthBudget`, clean
clause widths `≤ w`, deepest end-states in `Short`) containing `widthBad`, with the parameter condition
`|Short|·(2w)^depthBudget < #restrictions`: a restriction outside `widthBad` exists, yielding a
decision tree of depth `≤ depthBudget` computing `D` on its subcube. -/
theorem widthBad_collapse_dt_replay {w F : ℕ} [NeZero w] {cs : List (Clause n)} {D : Rung4DNF n}
    {Bad Short : Finset (Restriction n)} {depthBudget s : ℕ}
    (hnd : cs.Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ Bad, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hsteps : ∀ ρ ∈ Bad, (deepestSatSeq cs F ρ).length = s)
    (hsD : s ≤ depthBudget)
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hincl : widthBad D depthBudget ⊆ Bad)
    (hlt : Short.card * (2 * w) ^ depthBudget
      < (Finset.univ : Finset (Restriction n)).card) :
    ∃ ρ : Restriction n, ∃ T : BoolDecisionTree n,
      T.depth ≤ depthBudget ∧
      ∀ x : Fin n → Bool, Rung4Restriction.Extends ρ x → T.eval x = D.eval x := by
  have hcount := deepest_noskip_tight_count_depth hnd hwidth hmem hnf hleaf hns hsteps hsD
  have hwbcount : (widthBad D depthBudget).card ≤ Short.card * (2 * w) ^ depthBudget :=
    le_trans (Finset.card_le_card hincl) hcount
  exact widthBad_yields_short_dt (exists_good_restriction hwbcount hlt)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.widthBad_collapse_dt_replay
