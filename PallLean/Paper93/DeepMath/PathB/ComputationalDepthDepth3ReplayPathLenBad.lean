import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WidthBadCollapseReplay
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter

/-!
# Replay route G1-core: the count bounds the *path-length* bad set directly

`widthBad` (the `totalWidth`-based bad set) is the **wrong** set — the bridge records that
`widthBad ⊆ Bad` is not dischargeable, because a large `totalWidth` (a *sum* over surviving terms)
does not force a long canonical path.  The **correct** bad set is depth/path-length based: the
restrictions whose deepest-branch satisfy count is exactly `s`.  The replay count bounds *that* set
directly — the inclusion is definitional (filter membership), so there is no structural gate.

This is the honest replay-route analog of `canon_count_pathLenBad`.

* `deepestPathLenBad cs F s` — `{ρ : (deepestSatSeq cs F ρ).length = s}`.
* `replay_count_pathLenBad` — `|deepestPathLenBad cs F s| ≤ |Short| · (2w)^s`, directly from
  `deepest_noskip_tight_count_satsteps` (its `hsteps` holds by definition on this set).
* `replay_pathLenBad_le_depthBad` — the path-length bad set is contained in
  `{ρ : (canonicalDT cs F ρ).depth ≥ s}` (satisfy count ≤ depth), so it is genuinely a *decision-tree
  depth* slice — not a `totalWidth` slice.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The replay-route **path-length bad set**: restrictions whose deepest-branch satisfy count is
exactly `s` (the canonical-decision-tree quantity the `(2w)^s` count controls). -/
def deepestPathLenBad (cs : List (Clause n)) (F s : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ => (deepestSatSeq cs F ρ).length = s)

/-- **The replay count bounds the path-length bad set directly.**  The size condition `hsteps` of
`deepest_noskip_tight_count_satsteps` holds by definition on `deepestPathLenBad cs F s`, so there is no
structural inclusion gate: `|deepestPathLenBad cs F s| ≤ |Short| · (2w)^s`. -/
theorem replay_count_pathLenBad {w s F : ℕ} [NeZero w] {cs : List (Clause n)}
    {Short : Finset (Restriction n)}
    (hnd : cs.Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hnf : ∀ ρ ∈ deepestPathLenBad cs F s, ∀ T ∈ cs, termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ deepestPathLenBad cs F s, anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ deepestPathLenBad cs F s, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hmem : ∀ ρ ∈ deepestPathLenBad cs F s, deepestEnd cs F ρ ∈ Short) :
    (deepestPathLenBad cs F s).card ≤ Short.card * (2 * w) ^ s := by
  refine deepest_noskip_tight_count_satsteps hnd hwidth hmem hnf hleaf hns ?_
  intro ρ hρ
  simp only [deepestPathLenBad, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  exact hρ

/-- **The path-length bad set is a decision-tree-depth slice (not a `totalWidth` slice).**  On it the
canonical decision-tree depth is at least `s` — confirming it is the correct, depth-based bad set. -/
theorem replay_pathLenBad_le_depthBad (cs : List (Clause n)) (F s : ℕ) :
    deepestPathLenBad cs F s ⊆
      Finset.univ.filter (fun ρ => s ≤ (canonicalDT cs F ρ).depth) := by
  intro ρ hρ
  simp only [deepestPathLenBad, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  rw [← hρ]
  exact deepestSatSeq_length_le_depth cs F ρ

/-- **Uniform bound on the satisfy count.**  The deepest-branch satisfy count is at most the fuel `F`
(satisfy count `≤` canonical DT depth `≤` fuel) — the `maxLen` needed for the geometric summation. -/
theorem replay_satCount_le_fuel (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) :
    (deepestSatSeq cs F ρ).length ≤ F :=
  le_trans (deepestSatSeq_length_le_depth cs F ρ) (canonicalDT_depth_le cs F ρ)

/-- **The geometric sum: the long-path bad set is bounded by the per-`s` replay counts.**  The set
`{ρ : (deepestSatSeq cs F ρ).length > budget}` is the disjoint union of `deepestPathLenBad cs F s` over
`budget < s ≤ F`, so by `replay_count_pathLenBad`,

  `|{ρ : satisfy count > budget}|  ≤  ∑_{budget < s ≤ F} |Short s| · (2w)^s`.

This is the standard switching-lemma summation over decision-tree depths, on the deepest-branch replay
route.  The bound is finite because the satisfy count is `≤ F` (`replay_satCount_le_fuel`); no
`totalWidth` (`widthBad`) set appears — the gate is purely depth-based. -/
theorem replay_pathLenBadGt_card_le {w F : ℕ} [NeZero w] {cs : List (Clause n)}
    {Short : ℕ → Finset (Restriction n)} {budget : ℕ}
    (hnd : cs.Nodup)
    (hwidth : ∀ T ∈ cs, T.lits.length ≤ w)
    (hnf : ∀ s : ℕ, ∀ ρ ∈ deepestPathLenBad cs F s, ∀ T ∈ cs, termFalsified ρ T = false)
    (hleaf : ∀ s : ℕ, ∀ ρ ∈ deepestPathLenBad cs F s, anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ s : ℕ, ∀ ρ ∈ deepestPathLenBad cs F s, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hmem : ∀ s : ℕ, ∀ ρ ∈ deepestPathLenBad cs F s, deepestEnd cs F ρ ∈ Short s) :
    (Finset.univ.filter (fun ρ : Restriction n => budget < (deepestSatSeq cs F ρ).length)).card
      ≤ ∑ s ∈ (Finset.range (F + 1)).filter (fun s => budget < s),
          (Short s).card * (2 * w) ^ s := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ρ : Restriction n => (deepestSatSeq cs F ρ).length)
    (t := (Finset.range (F + 1)).filter (fun s => budget < s))
    (fun ρ hρ => by
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range] at hρ ⊢
      exact ⟨Nat.lt_succ_of_le (replay_satCount_le_fuel cs F ρ), hρ⟩)]
  refine Finset.sum_le_sum (fun s hs => ?_)
  simp only [Finset.mem_filter, Finset.mem_range] at hs
  have heq : (Finset.univ.filter
      (fun ρ : Restriction n => budget < (deepestSatSeq cs F ρ).length)).filter
        (fun ρ => (deepestSatSeq cs F ρ).length = s) = deepestPathLenBad cs F s := by
    ext ρ
    simp only [deepestPathLenBad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [heq]
  exact replay_count_pathLenBad hnd hwidth (hnf s) (hleaf s) (hns s) (hmem s)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_count_pathLenBad
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_pathLenBad_le_depthBad
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_satCount_le_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_pathLenBadGt_card_le
