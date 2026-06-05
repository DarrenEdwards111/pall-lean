import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqDepth

/-!
# No-skip replay count → decision-tree depth bound (the collapse bridgehead)

The collapse pipeline counts bad sets by the canonical decision-tree **depth**.  The replay count is by
`s = #satisfy steps ≤ depth` (`deepestSatSeq_length_le_depth`), so its label cost `(2w)^s` is bounded
by `(2w)^depth`.  This file packages that into the exact form the collapse wiring consumes: under the
no-skip structural hypotheses, with a uniform depth bound `D`,

    |Bad| ≤ |Short| · (2w)^D.

* `pow_satstep_le_pow_depth` — `(2w)^(deepestSatSeq …).length ≤ (2w)^(canonicalDT …).depth`.
* `deepest_noskip_tight_count_depth` — the no-skip tight count rebased on a depth bound `D ≥ s`.

This is the compact, referee-clean theorem the collapse layer can consume — no fake general theorem,
the empty-skip wall stays out of the claim.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Label cost is bounded by the depth.**  Since the satisfy-step count is at most the canonical
decision-tree depth, `(2w)^(#satisfy steps) ≤ (2w)^depth`. -/
theorem pow_satstep_le_pow_depth {w : ℕ} [NeZero w] (cs : List (Clause n)) (F : ℕ)
    (σ : Fin n → Option Bool) :
    (2 * w) ^ (deepestSatSeq cs F σ).length ≤ (2 * w) ^ (canonicalDT cs F σ).depth :=
  Nat.pow_le_pow_right (by have := NeZero.pos w; omega) (deepestSatSeq_length_le_depth cs F σ)

/-- **No-skip tight count, rebased on a depth bound.**  Under the no-skip structural hypotheses with
`s` satisfy steps and a uniform depth bound `s ≤ D`, `|Bad| ≤ |Short| · (2w)^D`.  This is the compact
theorem the collapse pipeline consumes: the recoverable (no-skip, width-`≤w`) bad set is counted by the
decision-tree depth. -/
theorem deepest_noskip_tight_count_depth {cs : List (Clause n)} {w s D F : ℕ} [NeZero w]
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hnd : cs.Nodup)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ Bad, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hsteps : ∀ ρ ∈ Bad, (deepestSatSeq cs F ρ).length = s)
    (hsD : s ≤ D) :
    Bad.card ≤ Short.card * (2 * w) ^ D :=
  calc Bad.card
      ≤ Short.card * (2 * w) ^ s :=
        deepest_noskip_tight_count_satsteps hnd hw hmem hnf hleaf hns hsteps
    _ ≤ Short.card * (2 * w) ^ D :=
        Nat.mul_le_mul (le_refl _)
          (Nat.pow_le_pow_right (by have := NeZero.pos w; omega) hsD)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pow_satstep_le_pow_depth
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_noskip_tight_count_depth
