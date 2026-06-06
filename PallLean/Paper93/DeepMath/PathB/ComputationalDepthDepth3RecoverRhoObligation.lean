import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ConfoundFence

/-!
# The open core of Obligation 1, as a named target: `recoverRho`

The satisfy-step switching obligation (`ReconstructionCorrect`) is proved in **five regimes**
(pure-satisfy, pure-falsify, no-skip, align, clean-skip) and its residual is **machine-checked** to be
the confound (`confound_uncovered`): a clause falsified at the leaf that *also* received satisfy steps,
indistinguishable at `(deepestEnd, (2w)^s label)` from a clean skip.  The fences
(`encLits_length_lt_depth`, `tight_pack_skip_invariant`, `confound_uncovered`) prove no cheap alignment
trick closes it: the only route is the **Håstad/Razborov clause-order forward-replay reconstruction**
of the restriction `ρ`.

This file states that core as a **named target** and *characterises it exactly* — without proving it
(no `sorry`, no fake theorem):

* `RecoverRhoObligation` — the open target: a `(2w)^s` label `lab` and a recovery map `recoverRho`
  with `recoverRho (deepestEnd cs F ρ) (lab ρ) = ρ` for every `ρ ∈ Bad`.
* `recoverRhoObligation_iff_reconstructionCorrect` — **proved**: the forward-replay obligation is
  *equivalent* to `ReconstructionCorrect`.  The bridge is the already-proved foundational invariant
  `freeOn_deepestEnd` (`freeOn (deepestEnd cs F ρ) (deepestSel cs F ρ) = ρ`): recovering `ρ` ⇔
  recovering the selected set `deepestSel` from the leaf and the label.

So building the clause-order forward-replay (`recoverRho`) and building the satisfy-step decoder are
the **same** problem — the genuine switching-lemma reconstruction, no shortcut.  Discharging either
discharges depth-3 Obligation 1.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.

## What remains (honest)

The open work is the **forward-replay induction**: define `recoverRho` as the clause-order
reconstruction (process clauses in `cs`-order; from `σ_end`, the packed label, and the canonical
deepest-step rules, decide for each clause which variables were `ρ`-fixed / path-selected /
satisfy-recorded / later-falsified; free the selected ones) and prove
`recoverRho (deepestEnd cs F ρ) (lab ρ) = ρ` for bad `ρ`.  This file fixes the target and proves it is
exactly the switching-lemma core; it does **not** carry out that induction.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The open Håstad/Razborov reconstruction obligation.**  A `(2w)^s` label `lab` and a recovery
map `recoverRho` reconstructing the restriction `ρ` from its leaf state and label, for every `ρ` in the
bad set.  *Stated, not proved* — the single residual core of Obligation 1, fenced by
`encLits_length_lt_depth`, `tight_pack_skip_invariant`, and `confound_uncovered`. -/
def RecoverRhoObligation (cs : List (Clause n)) (w s F : ℕ)
    (Bad : Finset (SwitchingCounting.Restriction n)) : Prop :=
  ∃ (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (recoverRho : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s
        → SwitchingCounting.Restriction n),
    ∀ ρ ∈ Bad, recoverRho (deepestEnd cs F ρ) (lab ρ) = ρ

/-- **The forward-replay obligation is exactly `ReconstructionCorrect`** (proved, via the foundational
invariant `freeOn_deepestEnd`).  Recovering `ρ` from the leaf ⇔ recovering the selected set
`deepestSel`.  So the clause-order `recoverRho` and the satisfy-step decoder are the same problem —
there is no shortcut; both are the switching-lemma reconstruction. -/
theorem recoverRhoObligation_iff_reconstructionCorrect (cs : List (Clause n)) (w s F : ℕ)
    (Bad : Finset (SwitchingCounting.Restriction n)) :
    RecoverRhoObligation cs w s F Bad ↔ ReconstructionCorrect cs w s F Bad := by
  constructor
  · rintro ⟨lab, recoverRho, hrec⟩
    refine ⟨lab, fun σ l => deepestSel cs F (recoverRho σ l), fun ρ hρ => ?_⟩
    show deepestSel cs F (recoverRho (deepestEnd cs F ρ) (lab ρ)) = deepestSel cs F ρ
    rw [hrec ρ hρ]
  · rintro ⟨lab, D, hD⟩
    refine ⟨lab, fun σ l => SwitchingCounting.freeOn σ (D σ l), fun ρ hρ => ?_⟩
    show SwitchingCounting.freeOn (deepestEnd cs F ρ) (D (deepestEnd cs F ρ) (lab ρ)) = ρ
    rw [hD ρ hρ]
    exact freeOn_deepestEnd cs F ρ

/-! ## `recoverRho` discharged for every determined regime

The forward-replay obligation is *proved* (no `sorry`) for all the regimes where the reconstruction is
determined — no-skip, clean-skip, align — by transporting the proved `ReconstructionCorrect` across the
equivalence.  The single regime left open is the confound (`confound_uncovered`), whose forward-replay
correctness is the Håstad switching lemma. -/

/-- `recoverRho` discharged for the interleaved **no-skip** regime. -/
theorem recoverRho_no_skip {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hns : ∀ ρ ∈ Bad, ∀ b ∈ replayLabel cs F ρ, b ≠ [])
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad, (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    RecoverRhoObligation cs w s F Bad :=
  (recoverRhoObligation_iff_reconstructionCorrect cs w s F Bad).mpr
    (reconstruction_no_skip hnf hleaf hns hpos hlen)

/-- `recoverRho` discharged for the **clean interior-skip** regime (`hskip`). -/
theorem recoverRho_clean_skip {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad, (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s)
    (hskip : ∀ ρ ∈ Bad, ∀ C ∈ leafClauses cs (deepestEnd cs F ρ),
      (deepestSatPositions cs F ρ C = [] ↔
        SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = true)) :
    RecoverRhoObligation cs w s F Bad :=
  (recoverRhoObligation_iff_reconstructionCorrect cs w s F Bad).mpr
    (reconstruction_clean_skip hnf hleaf hpos hlen hskip)

/-- `recoverRho` discharged under the exact **alignment** hypothesis `halign`. -/
theorem recoverRho_align {cs : List (Clause n)} {w s F : ℕ} [NeZero w]
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad, (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s)
    (halign : ∀ ρ ∈ Bad,
      replayBlocks cs (deepestEnd cs F ρ) (replayLabel cs F ρ)
        = replayBlocks cs (deepestEnd cs F ρ)
            ((replayLabel cs F ρ).filter (fun b => !b.isEmpty))) :
    RecoverRhoObligation cs w s F Bad :=
  (recoverRhoObligation_iff_reconstructionCorrect cs w s F Bad).mpr
    (reconstruction_align hnf hleaf hpos hlen halign)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recoverRhoObligation_iff_reconstructionCorrect
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.recoverRho_clean_skip
