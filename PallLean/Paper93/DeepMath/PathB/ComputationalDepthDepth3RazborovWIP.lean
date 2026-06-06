import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverRhoObligation

/-!
# WORK IN PROGRESS (branch `razborov-recoverRho-wip` — NOT for main)

Start of the Razborov/Håstad forward-replay reconstruction that discharges depth-3 Obligation 1 for
the **general** bad set (including the confound).  The `sorry` below is the single genuinely-open
switching-lemma step — `satSeqReconstruct_general` — and is **explicitly** the open core, not a hidden
gap.  Everything else (the reduction to it, and the determined-regime cases) is proved.

## Proof skeleton (the induction to fill in)

`recoverRho` correctness ⇔ `ReconstructionCorrect` ⇔ recovering `deepestSel` from `(σ_end, label)`
(`recoverRhoObligation_iff_reconstructionCorrect`, proved, via `freeOn_deepestEnd`).
`deepestSel = decodedSel(σ_end) ∪ deepestSatSel` with `decodedSel` label-free (proved).  So the entire
content is the **satisfy-step reconstruction** `satSeqReconstruct_general`: recover `deepestSatSel`
from `(σ_end, (2w)^s label)` for every bad `ρ`.

Razborov's clause-order forward-replay (the induction to carry out, on the canonical recursion / fuel):
* **base** `anyTermSat (deepestEnd) = false` reached at a leaf with no further steps: `deepestSatSel = ∅`.
* **falsify step** (active `T`, first free lit set to its false polarity): the variable is recovered
  label-free from `σ_end` (`decodedSel`); recurse.
* **satisfy step** (active `T`, first free lit set true): record its position in the active clause; the
  active clause is determined by the *reconstructed-so-far* restriction (clause-order), **not** read
  off `σ_end` — this is what defeats the confound (`confound_uncovered`) and is the irreducible step.
* the per-clause satisfy positions, attributed by this forward simulation, feed `decodeSatSeq` to
  rebuild `deepestSatSel`.

The proven determined regimes (`recoverRho_no_skip`, `recoverRho_clean_skip`, `recoverRho_align`) are
exactly the special cases where the attribution does *not* need the full forward simulation.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **OPEN — the switching-lemma core.**  The clause-order forward-replay reconstruction of the
satisfy-step selected set from the leaf and the tight `(2w)^s` label, for the general bad set
(including the confound).  This is the single irreducible step; `confound_uncovered` proves no cheaper
alignment closes it.  *WIP `sorry` — branch only.* -/
theorem satSeqReconstruct_general {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad, (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    ∃ (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
      (Dsat : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s → Finset (Fin n)),
      ∀ ρ ∈ Bad, Dsat (deepestEnd cs F ρ) (lab ρ) = deepestSatSel cs F ρ := by
  sorry

/-- **The general `recoverRho` obligation, modulo the open satisfy-reconstruction.**  This proof is
complete *except* for `satSeqReconstruct_general` — it shows the entire Razborov reconstruction reduces
to that single step (no further gaps): the falsify half is the proved label-free `decodedSel`, glued by
`reconstruction_of_satSel_decoder`, transported across `recoverRhoObligation_iff_reconstructionCorrect`. -/
theorem recoverRho_general {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad, (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    RecoverRhoObligation cs w s F Bad := by
  rw [recoverRhoObligation_iff_reconstructionCorrect]
  obtain ⟨lab, Dsat, hsat⟩ := satSeqReconstruct_general hnf hleaf hpos hlen
  exact reconstruction_of_satSel_decoder hnf Dsat lab hsat

end Depth3

end PallLean.Paper93.DeepMath.PathB
