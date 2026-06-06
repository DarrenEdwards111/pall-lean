import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverRhoObligation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqMono
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqContiguity

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

/-- **OPEN — the sharpened switching-lemma core.**  The clause-order forward-replay reconstruction of
the satisfy *sequence* `deepestSatSeq` (the `(clause, position)` list, exactly what the forward
simulation produces) from the leaf and the tight `(2w)^s` label, for the general bad set.  This is the
single irreducible step; `confound_uncovered` proves no cheaper alignment closes it.
*WIP `sorry` — branch only.*

The forward simulation that discharges this: process clauses in `cs`-order from the leaf; for each
clause stay in it until it resolves (`activeTerm_advance_stable` keeps it active across satisfy steps,
`activeTerm_falsify_advances` moves to a later clause on a falsify step — so **block sizes are
determined dynamically**, never read from the lost label boundaries); consume the next label position
as a satisfy step, or read a falsify step off `σ_end`.  Correctness is the Håstad switching lemma.

The structural backbone — **clause-order monotonicity** — is now PROVED (clean axioms, no `sorry`) in
`ComputationalDepthDepth3DeepestSatSeqMono`: `deepestSatSeq_clause_mem_activeSuffix` shows every clause
recorded in `deepestSatSeq cs F σ` lies in the active suffix `activeSuffix cs σ` (the tail of `cs` from
the active clause), and `activeSuffix_fixVar_suffix` shows that suffix only advances along the descent.
For distinct clauses (`cs.Nodup`, the Tseitin/DNF case) this sharpens to full **clause-order
contiguity** — `deepestSatSeq_idxOf_pairwise` (in `…DeepestSatSeqContiguity`): the `cs`-indices of the
recorded clauses are non-decreasing, so each clause's satisfy steps form one contiguous block (exactly
the dynamic block the simulation consumes label positions into).  So the simulation may legitimately
process `cs` in order, one contiguous block per clause; what remains is defining the dynamic-block
`Dseq` and proving it matches, the residual Håstad content. -/
theorem deepestSatSeq_recover {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad, (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    ∃ (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
      (Dseq : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s
          → List (Clause n × ℕ)),
      ∀ ρ ∈ Bad, Dseq (deepestEnd cs F ρ) (lab ρ) = deepestSatSeq cs F ρ := by
  sorry

/-- **The satisfy-set reconstruction reduces (proved, no gap) to recovering the satisfy *sequence*.**
`deepestSatSel = decodeSatSeq deepestSatSeq` (`deepestSatSel_eq_decodeSatSeq`), so a sequence-recoverer
gives a set-recoverer by post-composing `decodeSatSeq`. -/
theorem satSeqReconstruct_general {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ ∈ Bad, ∀ p ∈ SwitchingCounting.ungroupBlocks (replayLabel cs F ρ), p.1 < w)
    (hlen : ∀ ρ ∈ Bad, (SwitchingCounting.ungroupBlocks (replayLabel cs F ρ)).length = s) :
    ∃ (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
      (Dsat : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s → Finset (Fin n)),
      ∀ ρ ∈ Bad, Dsat (deepestEnd cs F ρ) (lab ρ) = deepestSatSel cs F ρ := by
  obtain ⟨lab, Dseq, hseq⟩ := deepestSatSeq_recover hnf hleaf hpos hlen
  refine ⟨lab, fun σ l => decodeSatSeq (Dseq σ l), fun ρ hρ => ?_⟩
  show decodeSatSeq (Dseq (deepestEnd cs F ρ) (lab ρ)) = deepestSatSel cs F ρ
  rw [hseq ρ hρ]
  exact (deepestSatSel_eq_decodeSatSeq cs F ρ).symm

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
