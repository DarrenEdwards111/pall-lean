import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeq

/-!
# Block-delimiting interface: reduce `ReconstructionCorrect` to per-clause position blocks

The per-step-clause decode (`deepestSatSel_eq_decodeSatSeq`) is order-insensitive (a `toFinset`), so
the decoder need only produce the right `(clause, position)` *set*.  This file reduces the general
`ReconstructionCorrect` to producing **per-clause position blocks** — a `List (Clause × List ℕ)`
assigning each clause its block of positions — from the end-state and label.  This is exactly the
block-delimiting target, with the decode and the reduction fully discharged.

* `ungroupClauseBlocks` — flatten per-clause position blocks `[(C, [p₀,p₁,…]), …]` to the
  `(clause, position)` pairs `[(C,p₀),(C,p₁),…, …]`.
* `reconstruction_of_satSeq_decoder` — `ReconstructionCorrect` follows from any decoder recovering the
  `(clause, position)` sequence `deepestSatSeq` from `(end-state, label)` (decode discharged via
  `deepestSatSel_eq_decodeSatSeq`).
* `reconstruction_of_blockDecoder` — the block form: `ReconstructionCorrect` follows from a decoder
  producing per-clause position blocks whose flattening is `deepestSatSeq`.

So the entire general interleaved `ReconstructionCorrect` now hinges on **one** construction: from the
end-state, enumerate the leaf-readable clauses in `cs`-order (`deepestSatSeq_clause_leaf`,
`deepest_falsified_clause_active`) and assign each its label-position block.  Everything downstream is
proved here.  That block-assignment construction is the remaining work; not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Flatten per-clause position blocks into `(clause, position)` pairs. -/
def ungroupClauseBlocks (blocks : List (Clause n × List ℕ)) : List (Clause n × ℕ) :=
  blocks.flatMap (fun cb => cb.2.map (fun p => (cb.1, p)))

/-- **Reduction to the `(clause, position)`-sequence decoder.**  `ReconstructionCorrect` follows from
any decoder recovering `deepestSatSeq` from the end-state and label — the order-insensitive decode
`decodeSatSeq` then recovers `deepestSatSel` (`deepestSatSel_eq_decodeSatSeq`). -/
theorem reconstruction_of_satSeq_decoder {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (Dseq : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s → List (Clause n × ℕ))
    (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (hseq : ∀ ρ ∈ Bad, Dseq (deepestEnd cs F ρ) (lab ρ) = deepestSatSeq cs F ρ) :
    ReconstructionCorrect cs w s F Bad :=
  reconstruction_of_satSel_decoder hnf (fun π l => decodeSatSeq (Dseq π l)) lab
    (fun ρ hρ => by
      show decodeSatSeq (Dseq (deepestEnd cs F ρ) (lab ρ)) = deepestSatSel cs F ρ
      rw [hseq ρ hρ]; exact (deepestSatSel_eq_decodeSatSeq cs F ρ).symm)

/-- **Reduction to the block decoder.**  `ReconstructionCorrect` follows from a decoder producing
per-clause position blocks whose flattening is `deepestSatSeq`.  This is the precise block-delimiting
target: assign each leaf-readable clause its block of label positions. -/
theorem reconstruction_of_blockDecoder {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (Dblk : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s →
      List (Clause n × List ℕ))
    (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (hblk : ∀ ρ ∈ Bad,
      ungroupClauseBlocks (Dblk (deepestEnd cs F ρ) (lab ρ)) = deepestSatSeq cs F ρ) :
    ReconstructionCorrect cs w s F Bad :=
  reconstruction_of_satSeq_decoder hnf (fun π l => ungroupClauseBlocks (Dblk π l)) lab hblk

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_of_satSeq_decoder
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_of_blockDecoder
