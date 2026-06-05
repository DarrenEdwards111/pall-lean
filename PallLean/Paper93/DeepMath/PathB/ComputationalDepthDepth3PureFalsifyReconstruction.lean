import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Threading
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction

/-!
# The reverse-induction decoder, closed for the pure-falsify regime

The reverse-induction decoder must recover `deepestSel` (the selected-variable set) from the deepest
end-state and a label — the open `ReconstructionCorrect` target.  The threading decomposition
`decodedSel (deepestEnd …) ∪ deepestSatSel = deepestSel` splits this into:

* the **falsify-step** variables, read off the end-state **label-free** by `decodedSel` (each carries
  a false literal that persists to the leaf), and
* the **satisfy-step** variables `deepestSatSel`, which is where the `(2w)^s` label and the
  active-clause-identification wall live.

This file closes the decoder completely in the **pure-falsify regime** — branches with *no* satisfy
step (`deepestSatSel = ∅`), i.e. the all-falsify branch that realises the depth
(`canonicalDT_depth_ge_replay`).  There the reverse-induction decoder is simply `decodedSel` of the
end-state: every path variable is a false literal visible at the leaf.  This is the honest
counterpart of the proven *pure-satisfy* regime.

* `deepestEnd_injOn_pure_falsify` — on a pure-falsify `Bad` set, the end-state **alone** determines
  `ρ` (no label needed): `deepestSel` is recovered as `decodedSel (deepestEnd …)`.
* `deepest_pure_falsify_count` — hence `|Bad| ≤ |Short|` (sharper than `(2w)^s`: the label carries no
  information when there are no satisfy steps).
* `reconstruction_pure_falsify` — discharges `ReconstructionCorrect` itself (decoder `= decodedSel`,
  satisfy-decoder `= ∅`), so the depth-count interface `deepest_switching_count_of_reconstruction`
  applies for any `s`.

## What remains (honest)

This closes the regime where the depth comes entirely from falsifications.  The complementary content
— branches with genuine satisfy steps, where `deepestSatSel ≠ ∅` and the `(2w)^s` label plus
active-clause identification are needed — is **not** discharged here; that is the remaining core of
`ReconstructionCorrect`.  Both extreme regimes (pure-satisfy, pure-falsify) are now closed; the
interleaved general case is the residual wall.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP
untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Pure-falsify: the end-state alone determines `ρ`.**  When the deepest branch has no satisfy step
(`deepestSatSel cs F ρ = ∅`) and `ρ` falsifies no term, `deepestSel = decodedSel (deepestEnd …)` is a
function of the end-state, so equal end-states force `ρ = σ` (`deepestEnd_inj`). -/
theorem deepestEnd_injOn_pure_falsify {cs : List (Clause n)} {F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hpf : ∀ ρ ∈ Bad, deepestSatSel cs F ρ = ∅) :
    ∀ ρ ∈ Bad, ∀ σ ∈ Bad, deepestEnd cs F ρ = deepestEnd cs F σ → ρ = σ := by
  intro ρ hρ σ hσ hE
  refine deepestEnd_inj cs F hE ?_
  rw [← decodedSel_union_satSel_eq_deepestSel (hnf ρ hρ),
      ← decodedSel_union_satSel_eq_deepestSel (hnf σ hσ),
      hpf ρ hρ, hpf σ hσ, hE]

/-- **The sharp pure-falsify count.**  With the end-state in `Short`, `ρ` falsifying nothing, and no
satisfy step on the deepest branch, the end-state is injective on `Bad`, so `|Bad| ≤ |Short|` — no
`(2w)^s` factor: the falsify-only path is read entirely off the leaf. -/
theorem deepest_pure_falsify_count {cs : List (Clause n)} {F : ℕ}
    {Bad Short : Finset (SwitchingCounting.Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hpf : ∀ ρ ∈ Bad, deepestSatSel cs F ρ = ∅) :
    Bad.card ≤ Short.card :=
  Finset.card_le_card_of_injOn (deepestEnd cs F) hmem (deepestEnd_injOn_pure_falsify hnf hpf)

/-- **`ReconstructionCorrect` discharged for the pure-falsify regime.**  The satisfy-step decoder is
`∅` (no satisfy steps), so the full reverse decoder is `decodedSel` of the end-state.  Any label `lab`
works since it is ignored. -/
theorem reconstruction_pure_falsify {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hpf : ∀ ρ ∈ Bad, deepestSatSel cs F ρ = ∅)
    (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s) :
    ReconstructionCorrect cs w s F Bad :=
  reconstruction_of_satSel_decoder hnf (fun _ _ => ∅) lab (fun ρ hρ => (hpf ρ hρ).symm)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestEnd_injOn_pure_falsify
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_pure_falsify_count
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_pure_falsify
