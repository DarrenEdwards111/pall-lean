import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3WitnessLabel

/-!
# Tight switching, step 25: the witnessed tight count — `(Cw)^s`, `hnf`-free in shape (branch `razborov-recoverRho-wip`)

Assembling the injection with the witness-augmented label (step 24).  The original tight count consumer
`deepest_switching_count_of_reconstruction` takes a `ReconstructionCorrect` (a `(2w)^s` `PathLabel` decoder)
and gives `|Bad| ≤ |Short|·(2w)^s` — but the only known proof of `ReconstructionCorrect` needs `hnf`
(empty-skip wall).  Here we swap the `PathLabel` for the witness label `WitLabel w s m` (step 24): the
decoder is *handed* the per-step active-clause witness, so it never has to disambiguate dead clauses by
scanning, and `hnf` is unnecessary in the count.

`card_bad_le_label_card` is generic over the label type, so the assembly is immediate: a witnessed
reconstruction `WitnessReconstructionCorrect` (a `WitLabel`-decoder recovering `deepestSel` from `deepestEnd`
plus the witness) yields, via `deepestEnd_inj` and `card_witLabels_le`,

```
  |Bad| ≤ |Short| · (2·w·m)^s,
```

the `(Cw)^s` shape (`C = m`, the clause-count bound), **independent of the fuel `F`** and with **no `hnf`
hypothesis** in the count.

* `WitnessReconstructionCorrect` — the witness-decoder invariant (the `hnf`-free target).
* `deepest_count_of_witness` — `WitnessReconstructionCorrect ⟹ |Bad| ≤ |Short|·(2wm)^s`.

## Honest scope

This is the injection assembled at `(2wm)^s` with no `hnf` in the count.  What remains is *constructing* the
witnessed decoder: the per-step witness records the active clause's index (`activeIdx`, recovered by
`getElem_activeIdx`, step 24) and the free-literal position, and the path-recovery is `hnf`-free via the
live-witness decoder (`decodedSel_filter_eq_replaySel`, step 23).  Discharging `WitnessReconstructionCorrect`
from those two ingredients (plus the satisfy-step handling) is the last mile to an unconditional tight count;
it is the genuine remaining switching-lemma content, not faked here.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The witnessed reconstruction invariant.**  A `WitLabel w s m` decoder recovering the deepest-branch
selected set from the end-state plus the per-step active-clause witness — *no* `hnf`, because the witness
identifies live clauses directly. -/
def WitnessReconstructionCorrect (cs : List (Clause n)) (w s F m : ℕ)
    (Bad : Finset (Restriction n)) : Prop :=
  ∃ (lab : Restriction n → SwitchingCounting.WitLabel w s m)
    (D : Restriction n → SwitchingCounting.WitLabel w s m → Finset (Fin n)),
    ∀ ρ ∈ Bad, D (deepestEnd cs F ρ) (lab ρ) = deepestSel cs F ρ

/-- **Witnessed reconstruction ⟹ the `(Cw)^s` tight count, `hnf`-free.**  The end-state plus the witness
label determine `ρ` (`deepestEnd_inj`), and the witness label space is `(2wm)^s` (`card_witLabels_le`), so
`|Bad| ≤ |Short|·(2wm)^s` — `F`-independent, with no `hnf` hypothesis. -/
theorem deepest_count_of_witness {w s F m : ℕ} {cs : List (Clause n)}
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, deepestEnd cs F ρ ∈ Short)
    (hrec : WitnessReconstructionCorrect cs w s F m Bad) :
    Bad.card ≤ Short.card * (2 * w * m) ^ s := by
  obtain ⟨lab, D, hdec⟩ := hrec
  refine card_bad_le_label_card (deepestEnd cs F) lab
    (SwitchingCounting.card_witLabels_le w s m) hmem ?_
  intro ρ hρ σ hσ hE hlab
  have h1 : D (deepestEnd cs F ρ) (lab ρ) = D (deepestEnd cs F σ) (lab σ) := by rw [hE, hlab]
  rw [hdec ρ hρ, hdec σ hσ] at h1
  exact deepestEnd_inj cs F hE h1

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_count_of_witness
