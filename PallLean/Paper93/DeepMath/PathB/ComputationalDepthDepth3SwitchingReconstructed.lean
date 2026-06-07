import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecoverStreamCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullPathRecover

/-!
# The depth-3 switching reconstruction, completed — branch only

Combining the two proved halves:

* `recoverStream_correct` — the active-clause stream is recovered from the leaf and the recorded
  positions (legal data only, no ρ);
* `fullReplaySatPar_correct` — the full path together with that stream reconstructs `deepestSatSeq`.

gives the keystone: **`deepestSatSeq` is a function of the leaf `deepestEnd cs F ρ` and the full path
`deepestFullSeq cs F ρ` alone** — recovered by legal-data decoders, with no reference to `ρ`.

* `deepestSatSeq_reconstructed` — the explicit reconstruction equation.
* `fullPathRecoverable_of_encoder` — discharges `FullPathRecoverable` for any label encoder that
  round-trips the full path and its positions (the remaining `(2w)^s` *count* packaging is exactly
  building such an encoder + the cardinality bound; the *reconstruction* obligation is now closed).

This is the genuine Razborov reconstruction the whole arc was reducing to: the circularity is dissolved
(a bad ρ falsifies nothing, so the leaf carries everything), and `deepestSatSeq` — hence ρ, via
`freeOn_deepestEnd` — is recovered.  Clean axioms, no `sorry`.  `Depth3CollapseModel.collapse` and
P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The reconstruction equation.**  For a bad ρ, `deepestSatSeq` is reconstructed from the leaf and
the full path by the legal-data decoders `recoverStream` (active-clause stream) and `fullReplaySatPar`
(satisfy sequence). -/
theorem deepestSatSeq_reconstructed (cs : List (Clause n)) (F : ℕ) (ρ : Fin n → Option Bool)
    (hnf : ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    fullReplaySatPar
        (recoverStream cs (deepestEnd cs F ρ) ((deepestFullSeq cs F ρ).map Prod.fst)
          (fun _ => none))
        (deepestFullSeq cs F ρ)
      = deepestSatSeq cs F ρ := by
  rw [recoverStream_correct cs F ρ hnf hleaf, fullReplaySatPar_correct]

/-- **Reconstruction obligation discharged, modulo the encoder.**  Given a label encoder `lab` that
round-trips both the full path `deepestFullSeq` and its positions from the leaf, the full
satisfy-sequence reconstruction holds — by composing the two recovery decoders.  Building such a `lab`
into the tight `(2w)^s` type (plus the cardinality bound) is the remaining *count* step; the
*reconstruction* is closed here. -/
theorem fullPathRecoverable_of_encoder {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (decodePath : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s
        → List (ℕ × Bool))
    (decodePos : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s → List ℕ)
    (hnf : ∀ ρ ∈ Bad, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ ∈ Bad, SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpath : ∀ ρ ∈ Bad, decodePath (deepestEnd cs F ρ) (lab ρ) = deepestFullSeq cs F ρ)
    (hpos : ∀ ρ ∈ Bad,
      decodePos (deepestEnd cs F ρ) (lab ρ) = (deepestFullSeq cs F ρ).map Prod.fst) :
    ∃ (lab' : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
      (D : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s
          → List (Clause n × ℕ)),
      ∀ ρ ∈ Bad, D (deepestEnd cs F ρ) (lab' ρ) = deepestSatSeq cs F ρ := by
  refine ⟨lab, fun σ l => fullReplaySatPar (recoverStream cs σ (decodePos σ l) (fun _ => none))
    (decodePath σ l), fun ρ hρ => ?_⟩
  show fullReplaySatPar
      (recoverStream cs (deepestEnd cs F ρ) (decodePos (deepestEnd cs F ρ) (lab ρ)) (fun _ => none))
      (decodePath (deepestEnd cs F ρ) (lab ρ)) = deepestSatSeq cs F ρ
  rw [hpath ρ hρ, hpos ρ hρ]
  exact deepestSatSeq_reconstructed cs F ρ (hnf ρ hρ) (hleaf ρ hρ)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSeq_reconstructed
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.fullPathRecoverable_of_encoder
