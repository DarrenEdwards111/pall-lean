import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullReplayCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel

/-!
# Full-path re-architecture, step 4b: the reduction to stream recovery — branch only

Step 4a (`fullReplaySatPar_correct`) proved the full path **plus the active-clause stream** reconstruct
`deepestSatSeq` exactly.  This file packages the *only* remaining obligation and proves everything else
reduces to it.

* `FullPathRecoverable` — the named obligation: a label encoder `lab` together with two recovery maps
  (the **stream** `recoverStream` and the **path** `recoverPath`) that, from the leaf and `lab ρ`,
  reproduce `activeStreamPar` and `deepestFullSeq` for every bad `ρ`.
* `fullpath_deepestSatSeq_recover` — **the reduction (proved)**: `FullPathRecoverable` implies the full
  satisfy-sequence reconstruction (`∃ lab D, D (deepestEnd …) (lab ρ) = deepestSatSeq …`), by feeding
  the recovered stream and path through `fullReplaySatPar_correct`.

So the entire switching lemma now reduces, with no gaps, to the two recoveries.  `recoverPath` is the
*easy* half — the label literally encodes the full path, so it is an encode/decode round-trip (the
positions, with the `×2` satisfy/falsify bit, all fit the `(2w)^s` budget).  **`recoverStream` is the
genuine Håstad/Razborov reconstruction** (step 4b proper): recover which clause is active at each step
from `σ_end` alone.  Its real difficulty is a circularity — un-fixing a step's variable needs that
step's active clause — resolved in the literature by a canonical-tree walk.  That step is *not* done
here; this file proves it is the *sole* remaining content.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The named full-path obligation.**  A label `lab` and recovery maps for the active-clause stream
and the full path, reproducing `activeStreamPar` and `deepestFullSeq` from the leaf for every bad `ρ`. -/
def FullPathRecoverable (cs : List (Clause n)) (w s F : ℕ)
    (Bad : Finset (SwitchingCounting.Restriction n)) : Prop :=
  ∃ (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (recoverStream : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s
        → List (Clause n))
    (recoverPath : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s
        → List (ℕ × Bool)),
    ∀ ρ ∈ Bad,
      recoverStream (deepestEnd cs F ρ) (lab ρ) = activeStreamPar cs F ρ ∧
      recoverPath (deepestEnd cs F ρ) (lab ρ) = deepestFullSeq cs F ρ

/-- **The reduction (proved).**  Recovering the active-clause stream and the full path from the leaf
yields the full satisfy-sequence reconstruction — feed both through `fullReplaySatPar_correct`. -/
theorem fullpath_deepestSatSeq_recover {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (h : FullPathRecoverable cs w s F Bad) :
    ∃ (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
      (D : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s
          → List (Clause n × ℕ)),
      ∀ ρ ∈ Bad, D (deepestEnd cs F ρ) (lab ρ) = deepestSatSeq cs F ρ := by
  obtain ⟨lab, recoverStream, recoverPath, h⟩ := h
  refine ⟨lab, fun σ l => fullReplaySatPar (recoverStream σ l) (recoverPath σ l), fun ρ hρ => ?_⟩
  obtain ⟨hstream, hpath⟩ := h ρ hρ
  show fullReplaySatPar (recoverStream (deepestEnd cs F ρ) (lab ρ))
      (recoverPath (deepestEnd cs F ρ) (lab ρ)) = deepestSatSeq cs F ρ
  rw [hstream, hpath]
  exact fullReplaySatPar_correct cs F ρ

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.fullpath_deepestSatSeq_recover
