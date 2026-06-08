import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LabelBound

/-!
# Block-DT model, foundation 43: branching holography, step 4a — the encoding is injective (branch only)

The combinatorial capstone of the switching-lemma count: the encoding
`σ ↦ (descentLabels, descentFinal)` is an *injective* function.  This is the precise sense in which the
deep-path data determines the restriction — the decoder (brick 41) is its left inverse, so the map is
injective, and a counting bound on restrictions with deep paths reduces to a counting bound on the
(label-list, final-restriction) image.

* `descent_encode_injective` — for fixed `cs, w, F, x`, the map
  `σ ↦ (descentLabels cs w F σ x, descentFinal cs w F σ x)` is injective.

## Honest note on the remaining probability layer

This is the combinatorial half of step 4.  The quantitative bound `Pr_ρ[canonicalDTree.depth ≥ s] ≤
(c·w)^s` additionally requires:
  1. the *p-biased random-restriction measure* on `Fin n → Option Bool` (not yet built in this arc — every
     prior brick is measure-free / structural);
  2. bounding the label-list image to a finite set using the length bounds (brick 42:
     `flatten.length = pathLen ≥ s`, each block `≤ w`) — turning `List (List (Fin n))` into a counted space;
  3. the arithmetic converting the cardinality ratio into `(c·w)^s`.
That measure layer is a self-contained sub-project; the structural injection it stands on is complete here.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The encoding is injective.**  For a fixed descent input `x`, the map sending a restriction to its
descent labels and final restriction is injective: the decoder (`descent_decode`) is its left inverse. -/
theorem descent_encode_injective (cs : List (Clause n)) (w : ℕ) (F : ℕ) (x : Fin n → Bool) :
    Function.Injective
      (fun σ : Fin n → Option Bool => (descentLabels cs w F σ x, descentFinal cs w F σ x)) := by
  intro σ₁ σ₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hL, hf⟩ := h
  have d1 := descent_decode cs w F σ₁ x
  have d2 := descent_decode cs w F σ₂ x
  rw [hL, hf] at d1
  rw [← d1]
  exact d2

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_encode_injective
