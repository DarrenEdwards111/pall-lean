import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullReplayCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BadLive

/-!
# `recoverStream` base, on the target `activeStreamPar` — branch only

The foothold (`activeTerm_eq_head_of_bad`) recovered the first active clause circularity-free.  Here we
pin that to the actual reconstruction target, the per-step active stream:

* `activeStreamPar_head` — the head of `activeStreamPar` is exactly the active term `activeTerm cs σ`
  (the descent records the active clause first; `activeTerm_pred` rules out the no-free-literal case).
* `activeStreamPar_head_of_bad` — therefore, for a bad ρ, the first element of the stream a correct
  `recoverStream` must output is `cs.head?` — recovered with **no reference to the leaf**.

So the base of `recoverStream` is fixed on the target sequence itself.  The recursion — the *next*
element, once queries have changed the running state — is the irreducible switching-lemma circularity.

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The head of the per-step active stream is the active term. -/
theorem activeStreamPar_head (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool) :
    (activeStreamPar cs (F + 1) σ).head? = SwitchingCounting.activeTerm cs σ := by
  cases hany : SwitchingCounting.anyTermSat cs σ with
  | true => simp [activeStreamPar, SwitchingCounting.activeTerm, hany]
  | false =>
    rw [activeStreamPar]
    cases hact : SwitchingCounting.activeTerm cs σ with
    | none => simp [hany, hact]
    | some T =>
      have hfree : 0 < (SwitchingCounting.freeLits σ T).length :=
        (SwitchingCounting.activeTerm_pred hact).2
      cases hh : (SwitchingCounting.freeLits σ T).head? with
      | none =>
        rw [List.head?_eq_none_iff] at hh
        rw [hh] at hfree; simp at hfree
      | some ℓ =>
        simp only [hany, Bool.false_eq_true, if_false, hact, hh]
        split <;> rfl

/-- For a bad ρ, the first element of the stream that `recoverStream` must output is `cs.head?` —
recovered with no reference to the leaf. -/
theorem activeStreamPar_head_of_bad {cs : List (Clause n)} {F : ℕ} {ρ : Fin n → Option Bool}
    (hnf : ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (hleaf : SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false) :
    (activeStreamPar cs (F + 1) ρ).head? = cs.head? := by
  rw [activeStreamPar_head, activeTerm_eq_head_of_bad hnf hleaf]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeStreamPar_head_of_bad
