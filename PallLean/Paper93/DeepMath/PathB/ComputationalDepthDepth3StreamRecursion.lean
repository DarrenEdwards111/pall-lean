import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BadLive

/-!
# Recursive reconstruction, the central lemma — branch only

The circularity in recovering the active-clause stream is broken by one fact, already proved: a bad ρ
**falsifies nothing** (`bad_live_everywhere`).  Therefore a term's *falsification* at a descent state is
determined entirely by the queried variables, not by ρ.  A decoder maintaining a running state `τ`
(queried variables set to their `σ_end` values, everything else free) thus has the **same falsification
status as the descent state on every term**, hence the **same active term**.

This file proves that central equivalence, with no reference to ρ:

* `find?_congr` — `List.find?` respects pointwise-equal predicates.
* `activeTerm_eq_of_falsified_agree` — if `τ` and `σ` agree on the falsification of every clause and
  neither satisfies any clause, then `activeTerm cs τ = activeTerm cs σ`.  (A non-falsified clause has a
  free literal by the dichotomy, so the active predicate reduces to `¬ falsified`, and that agrees.)

This is the engine of the recursive `recoverStream`: the running state and the descent state stay
active-term-synchronised step by step.  Assembling the full `recoverStream` and its correctness on top
of this is the remaining work (the running state's falsification invariant is maintained because each
step fixes the same free variable to the same value on both sides).

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `List.find?` respects pointwise-equal predicates. -/
theorem find?_congr {α : Type*} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: t, h => by
    have ha : p a = q a := h a List.mem_cons_self
    by_cases hq : q a = true
    · rw [List.find?_cons_of_pos (ha.trans hq), List.find?_cons_of_pos hq]
    · rw [Bool.not_eq_true] at hq
      rw [List.find?_cons_of_neg (by rw [ha, hq]; simp),
          List.find?_cons_of_neg (by rw [hq]; simp)]
      exact find?_congr t (fun x hx => h x (List.mem_cons_of_mem a hx))

/-- A clause unsatisfied at a state where nothing is satisfied is not satisfied (extracted from
`anyTermSat = false`). -/
theorem termSat_false_of_anyTermSat_false {cs : List (Clause n)} {τ : Restriction n}
    (hτ : SwitchingCounting.anyTermSat cs τ = false) {U : Clause n} (hU : U ∈ cs) :
    SwitchingCounting.termSat τ U = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have : SwitchingCounting.anyTermSat cs τ = true := by
    rw [SwitchingCounting.anyTermSat, List.any_eq_true]; exact ⟨U, hU, h⟩
  rw [hτ] at this; exact absurd this (by simp)

/-- **The central recursion lemma.**  If `τ` and `σ` agree on the falsification of every clause and
neither satisfies any clause, they have the same active term — so the running decoder state and the
descent state stay active-term-synchronised. -/
theorem activeTerm_eq_of_falsified_agree {cs : List (Clause n)} {τ σ : Restriction n}
    (hfal : ∀ U ∈ cs, SwitchingCounting.termFalsified τ U = SwitchingCounting.termFalsified σ U)
    (hτ : SwitchingCounting.anyTermSat cs τ = false)
    (hσ : SwitchingCounting.anyTermSat cs σ = false) :
    SwitchingCounting.activeTerm cs τ = SwitchingCounting.activeTerm cs σ := by
  rw [SwitchingCounting.activeTerm_eq_find hτ, SwitchingCounting.activeTerm_eq_find hσ]
  apply find?_congr
  intro U hU
  show (!SwitchingCounting.termFalsified τ U && decide (0 < (SwitchingCounting.freeLits τ U).length))
     = (!SwitchingCounting.termFalsified σ U && decide (0 < (SwitchingCounting.freeLits σ U).length))
  rw [hfal U hU]
  cases hfσ : SwitchingCounting.termFalsified σ U with
  | true => simp [hfσ]
  | false =>
    have hfτ : SwitchingCounting.termFalsified τ U = false := (hfal U hU).trans hfσ
    have hsτ := termSat_false_of_anyTermSat_false hτ hU
    have hsσ := termSat_false_of_anyTermSat_false hσ hU
    simp only [Bool.not_false, Bool.true_and, decide_eq_decide]
    exact iff_of_true (List.length_pos_iff_ne_nil.mpr (has_free_of_live hfτ hsτ))
                      (List.length_pos_iff_ne_nil.mpr (has_free_of_live hfσ hsσ))

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_eq_of_falsified_agree
