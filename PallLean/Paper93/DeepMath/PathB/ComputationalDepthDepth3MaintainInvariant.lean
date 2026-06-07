import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StreamRecursion

/-!
# The maintain-invariant step of the recursive reconstruction — branch only

The recursion engine (`activeTerm_eq_of_falsified_agree`) needs the falsification-agreement invariant
`∀ U ∈ cs, termFalsified τ U = termFalsified σ U` to be **maintained** across a step.  A step fixes the
*same* free variable `v` to the *same* value `b` on both the decoder state `τ` and the descent state
`σ`.  This file proves agreement is preserved.

The mechanism: fixing `v` adds the **same** `v`-literal contribution to every clause on both sides
(`litFalse_fixVar_v` — a `v`-literal's falsity depends only on `b`, not on the rest of the state), and
because `v` was free on both sides it contributed nothing before (`litFalse_free_eq_false`).  Off `v`
the falsity is unchanged (`litFalse_fixVar_ne`).  So per clause: either some `v`-literal is newly false
(both sides falsified) or none is (both sides keep their old, agreeing, falsification).

* `maintain_one` — agreement at one clause is preserved by the step.
* `maintain_falsified_agree` — hence agreement on all of `cs` is preserved.

Combined with the engine and the base case, the running decoder state stays active-term-synchronised
with the descent state across every step — the recursion is sound.  (Assembling the concrete
`recoverStream` function and threading this invariant through its induction is the remaining packaging.)

All clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `List.any` respects pointwise-equal predicates. -/
theorem any_congr_mem {α : Type*} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | a :: t, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
        any_congr_mem t (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- A free literal is not forced false. -/
theorem litFalse_free_eq_false {ρ : Restriction n} {m : Rung4Literal n}
    (h : ρ (litVar m) = none) : SwitchingCounting.litFalse ρ m = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  exact SwitchingCounting.litFalse_litVar_fixed hc h

/-- Fixing a variable other than `m`'s leaves `m`'s falsity unchanged. -/
theorem litFalse_fixVar_ne {ρ : Restriction n} {v : Fin n} {b : Bool} {m : Rung4Literal n}
    (h : litVar m ≠ v) :
    SwitchingCounting.litFalse (fixVar ρ v b) m = SwitchingCounting.litFalse ρ m := by
  apply SwitchingCounting.litFalse_eq_of_litVar_val
  rw [fixVar, Function.update_of_ne h]

/-- A `v`-literal's falsity after fixing `v := b` is the same regardless of the rest of the state. -/
theorem litFalse_fixVar_v {τ σ : Restriction n} {v : Fin n} {b : Bool} {m : Rung4Literal n}
    (h : litVar m = v) :
    SwitchingCounting.litFalse (fixVar τ v b) m = SwitchingCounting.litFalse (fixVar σ v b) m := by
  apply SwitchingCounting.litFalse_eq_of_litVar_val
  rw [h, fixVar, fixVar, Function.update_self, Function.update_self]

/-- **Maintain-invariant at one clause.**  Fixing the same free variable `v` to the same value on both
states preserves falsification-agreement at a clause. -/
theorem maintain_one {τ σ : Restriction n} {v : Fin n} {b : Bool} {U : Clause n}
    (hτv : τ v = none) (hσv : σ v = none)
    (hagree : SwitchingCounting.termFalsified τ U = SwitchingCounting.termFalsified σ U) :
    SwitchingCounting.termFalsified (fixVar τ v b) U
      = SwitchingCounting.termFalsified (fixVar σ v b) U := by
  by_cases hvf : ∃ m ∈ U.lits, litVar m = v ∧ SwitchingCounting.litFalse (fixVar τ v b) m = true
  · obtain ⟨m, hm, hmv, hmf⟩ := hvf
    have e1 : SwitchingCounting.termFalsified (fixVar τ v b) U = true := by
      rw [SwitchingCounting.termFalsified, List.any_eq_true]; exact ⟨m, hm, hmf⟩
    have e2 : SwitchingCounting.termFalsified (fixVar σ v b) U = true := by
      rw [SwitchingCounting.termFalsified, List.any_eq_true]
      refine ⟨m, hm, ?_⟩
      rw [← litFalse_fixVar_v (τ := τ) (σ := σ) hmv]; exact hmf
    rw [e1, e2]
  · have hall : ∀ m ∈ U.lits, litVar m = v →
        SwitchingCounting.litFalse (fixVar τ v b) m = false := by
      intro m hm hmv
      by_contra h; rw [Bool.not_eq_false] at h
      exact hvf ⟨m, hm, hmv, h⟩
    have hτeq : SwitchingCounting.termFalsified (fixVar τ v b) U
        = SwitchingCounting.termFalsified τ U := by
      rw [SwitchingCounting.termFalsified, SwitchingCounting.termFalsified]
      apply any_congr_mem
      intro m hm
      by_cases hmv : litVar m = v
      · rw [hall m hm hmv, litFalse_free_eq_false (by rw [hmv]; exact hτv)]
      · exact litFalse_fixVar_ne hmv
    have hσeq : SwitchingCounting.termFalsified (fixVar σ v b) U
        = SwitchingCounting.termFalsified σ U := by
      rw [SwitchingCounting.termFalsified, SwitchingCounting.termFalsified]
      apply any_congr_mem
      intro m hm
      by_cases hmv : litVar m = v
      · have hσf : SwitchingCounting.litFalse (fixVar σ v b) m = false := by
          rw [← litFalse_fixVar_v (τ := τ) (σ := σ) hmv]; exact hall m hm hmv
        rw [hσf, litFalse_free_eq_false (by rw [hmv]; exact hσv)]
      · exact litFalse_fixVar_ne hmv
    rw [hτeq, hσeq, hagree]

/-- **Maintain-invariant on the whole formula.**  Falsification-agreement on all of `cs` is preserved
by a step fixing the same free variable to the same value on both states. -/
theorem maintain_falsified_agree {cs : List (Clause n)} {τ σ : Restriction n} {v : Fin n} {b : Bool}
    (hτv : τ v = none) (hσv : σ v = none)
    (hagree : ∀ U ∈ cs, SwitchingCounting.termFalsified τ U = SwitchingCounting.termFalsified σ U) :
    ∀ U ∈ cs, SwitchingCounting.termFalsified (fixVar τ v b) U
      = SwitchingCounting.termFalsified (fixVar σ v b) U :=
  fun U _ => maintain_one hτv hσv (hagree U ‹_›)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.maintain_falsified_agree
