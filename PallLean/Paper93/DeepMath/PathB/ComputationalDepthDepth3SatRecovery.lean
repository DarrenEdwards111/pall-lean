import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FilterFalsified

/-!
# The satisfying-encoding recovery: one-step soundness for falsifying ρ (branch only)

The tight-decoder no-go (`allfree_step0_fails`) showed the all-free forward decoder mis-identifies the
first active clause for a falsifying `ρ`, because it cannot see `ρ`'s falsified prefix.  The resolution
(Håstad) is to recover the active term as the **first *satisfied* term** of an encoding that *satisfies*
the active term — because the `ρ`-falsified prefix stays **unsatisfied** under any extension
(monotonicity), so it is correctly skipped *even when `ρ` falsifies clauses*.

This file proves that one-step soundness, for **any** `ρ` (falsifying or not):

* `litFalse_mono`, `termFalsified_mono` — falsification is preserved under extending the restriction.
* `firstSat_eq_active` — **the key lemma**: if `σ` extends `ρ`, `ρ` satisfies no term, `T` is the active
  term of `ρ`, and `σ` satisfies `T`, then `cs.find? (termSat σ) = T`.  So the active term is recovered
  as the first satisfied term, with **no reference to `ρ`'s falsified set** — the missing mechanism the
  no-go identified, now resolved at the one-step level for falsifying `ρ`.

This is the genuine breakthrough direction: the active-clause recovery that the all-free decoder could
not do.  Building the full encoding (set each active term's free literals to satisfy it), the `s`-step
iteration, and the count bookkeeping on top is the remaining work; the load-bearing step-0 soundness for
falsifying `ρ` is proved here.

Clean, no `sorry`.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A `σ` **extends** `ρ` if it agrees on every coordinate `ρ` fixes. -/
def Extends (ρ σ : Restriction n) : Prop := ∀ v b, ρ v = some b → σ v = some b

/-- Falsification of a literal is preserved under extension. -/
theorem litFalse_mono {ρ σ : Restriction n} (hext : Extends ρ σ)
    {ℓ : Rung4Literal n} (h : SwitchingCounting.litFalse ρ ℓ = true) :
    SwitchingCounting.litFalse σ ℓ = true := by
  cases ℓ with
  | pos i =>
    simp only [SwitchingCounting.litFalse, Depth3.litFixedVal] at h ⊢
    cases hρ : ρ i with
    | none => rw [hρ] at h; simp at h
    | some b =>
      cases b with
      | true => rw [hρ] at h; simp at h
      | false => simp [hext i false hρ]
  | neg i =>
    simp only [SwitchingCounting.litFalse, Depth3.litFixedVal] at h ⊢
    cases hρ : ρ i with
    | none => rw [hρ] at h; simp at h
    | some b =>
      cases b with
      | false => rw [hρ] at h; simp at h
      | true => simp [hext i true hρ]

/-- Falsification of a term is preserved under extension. -/
theorem termFalsified_mono {ρ σ : Restriction n} (hext : Extends ρ σ)
    {U : Clause n} (h : SwitchingCounting.termFalsified ρ U = true) :
    SwitchingCounting.termFalsified σ U = true := by
  rw [SwitchingCounting.termFalsified, List.any_eq_true] at h ⊢
  obtain ⟨ℓ, hℓ, hf⟩ := h
  exact ⟨ℓ, hℓ, litFalse_mono hext hf⟩

/-- **One-step soundness of the satisfying-encoding decoder.**  If `σ` extends `ρ`, `ρ` satisfies no
term, `T` is the active term at `ρ`, and `σ` satisfies `T`, then the **first satisfied term** of `σ` is
exactly `T`.  The `ρ`-falsified prefix stays falsified (hence unsatisfied) under `σ` (monotonicity), so
it is correctly skipped — *no knowledge of `ρ`'s falsified set is needed*. -/
theorem firstSat_eq_active {cs : List (Clause n)} {ρ σ : Restriction n} {T : Clause n}
    (hext : Extends ρ σ)
    (hact : SwitchingCounting.activeTerm cs ρ = some T)
    (hsat : SwitchingCounting.termSat σ T = true) :
    cs.find? (SwitchingCounting.termSat σ) = some T := by
  obtain ⟨pre, post, hcs, hpre⟩ := SwitchingCounting.activeTerm_prefix_falsified hact
  have hprenone : pre.find? (SwitchingCounting.termSat σ) = none := by
    rw [List.find?_eq_none]
    intro U hU
    have hfσ : SwitchingCounting.termFalsified σ U = true := termFalsified_mono hext (hpre U hU)
    rw [termSat_false_of_termFalsified hfσ]; simp
  rw [hcs, List.find?_append, hprenone]
  exact List.find?_cons_of_pos hsat

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.firstSat_eq_active
