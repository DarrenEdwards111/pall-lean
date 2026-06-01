import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPolarity

/-!
# Satisfaction is preserved under falsifying a free variable

**STATUS: REAL.  THE KEY DECODER-STABILITY FACT (cross-clause worry dispelled).**

Designing the decoder raised a worry: could falsifying the active clause's literal
*un-satisfy* an earlier clause and so change the active clause?  No — and here is
why, proved here:

* a satisfied clause has a forced-**true** literal, which lives on a **fixed**
  variable; but the step only fixes a **free** variable;
* so the witnessing literal is on a different variable and is unchanged
  (`litTrue_falFix_ne`), hence the clause stays satisfied
  (`clauseSatisfied_mono_falFix`).

So `clauseSatisfied` is monotone under `falFix` on a free variable: satisfied
clauses stay satisfied.  Together with `clauseSatisfied_falFix` (the active clause
stays unsatisfied) this is the foundation for active-clause stability — the
decoder invariant that the active clause does not move while it still has free
literals.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- A forced-true literal has its forced value `some true`. -/
theorem litFixedVal_some_of_litTrue {σ : Restriction n} {ℓ : Rung4Literal n}
    (h : Depth3.litTrue σ ℓ = true) : Depth3.litFixedVal σ ℓ = some true := by
  unfold Depth3.litTrue at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- **A forced-true literal lives on a different variable than any free literal.** -/
theorem litVar_ne_of_litTrue_litFree {σ : Restriction n} {ℓ' ℓ : Rung4Literal n}
    (ht : Depth3.litTrue σ ℓ' = true) (hf : Depth3.litFree σ ℓ = true) :
    litVar ℓ' ≠ litVar ℓ := by
  have hsome : σ (litVar ℓ') ≠ none := by
    have hfix := litFixedVal_some_of_litTrue ht
    cases ℓ' with
    | pos i => simp only [Depth3.litFixedVal, litVar] at hfix ⊢; rw [hfix]; simp
    | neg i =>
      simp only [Depth3.litFixedVal, litVar] at hfix ⊢
      intro hn; rw [hn] at hfix; simp at hfix
  have hnone : σ (litVar ℓ) = none := by
    rw [litFree_var] at hf; exact Option.isNone_iff_eq_none.mp hf
  intro hv; rw [hv] at hsome; exact hsome hnone

/-- **Satisfaction is preserved under falsifying a free variable.**  A satisfied
clause stays satisfied — its witnessing literal is on a fixed variable, unaffected
by fixing a free one. -/
theorem clauseSatisfied_mono_falFix {σ : Restriction n} {ℓ : Rung4Literal n}
    (C : Clause n) (hf : Depth3.litFree σ ℓ = true) (hsat : clauseSatisfied σ C = true) :
    clauseSatisfied (falFix σ ℓ) C = true := by
  rw [clauseSatisfied, List.any_eq_true] at hsat ⊢
  obtain ⟨ℓ', hmem, htrue⟩ := hsat
  refine ⟨ℓ', hmem, ?_⟩
  rw [litTrue_falFix_ne σ (litVar_ne_of_litTrue_litFree htrue hf)]
  exact htrue

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseSatisfied_mono_falFix
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.litVar_ne_of_litTrue_litFree
