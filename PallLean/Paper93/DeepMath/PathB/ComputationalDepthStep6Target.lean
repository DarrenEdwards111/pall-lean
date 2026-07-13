import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedCircuitCompiler

/-!
# Step (6): the target, stated precisely — and its formal height marker

This file does NOT attempt step (6).  It pins down exactly what the step-(6) statement is in the charged model,
and machine-checks its strength, so that the scope (`SCOPE_STEP6_SAT_FORCING.md`) rests on formal ground:

* `ProgPoly F` — the family `F` has a polynomial-cost charged program family;
* `Step6 F := ¬ ProgPoly F` — **the step-(6) target** for a family: no polynomial-cost program family exists.
  Note the quantifier structure: one program per input length — the model is **non-uniform**, so for an
  NP-complete family this is `SAT ∉ SIZE(poly)` strength, *stronger* than `P ≠ NP`;
* `formulaPoly_to_progPoly` — the compiler transfer: polynomial formulas give polynomial programs (cost = size,
  `ChargedCircuit.compile`);
* `step6_implies_no_poly_formulas` — **the height marker**: the step-(6) target implies a superpolynomial
  formula-size lower bound for the family.  (Programs are straight-line — circuits — so the target is at least
  circuit-lower-bound strength; the formula direction is the one the corpus's compiler makes formal.)

Together with the one-way soundness reduction of step (4) (invariant hardness ⟹ cost hardness, never the
converse), this is the machine-checked meaning of "at-least-separation-hard".  Nothing here proves, approaches,
or claims progress on the target.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Step6Target

open PallLean.Paper93.DeepMath.PathB.ChargedGate
open PallLean.Paper93.DeepMath.PathB.ChargedCircuit

/-- A Boolean function family (one function per input length). -/
def Family : Type := (n : ℕ) → (Fin n → Bool) → Bool

/-- The family has a polynomial-cost charged program family (non-uniform: one program per length). -/
def ProgPoly (F : Family) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ (w : ℕ) (P : Prog n w), (∀ z, P.run z = F n z) ∧ P.cost ≤ n ^ c + c

/-- The family has a polynomial-size formula family. -/
def FormulaPoly (F : Family) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ f : BForm n, (∀ z, f.eval z = F n z) ∧ f.size ≤ n ^ c + c

/-- **The step-(6) target** for a family: no polynomial-cost charged program family.  For an NP-complete family
this is `∉ SIZE(poly)` strength (non-uniform), strictly stronger than `P ≠ NP`. -/
def Step6 (F : Family) : Prop := ¬ ProgPoly F

/-- The compiler transfer: polynomial formulas compile to polynomial programs (cost = size). -/
theorem formulaPoly_to_progPoly (F : Family) : FormulaPoly F → ProgPoly F := by
  rintro ⟨c, hc⟩
  refine ⟨c, fun n => ?_⟩
  obtain ⟨f, hf, hsz⟩ := hc n
  exact ⟨stackS f, f.compile, fun z => by rw [compile_correct, hf],
    by rw [compile_cost]; exact hsz⟩

/-- **The height marker.**  The step-(6) target implies a superpolynomial formula-size lower bound for the
family — machine-checked meaning of "at-least-separation-hard". -/
theorem step6_implies_no_poly_formulas (F : Family) : Step6 F → ¬ FormulaPoly F :=
  fun h hf => h (formulaPoly_to_progPoly F hf)

end PallLean.Paper93.DeepMath.PathB.Step6Target

#print axioms PallLean.Paper93.DeepMath.PathB.Step6Target.step6_implies_no_poly_formulas
