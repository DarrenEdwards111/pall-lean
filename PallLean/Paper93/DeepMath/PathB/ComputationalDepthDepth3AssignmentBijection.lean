import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitFromUnsat

/-!
# The assignment bijection: `(Fin n → Bool)` ⟷ `(Fin n → ZMod 2)`

The circuit side (`rFalsifies`, `dualDNF`) lives over Boolean assignments `Fin n → Bool`; the Tseitin
side (`TSat`, `TConstr`) lives over `Edge → ZMod 2`.  The literal bijection `rlitToTlit` is already
proved; this file supplies the **assignment**-level transfer that carries unsatisfiability across,
completing the instantiation of `circuit_refutation_of_unsat` from a Tseitin-side unsatisfiability.

Via `boolToZMod2 : Bool → ZMod 2` (a bijection), a Boolean assignment `x` maps to `a = boolToZMod2 ∘ x`,
and:

* `litFromRLit_eval_iff` — `(litFromRLit p).eval x = true` iff `¬ TSat (boolToZMod2 ∘ x) (rlitToTlit p)`:
  the De Morgan-dual literal is true under `x` exactly when the resolution literal is *unsatisfied*
  under the corresponding `ZMod 2` assignment.
* `rFalsifies_iff_image_falsified` — `x` falsifies `C` iff every `rlitToTlit`-image literal is
  unsatisfied by `boolToZMod2 ∘ x`.
* `rFalsifies_unsat_of_tlit_unsat` — if every `ZMod 2` assignment leaves some clause's image-literals
  all unsatisfied, then every Boolean assignment falsifies some clause (`rFalsifies`-unsat).
* `circuit_refutation_of_tlit_unsat` — hence a Tseitin-side-unsatisfiable family yields the refuting
  `DTRef` of `circuit_refutation_of_unsat`.

This is the assignment-bijection instantiation: it reduces the circuit-construction's
unsatisfiability hypothesis to a statement over `ZMod 2` assignments — the form the Tseitin
constraint system speaks.  The one remaining tie (separate) is the **clause encoding**: that the
specific expander-Tseitin vertex constraints `TConstr G charge v` yield such an image-clause family
(implied by the constraints, unsatisfiable iff the parity system is) — the standard Tseitin CNF
encoding.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

namespace SearchDischarge

open Depth3

variable {n : ℕ}

/-- **Literal satisfaction transfer.**  The dual literal `litFromRLit p` is true under the Boolean
assignment `x` exactly when the resolution literal `p`, sent to `TLit` by `rlitToTlit`, is *not*
satisfied by the corresponding `ZMod 2` assignment `boolToZMod2 ∘ x`. -/
theorem litFromRLit_eval_iff (x : Fin n → Bool) (p : RLit n) :
    (litFromRLit p).eval x = true ↔ ¬ TSat (fun i => boolToZMod2 (x i)) (rlitToTlit p) := by
  obtain ⟨i, b⟩ := p
  simp only [rlitToTlit, TSat, boolToZMod2_injective.eq_iff]
  cases b <;> cases hxi : x i <;>
    simp [litFromRLit, Rung4Literal.eval, hxi]

/-- **Clause falsification transfer.**  `x` falsifies `C` iff every `rlitToTlit`-image literal of `C`
is unsatisfied by `boolToZMod2 ∘ x`. -/
theorem rFalsifies_iff_image_falsified (x : Fin n → Bool) (C : ResolutionClause (RLit n)) :
    rFalsifies x C ↔ ∀ p ∈ C, ¬ TSat (fun i => boolToZMod2 (x i)) (rlitToTlit p) := by
  constructor
  · intro hf p hp; exact (litFromRLit_eval_iff x p).mp (hf p hp)
  · intro hf p hp; exact (litFromRLit_eval_iff x p).mpr (hf p hp)

/-- **Unsatisfiability transfer.**  If every `ZMod 2` assignment `a` leaves some clause of `Ax` with
all its `rlitToTlit`-image literals unsatisfied, then every Boolean assignment falsifies some clause
— i.e. `Ax` is `rFalsifies`-unsatisfiable.  (The bijection `x ↦ boolToZMod2 ∘ x` carries one to the
other.) -/
theorem rFalsifies_unsat_of_tlit_unsat {Ax : List (ResolutionClause (RLit n))}
    (h : ∀ a : Fin n → ZMod 2, ∃ C ∈ Ax, ∀ p ∈ C, ¬ TSat a (rlitToTlit p)) :
    ∀ x : Fin n → Bool, ∃ C ∈ Ax, rFalsifies x C := by
  intro x
  obtain ⟨C, hC, hfals⟩ := h (fun i => boolToZMod2 (x i))
  exact ⟨C, hC, (rFalsifies_iff_image_falsified x C).mpr hfals⟩

/-- **Circuit refutation from Tseitin-side unsatisfiability.**  If the image clause family is
unsatisfiable over `ZMod 2` assignments, the concrete circuit `dualDNF Ax` yields a refuting `DTRef`
over `TLit (Fin n)` labeled by `tautAx (dualDNF Ax)`, of `depth ≤ fuel` — the assignment-bijection
instantiation of `circuit_refutation_of_unsat`. -/
theorem circuit_refutation_of_tlit_unsat {Ax : List (ResolutionClause (RLit n))}
    (h : ∀ a : Fin n → ZMod 2, ∃ C ∈ Ax, ∀ p ∈ C, ¬ TSat a (rlitToTlit p))
    (fuel : ℕ)
    (hfuel : SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool)) ≤ fuel) :
    ∃ T : DTRef (TLit (Fin n)),
      DTRef.Labeled (· ∈ tautAx (dualDNF Ax)) T ∧
      DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Fin n))) ∧
      T.depth ≤ fuel :=
  circuit_refutation_of_unsat (rFalsifies_unsat_of_tlit_unsat h) fuel hfuel

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.litFromRLit_eval_iff
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.rFalsifies_unsat_of_tlit_unsat
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.circuit_refutation_of_tlit_unsat
