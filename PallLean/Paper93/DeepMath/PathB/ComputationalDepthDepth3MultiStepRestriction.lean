import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3OneStepRestriction

/-!
# Iterated (`k`-step) restriction of depth-3 ΣΠΣ circuits

**STATUS: DETERMINISTIC, FULLY PROVED.  STILL NOT HÅSTAD.**

Composing the one-step restriction over a list of partial assignments.  Both
invariants of the one-step lemma carry through by induction:

* **Soundness** (`restrictList_eval`): the `k`-fold restricted circuit computes the
  original under the composed assignment — `eval (restrictList ρs D) x = eval D
  (overrideList ρs x)`.
* **Bottom width** (`restrictList_bottomWidthLe`): a bound on all bottom clause
  widths is preserved by any sequence of restrictions.

This is the deterministic scaffold a probabilistic switching argument runs on; the
probability that a *random* `ρs` collapses the circuit to a shallow object is the
remaining gate, not addressed here.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

variable {n : ℕ}

/-- The total assignment obtained by applying a sequence of restrictions in order
(then filling the still-free coordinates with `x`). -/
def overrideList : List (Fin n → Option Bool) → (Fin n → Bool) → (Fin n → Bool)
  | [], x => x
  | ρ :: ρs, x => overrideList ρs (override ρ x)

/-- Apply a sequence of restrictions to a ΣΠΣ circuit. -/
def restrictList : List (Fin n → Option Bool) → Circuit n → Circuit n
  | [], D => D
  | ρ :: ρs, D => restrictCircuit ρ (restrictList ρs D)

/-- **`k`-step soundness.**  The iterated restriction computes the original circuit
under the composed assignment. -/
theorem restrictList_eval :
    ∀ (ρs : List (Fin n → Option Bool)) (D : Circuit n) (x : Fin n → Bool),
      (restrictList ρs D).eval x = D.eval (overrideList ρs x)
  | [], _, _ => rfl
  | ρ :: ρs, D, x => by
    show (restrictCircuit ρ (restrictList ρs D)).eval x = D.eval (overrideList ρs (override ρ x))
    rw [← restrictCircuit_eval ρ x (restrictList ρs D)]
    exact restrictList_eval ρs D (override ρ x)

/-- All bottom clauses of the circuit have width `≤ w`. -/
def BottomWidthLe (D : Circuit n) (w : ℕ) : Prop :=
  ∀ T ∈ D.terms, ∀ C ∈ T.clauses, C.width ≤ w

/-- One restriction step preserves a bottom-width bound. -/
theorem restrictCircuit_bottomWidthLe {D : Circuit n} {w : ℕ}
    (ρ : Fin n → Option Bool) (h : BottomWidthLe D w) :
    BottomWidthLe (restrictCircuit ρ D) w := by
  intro T' hT' C' hC'
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
  obtain ⟨C, hC, hCeq⟩ := List.mem_filterMap.mp hC'
  have hwle : (restrictClause ρ C).elim 0 Clause.width ≤ C.width := restrictClause_width_le ρ C
  rw [hCeq] at hwle
  exact le_trans hwle (h T hT C hC)

/-- **Bottom width is preserved by any sequence of restrictions.** -/
theorem restrictList_bottomWidthLe {D : Circuit n} {w : ℕ}
    (ρs : List (Fin n → Option Bool)) (h : BottomWidthLe D w) :
    BottomWidthLe (restrictList ρs D) w := by
  induction ρs with
  | nil => exact h
  | cons ρ ρs ih => exact restrictCircuit_bottomWidthLe ρ ih

/-- Single restrictions are the length-one case of the iterated restriction. -/
theorem restrictList_singleton (ρ : Fin n → Option Bool) (D : Circuit n) :
    restrictList [ρ] D = restrictCircuit ρ D := rfl

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.restrictList_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.restrictList_bottomWidthLe
