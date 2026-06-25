import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagonalizationKernel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedHierarchyConditional

/-!
# Bit-cost time hierarchy — the measure-agnostic core (PROVED)

The EffSim time hierarchy's lower-bound half is pure diagonalisation (`diag_ne`), independent of the cost
measure.  This file abstracts the hierarchy to *any* decider enumeration `D : code → input → Bool` (which
bakes in whatever budget/measure it is built from), so it can be instantiated with a **bit-cost**-bounded
enumeration as well as the EffSim **fuel**-bounded one.

  `InTimeGen D` — the `D`-time class.
  `not_inTime_diag` — `diag D ∉ TIME(D)` (unconditional).
  `hierarchy_gen` — `TIME(Dbound) ⊊ TIME(Dbig)` from the simulator hypothesis `hsim` (any measure).
  `recovers_effsim` — instantiating `D := timedEnum` recovers the EffSim fuel hierarchy.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel (diag diag_ne)

namespace PallLean.Paper93.DeepMath.PathB.BitHierarchy

/-- `L` is in the `D`-time class: decided by some enumerated program `D e`.  `D : code → input → Bool` bakes
in whatever cost measure / budget `D` is built from — this is the **measure-agnostic** time class. -/
def InTimeGen (D : ℕ → ℕ → Bool) (L : ℕ → Bool) : Prop := ∃ e, L = D e

/-- **The diagonal is not in the `D`-time class (proved, measure-agnostic, unconditional).** -/
theorem not_inTime_diag (D : ℕ → ℕ → Bool) : ¬ InTimeGen D (diag D) := by
  rintro ⟨e, he⟩; exact diag_ne D e he

/-- **The generic time hierarchy (proved): for any two enumerations, if the bigger one computes the smaller's
diagonal, then `TIME(Dbound) ⊊ TIME(Dbig)`.**  Lower-bound half unconditional; upper-bound half is exactly the
simulator hypothesis `hsim`.  Abstracts the EffSim fuel hierarchy to *any* cost measure. -/
theorem hierarchy_gen (Dbound Dbig : ℕ → ℕ → Bool) (hsim : ∃ e₀, Dbig e₀ = diag Dbound) :
    ∃ L, InTimeGen Dbig L ∧ ¬ InTimeGen Dbound L :=
  ⟨diag Dbound, (by obtain ⟨e₀, he₀⟩ := hsim; exact ⟨e₀, he₀.symm⟩), not_inTime_diag Dbound⟩

/-- **Sanity: the generic hierarchy recovers the EffSim fuel hierarchy** (`InTime = InTimeGen ∘ timedEnum`). -/
theorem recovers_effsim (bound bigbound : ℕ → ℕ)
    (hsim : ∃ e₀, PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration.timedEnum bigbound e₀
      = diag (PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration.timedEnum bound)) :
    ∃ L, PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional.InTime bigbound L
       ∧ ¬ PallLean.Paper93.DeepMath.PathB.ACC0TimedHierarchyConditional.InTime bound L :=
  hierarchy_gen _ _ hsim

end PallLean.Paper93.DeepMath.PathB.BitHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.BitHierarchy.hierarchy_gen
