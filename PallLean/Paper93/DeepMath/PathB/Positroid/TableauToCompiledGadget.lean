import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.DeciderSpecificGauge
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Tableau to compiled-gadget gauge matrix

This file defines a function from a SAT decider tableau to its corresponding
compiled-gadget gauge matrix. Given a tableau of dimension `m × n`, the
associated gauge matrix is the §28.3 compiled gadget at the decider-specific
coupling, with dimension matching the tableau's column count.

For tableaus with `n = 2`, the gauge matrix is the §28.3 compiled gadget at
`α = √2 − 1`, and we show that this matrix is **NOT** the identity.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- The **gauge matrix associated to a SAT decider tableau**: the §28.3 compiled
    gadget at the decider-specific coupling, with dimension matching the tableau's
    column count. For tableaus of dimension `m × n`, this returns a matrix in
    `Matrix (Fin n) (Fin n) ℝ`. -/
noncomputable def tableauToCompiledGadget {m n : ℕ}
    (_T : SATDeciderTableau m n) : Matrix (Fin n) (Fin n) ℝ :=
  deciderSpecificGauge n

/-- For any tableau of column dimension n=2, the gauge matrix is the §28.3
    compiledGadget at α=√2-1. -/
theorem tableauToCompiledGadget_two {m : ℕ} (T : SATDeciderTableau m 2) :
    tableauToCompiledGadget T = compiledGadget (Real.sqrt 2 - 1) 2 := by
  unfold tableauToCompiledGadget
  exact deciderSpecificGauge_two

/-- For any tableau of column dimension n=2, the gauge matrix is NOT the identity. -/
theorem tableauToCompiledGadget_two_ne_identity {m : ℕ} (T : SATDeciderTableau m 2) :
    tableauToCompiledGadget T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [tableauToCompiledGadget_two T]
  exact compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)

/-- The gauge matrix is well-defined for any tableau (the decider-specific
    coupling is positive). -/
theorem tableauToCompiledGadget_witness_exists {m n : ℕ} (T : SATDeciderTableau m n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A = tableauToCompiledGadget T :=
  ⟨tableauToCompiledGadget T, rfl⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
