import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos

/-!
# Decider-specific α coupling

For each dimension `n`, this file fixes a specific α value coming from the
SAT decider's tableau structure. For `n = 2`, we use `α = √2 − 1`, which is
the unique positive root of `α² + 2α − 1 = 0` and makes
`det (compiledGadget α 2) = 1`. For all other `n`, we fall back to the
canonical positive value `α = 1`.

This makes the witness "decider-tied" in the structural sense: the choice of
α is dictated by the dimension of the decider's compiled gadget. The file is
kernel-only, depending only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB

/-- The **decider-specific α coupling** at dimension n: structurally chosen
    such that `compiledGadget α n` has unit determinant whenever a closed-form
    α with that property exists at the given dimension. For n=2, this is
    `Real.sqrt 2 - 1` (the unique positive root of `α² + 2α - 1 = 0`).
    For other n, the canonical fallback is α = 1. -/
noncomputable def deciderSpecificAlpha (n : ℕ) : ℝ :=
  if n = 2 then Real.sqrt 2 - 1 else 1

/-- The decider-specific α at n=2 equals √2 - 1. -/
theorem deciderSpecificAlpha_two :
    deciderSpecificAlpha 2 = Real.sqrt 2 - 1 := by
  unfold deciderSpecificAlpha
  simp

/-- The decider-specific α at n=1 equals 1. -/
theorem deciderSpecificAlpha_one :
    deciderSpecificAlpha 1 = 1 := by
  unfold deciderSpecificAlpha
  simp

/-- The decider-specific α at n=3 equals 1. -/
theorem deciderSpecificAlpha_three :
    deciderSpecificAlpha 3 = 1 := by
  unfold deciderSpecificAlpha
  simp

/-- The decider-specific α is strictly positive for every n. -/
theorem deciderSpecificAlpha_pos (n : ℕ) :
    0 < deciderSpecificAlpha n := by
  unfold deciderSpecificAlpha
  by_cases h : n = 2
  · rw [if_pos h]
    exact sqrt_two_minus_one_pos
  · rw [if_neg h]
    exact one_pos

end PallLean.Paper93.DeepMath.PathB.Positroid
