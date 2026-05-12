import PallLean.Paper93.DeepMath.PathB.Positroid.N3IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Closed-form gauge witness bundle for `n = 2, 3, 4`

This file packages, in a single statement, the existence of a positive
coupling `α > 0` for which the compiled gadget `compiledGadget α n` has
determinant `1` and is *not* the `n × n` identity matrix, simultaneously
for `n ∈ {2, 3, 4}`.

The three components are:

* `n = 2`: closed-form witness `α = √2 − 1`. The 2×2 determinant formula
  `α (α + 2)` (from `compiledGadget_2x2_det`) reduces the gauge equation
  `det = 1` to `(√2 − 1)(√2 + 1) = 1`, which is exactly
  `sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one`. Positivity of
  `α = √2 − 1` is `sqrt_two_minus_one_pos`.

* `n = 3`: existence-via-IVT witness from `exists_alpha_n3_det_one`,
  which produces some `α ∈ (0, 1)` with `α (α + 3)² = 1`. The 3×3
  determinant formula `α (α + 3)²` (from `compiledGadget_3x3_det`)
  converts this into the gauge equation `det = 1`.

* `n = 4`: existence-via-IVT witness from `exists_alpha_n4_det_one`,
  which produces some `α ∈ (0, 1)` with `α (α + 4)³ = 1`. The 4×4
  determinant formula `α (α + 4)³` (from `compiledGadget_4x4_det`)
  converts this into the gauge equation `det = 1`.

In each case, non-identity is supplied uniformly by
`compiledGadget_ne_identity`, which only requires `2 ≤ n`.

All results are kernel-only: the proofs use only `propext`,
`Classical.choice`, `Quot.sound`.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Closed-form gauge witness bundle for `n ∈ {2, 3, 4}`.**

For each `n ∈ {2, 3, 4}` there exists a strictly positive coupling
`α > 0` such that

* `(compiledGadget α n).det = 1` (gauge condition), and
* `compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)` (non-trivial).

The witnesses are:

* `n = 2`: `α = √2 − 1`, via the closed-form determinant
  `α (α + 2)` and the identity `(√2 − 1)(√2 + 1) = 1`.
* `n = 3`: an IVT witness `α ∈ (0, 1)` with `α (α + 3)² = 1`, combined
  with the closed-form determinant `α (α + 3)²`.
* `n = 4`: an IVT witness `α ∈ (0, 1)` with `α (α + 4)³ = 1`, combined
  with the closed-form determinant `α (α + 4)³`.

In each case the non-identity property is supplied by
`compiledGadget_ne_identity`, which uses the fact that the `(0, 1)`
off-diagonal entry is `-1 ≠ 0`. -/
theorem closed_form_gauge_bundle_n2_n3_n4 :
    -- n=2: closed form via √2-1
    (∃ α : ℝ, 0 < α ∧ (compiledGadget α 2).det = 1 ∧
      compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- n=3: IVT-α with closed-form det formula
    (∃ α : ℝ, 0 < α ∧ (compiledGadget α 3).det = 1 ∧
      compiledGadget α 3 ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    -- n=4: IVT-α with closed-form det formula
    (∃ α : ℝ, 0 < α ∧ (compiledGadget α 4).det = 1 ∧
      compiledGadget α 4 ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- n=2
    refine ⟨Real.sqrt 2 - 1, sqrt_two_minus_one_pos, ?_, ?_⟩
    · rw [compiledGadget_2x2_det]
      have h1 : Real.sqrt 2 - 1 + 2 = Real.sqrt 2 + 1 := by ring
      rw [h1]; exact sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one
    · exact compiledGadget_ne_identity (Real.sqrt 2 - 1) 2 (by norm_num)
  · -- n=3
    obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n3_det_one
    refine ⟨α, hα_pos, ?_, ?_⟩
    · rw [compiledGadget_3x3_det]; exact hα_eq
    · exact compiledGadget_ne_identity α 3 (by norm_num)
  · -- n=4
    obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n4_det_one
    refine ⟨α, hα_pos, ?_, ?_⟩
    · rw [compiledGadget_4x4_det]; exact hα_eq
    · exact compiledGadget_ne_identity α 4 (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid
