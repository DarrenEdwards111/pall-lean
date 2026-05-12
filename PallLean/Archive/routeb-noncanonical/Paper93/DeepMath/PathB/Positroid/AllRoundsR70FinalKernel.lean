import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerRelation2x4
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Identity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Round-70 Final Kernel Theorem

This file bundles the round-70 final kernel theorem, extending the
round-69 conjunction with two new closed-form determinant results at
`n = 5` and `n = 6`:

* `(compiledGadget α 5).det = α * (α + 5)^4` (via
  `compiledGadget_5x5_det`).
* `(compiledGadget α 6).det = α * (α + 6)^5` (via
  `compiledGadget_6x6_det`).

These extend the closed-form pattern `det(α • I + L_{K_n}) = α (α + n)^{n−1}`
of the Path B compiled gadget through `n = 6`, complementing the
existing `n = 2`, `n = 3`, `n = 4` instances.

The conjunction shape mirrors `AllRoundsR69FinalKernel.lean` and adds
the two new determinant conjuncts as the round-70 increment.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Round-70 Final Kernel Theorem.**

Bundles the round-69 conjunction with the two new round-70 closed-form
determinant results at `n = 5` and `n = 6`. The new conjuncts are:

* `(compiledGadget α 5).det = α * (α + 5)^4` for every `α : ℝ`,
* `(compiledGadget α 6).det = α * (α + 6)^5` for every `α : ℝ`.

These complete the closed-form determinant pattern through `n = 6` for
the Path B compiled gadget `α • I + L_{K_n}`. -/
theorem all_rounds_r70_final_kernel :
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    (∀ a b c d e f g h : ℝ,
       (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f) + (a*h - d*e) * (b*g - c*f) = 0) ∧
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → 0 < (compiledGadget α n).det) ∧
    (compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2)) ∧
    (compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) ∧
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) ∧
    -- Cumulative breadth: n=2..100
    (∀ n : ℕ, 2 ≤ n → n ≤ 100 →
       ∃ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- Round-69 increment: explicit n=11 PosDef witness via compiledGadget 1 11
    (compiledGadget 1 11).PosDef ∧
    -- Round-70 increment: closed-form det at n=5
    (∀ α : ℝ, (compiledGadget α 5).det = α * (α + 5)^4) ∧
    -- Round-70 increment: closed-form det at n=6
    (∀ α : ℝ, (compiledGadget α 6).det = α * (α + 6)^5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · exact plucker_relation_2x4
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · intros α n hα hn; exact Matrix.PosDef.det_pos (compiledGadget_posDef α n hα hn)
  · exact compiledGadget_one_one_is_identity
  · exact compiledGadget_n2_isGauge_satFamily
  · exact compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)
  · exact compiledGadget_2x2_det
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det
  · exact fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩
  · intros n hn _
    exact ⟨compiledGadget 1 n, compiledGadget_posDef 1 n one_pos (by omega),
           compiledGadget_ne_identity 1 n hn⟩
  · exact compiledGadget_posDef 1 11 one_pos (by norm_num)
  · exact compiledGadget_5x5_det
  · exact compiledGadget_6x6_det

end PallLean.Paper93.DeepMath.PathB.Positroid
