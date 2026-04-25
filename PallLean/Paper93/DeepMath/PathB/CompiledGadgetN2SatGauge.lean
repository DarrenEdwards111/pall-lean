import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Explicit
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The compiled gadget at `α = √2 − 1, n = 2` is a gauge for `satFamily 2`

This file gives a **non-trivial** witness that the §28.3 compiled gadget
`compiledGadget (Real.sqrt 2 − 1) 2` satisfies the amplituhedron gauge
property `IsAmplituhedronGauge _ (satFamily 2)`. Unlike the `n = 1`
case — where `compiledGadget 1 1` collapses to the identity — here the
gauge matrix is **genuinely non-identity**: its off-diagonal entries
are `−1` (by `compiledGadget_2x2_off_diag_01`), so it is not equal to
`(1 : Matrix (Fin 2) (Fin 2) ℝ)`.

The proof chain is:

* Positive definiteness: `compiledGadget_2x2_at_sqrt2_posDef`
  (specialisation of `compiledGadget_posDef` at `α = √2 − 1 > 0`,
  `1 ≤ 2`).
* For `J = ∅ ∈ satFamily 2`: the principal minor is a `0×0`
  determinant, hence `1` by `Matrix.det_isEmpty`.
* For `J = Finset.univ ∈ satFamily 2`: the principal minor equals
  `det (compiledGadget (√2 − 1) 2)` via
  `Matrix.det_submatrix_equiv_self`, and this determinant equals
  `1` by `compiledGadget_2x2_det_at_sqrt2`, which is in turn
  `(√2 − 1) * ((√2 − 1) + 2) = (√2 − 1) * (√2 + 1) = 1` from
  the conjugate identity.

Hence the collection of (two) principal minors is entirely determined
by the closed-form §28.3 geometry, and the gauge property is discharged
without any axiom beyond `propext, Classical.choice, Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **The 2×2 compiled gadget at `α = √2 − 1` has determinant `1`.**

Inlined here because the dependency `CompiledGadget2x2DetAtSqrt2.lean`
is in flight. Direct computation: by `compiledGadget_2x2_det`,
`det (compiledGadget α 2) = α * (α + 2)`; for `α = √2 − 1` we have
`α + 2 = √2 + 1`, and `(√2 − 1) * (√2 + 1) = 1` by the conjugate
identity `sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one`. -/
theorem compiledGadget_2x2_det_at_sqrt2 :
    (compiledGadget (Real.sqrt 2 - 1) 2).det = 1 := by
  rw [compiledGadget_2x2_det]
  -- Goal: `(√2 - 1) * ((√2 - 1) + 2) = 1`.
  have h1 : (Real.sqrt 2 - 1) + 2 = Real.sqrt 2 + 1 := by ring
  rw [h1]
  -- Goal: `(√2 - 1) * (√2 + 1) = 1`.
  exact sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one

/-- **The 2×2 compiled gadget at `α = √2 − 1` is positive definite.**

Specialisation of `compiledGadget_posDef` at `α = √2 − 1 > 0`
(via `sqrt_two_minus_one_pos`) and `n = 2 ≥ 1`. -/
theorem compiledGadget_2x2_at_sqrt2_posDef :
    (compiledGadget (Real.sqrt 2 - 1) 2).PosDef :=
  compiledGadget_posDef (Real.sqrt 2 - 1) 2 sqrt_two_minus_one_pos
    (by norm_num : (1 : ℕ) ≤ 2)

/-- **The compiled gadget at `α = √2 − 1, n = 2` is an amplituhedron gauge
for `satFamily 2 = {∅, Finset.univ}`.**

Combines `compiledGadget_2x2_at_sqrt2_posDef` (positive definiteness)
with the two principal-minor computations:

* `J = ∅`: the submatrix is indexed by the empty subtype, its
  determinant is `1` by `Matrix.det_isEmpty`.
* `J = Finset.univ`: the submatrix is `compiledGadget (√2 − 1) 2`
  reindexed by the bijection
  `e.trans (Equiv.subtypeUnivEquiv Finset.mem_univ) : Fin 2 ≃ Fin 2`,
  so its determinant equals the full determinant
  `(compiledGadget (√2 − 1) 2).det = 1` by
  `Matrix.det_submatrix_equiv_self` and
  `compiledGadget_2x2_det_at_sqrt2`.

This is the non-trivial Path B gauge witness at `n = 2`: the matrix is
the actual §28.3 compiled gadget (not the identity), and it certifies
the gauge property for `satFamily 2`. -/
theorem compiledGadget_n2_isGauge_satFamily :
    IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) := by
  refine ⟨compiledGadget_2x2_at_sqrt2_posDef, ?_⟩
  intro J hJ e
  -- Membership in satFamily 2 means J = ∅ or J = Finset.univ.
  rw [satFamily_subset_iff] at hJ
  rcases hJ with hEmpty | hUniv
  · -- Case J = ∅: the submatrix is 0×0, so det = 1 by det_isEmpty.
    subst hEmpty
    -- The card of ∅ is 0, so Fin J.card = Fin 0 which is empty.
    have : IsEmpty (Fin ((∅ : Finset (Fin 2)).card)) := by
      rw [Finset.card_empty]
      exact Fin.isEmpty'
    exact Matrix.det_isEmpty
  · -- Case J = Finset.univ: submatrix det = whole det = 1.
    subst hUniv
    -- Build the bijection fun i => (e i).1 : Fin univ.card → Fin 2 as an Equiv.
    -- It is the composition of e with Equiv.subtypeUnivEquiv Finset.mem_univ.
    let u : (Finset.univ : Finset (Fin 2)) ≃ Fin 2 :=
      Equiv.subtypeUnivEquiv (fun i : Fin 2 => Finset.mem_univ i)
    let φ : Fin (Finset.univ : Finset (Fin 2)).card ≃ Fin 2 := e.trans u
    -- The underlying function of φ is exactly fun i => (e i).1.
    have hφ_apply : ∀ i, φ i = (e i).1 := by
      intro i
      rfl
    -- So the submatrix along (fun i => (e i).1) equals the submatrix along φ.
    have hsub_eq :
        (compiledGadget (Real.sqrt 2 - 1) 2).submatrix
            (fun i => (e i).1) (fun i => (e i).1)
          = (compiledGadget (Real.sqrt 2 - 1) 2).submatrix
              (fun i => φ i) (fun i => φ i) := by
      funext i j
      show compiledGadget (Real.sqrt 2 - 1) 2 ((e i).1) ((e j).1)
        = compiledGadget (Real.sqrt 2 - 1) 2 (φ i) (φ j)
      rw [hφ_apply i, hφ_apply j]
    rw [hsub_eq]
    -- Use det_submatrix_equiv_self with the equivalence φ.
    rw [Matrix.det_submatrix_equiv_self φ (compiledGadget (Real.sqrt 2 - 1) 2)]
    -- Now the goal is (compiledGadget (√2 - 1) 2).det = 1.
    exact compiledGadget_2x2_det_at_sqrt2

/-- **Existence of a non-trivial gauge witness at `n = 2`.**

There exists a strictly positive `α` (namely `α = Real.sqrt 2 − 1`) such
that `compiledGadget α 2`:

* is an amplituhedron gauge for `satFamily 2`;
* is `≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)` (the off-diagonal entries are
  `−1`, independent of `α`).

This is the strengthened existential form of the Path B gauge statement
at `n = 2`, pulling its witness from the concrete §28.3 compiled-gadget
construction rather than a posited identity. -/
theorem nontrivial_gauge_exists_n2 :
    ∃ α : ℝ, 0 < α ∧
      IsAmplituhedronGauge (compiledGadget α 2) (satFamily 2) ∧
      compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨Real.sqrt 2 - 1, sqrt_two_minus_one_pos,
          compiledGadget_n2_isGauge_satFamily, ?_⟩
  -- Show compiledGadget (√2−1) 2 ≠ 1: off-diagonal entry is −1, not 0.
  intro h_eq
  have h01 : compiledGadget (Real.sqrt 2 - 1) 2 (0 : Fin 2) (1 : Fin 2)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 2) (1 : Fin 2) := by
    rw [h_eq]
  rw [compiledGadget_2x2_off_diag_01] at h01
  rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at h01
  -- h01 : (-1 : ℝ) = 0
  linarith

end PallLean.Paper93.DeepMath.PathB
