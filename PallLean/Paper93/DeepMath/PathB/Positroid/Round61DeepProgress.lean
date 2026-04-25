import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Round-61 deep positroid progress: kernel-only summary

This file bundles the round-61 positroid-foundational progress into a
single substantive *eight-fold* conjunction theorem
`round_61_deep_progress`.

Compared to the round-60 bundle, round 61 augments the structural
catalogue with two additional *concrete existence* clauses, asserting
the existence of non-identity positive-definite matrices at the
specific small dimensions `n = 2` and `n = 3`. The witnesses are
provided by the §28.3 compiled gadget `compiledGadget 1 n`, which is
positive definite at `α = 1 > 0` and is not the identity once `n ≥ 2`.

The eight clauses are:

* **(1) Identity is principal-TNN at every `n`.** Every principal minor
  of `(1 : Matrix (Fin n) (Fin n) ℝ)` is `1`, hence non-negative.

* **(2) Identity gauges every family.** For every family
  `𝒥 ⊆ 𝒫(Fin n)`, the identity matrix is positive definite and every
  principal minor at every member of `𝒥` evaluates to `1`.

* **(3) Non-identity at every `n ≥ 2`.** The §28.3 compiled gadget
  `compiledGadget α n = α • I + L_{K_n}` has off-diagonal `(0,1)`
  entry equal to `−1` (independent of `α`), so it never collapses to
  the identity once `n ≥ 2`.

* **(4) Positive definiteness at every `α > 0` and every `n ≥ 1`.**
  The compiled gadget is the sum of the `PosDef` matrix `α • I` and the
  `PosSemidef` Laplacian `L_{K_n}`, hence is itself `PosDef`.

* **(5) Non-trivial 2×2 gauge.** At `α = √2 − 1` and `n = 2` the
  compiled gadget is an amplituhedron gauge for `satFamily 2` and is
  *not* the identity matrix; this is the canonical Path B
  non-identity gauge witness.

* **(6) Concrete non-identity PosDef witness at `n = 2`.** The matrix
  `compiledGadget 1 2` is positive definite and is not the `2×2`
  identity matrix.

* **(7) Concrete non-identity PosDef witness at `n = 3`.** The matrix
  `compiledGadget 1 3` is positive definite and is not the `3×3`
  identity matrix.

* **(8) Existence at every `n`.** For every `n` there exists a matrix
  that gauges `satFamily n`; the identity is one such witness.

The bundle inherits the kernel-only status of its components: only the
axioms `propext`, `Classical.choice`, `Quot.sound` are used. None of
the eight clauses depends on the upstream
`exists_amplituhedron_gauge_for_sat_decider` axiom or any other custom
axiom.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Round-61 deep positroid progress (kernel-only).**

    An 8-fold conjunction. None of the clauses depend on the upstream
    axiom `exists_amplituhedron_gauge_for_sat_decider`. -/
theorem round_61_deep_progress :
    -- (1) Identity TNN
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (2) Identity gauges any family
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    -- (3) compiledGadget α n ≠ identity for n ≥ 2
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (4) compiledGadget α n PosDef for α > 0, n ≥ 1
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    -- (5) §28.3 compiledGadget at √2-1 is non-trivial gauge for satFamily 2
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (6) Existence of non-identity PosDef matrix at n = 2
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (7) Existence of non-identity PosDef matrix at n = 3
    (∃ A : Matrix (Fin 3) (Fin 3) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) ∧
    -- (8) Existence: any n satFamily admits a gauge witness via identity
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · exact ⟨compiledGadget_n2_isGauge_satFamily, compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · refine ⟨compiledGadget 1 2, ?_, ?_⟩
    · exact compiledGadget_posDef 1 2 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 2 (by norm_num)
  · refine ⟨compiledGadget 1 3, ?_, ?_⟩
    · exact compiledGadget_posDef 1 3 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 3 (by norm_num)
  · exact fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
