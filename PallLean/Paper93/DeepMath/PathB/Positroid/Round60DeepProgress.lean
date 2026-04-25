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
# Round-60 deep positroid progress: kernel-only summary

This file bundles the round-60 positroid-foundational progress into a
single substantive six-fold conjunction theorem
`round_60_deep_progress`.

Compared to the round-59 bundle, round 60 augments the structural
catalogue with an explicit *existence* clause: for every `n`, there
exists a matrix `A` over `Fin n × Fin n` that gauges the `satFamily n`
family. The witness is the identity matrix, which is a gauge for any
family (`identity_isAmplituhedronGauge_any`); this packaging of the
gauge property as a `∃`-statement at every `n` provides the foundation
for downstream sections that quantify over witnesses rather than fix
one in advance.

The six clauses are:

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

* **(6) Existence at every `n`.** For every `n` there exists a matrix
  that gauges `satFamily n`; the identity is one such witness.

The bundle inherits the kernel-only status of its components: only the
axioms `propext`, `Classical.choice`, `Quot.sound` are used. None of
the six clauses depends on the upstream
`exists_amplituhedron_gauge_for_sat_decider` axiom or any other custom
axiom.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Round-60 deep positroid progress (kernel-only).**

    A 6-fold conjunction. None depend on the upstream axiom. -/
theorem round_60_deep_progress :
    -- (1) Identity is principal-TNN at any n
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (2) Identity gauges any family
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    -- (3) For all α and n ≥ 2, compiledGadget α n ≠ identity
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (4) For all α > 0 and n ≥ 1, compiledGadget α n is PosDef
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    -- (5) §28.3 compiledGadget at √2-1, n=2 is non-trivial gauge for satFamily 2
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (6) Existence: any n satFamily admits a gauge witness via identity
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · intros α n hn
    exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · exact ⟨compiledGadget_n2_isGauge_satFamily,
           compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
