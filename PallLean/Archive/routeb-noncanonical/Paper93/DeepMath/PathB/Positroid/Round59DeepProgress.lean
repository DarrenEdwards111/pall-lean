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
# Round-59 deep positroid progress: kernel-only summary

This file bundles the round-59 positroid-foundational progress into a
single substantive five-fold conjunction theorem
`round_59_deep_progress`.

Compared to the round-58 bundle, round 59 strengthens the structural
catalogue of `compiledGadget` with two general (`n`-ary) clauses:

* **Non-identity at every `n ≥ 2`.** The closed-form §28.3 compiled
  gadget `compiledGadget α n = α • I + L_{K_n}` has off-diagonal entries
  equal to `−1` (independent of `α`), so it never collapses to the
  identity once `n ≥ 2`. This generalises the earlier 2×2 statement
  `compiledGadget_2x2_ne_identity` to all dimensions `n ≥ 2`, and is
  established in `CompiledGadgetNonIdentityAny.lean`.

* **Positive definiteness for any `α > 0` and any `n ≥ 1`.** Using the
  decomposition `α • I + L_{K_n}`, with `α • I` `PosDef` and the
  Laplacian `L_{K_n}` `PosSemidef`, the compiled gadget is `PosDef`
  for every strictly positive scaling and every non-empty vertex set.
  This is `compiledGadget_posDef` from `CompiledGadgetPosDef.lean`.

Together with the three round-58 anchors (identity is principal-TNN,
identity gauges any family, and the §28.3 non-trivial 2×2 gauge for
`satFamily 2`), the bundle records a five-fold structural snapshot of
the kernel-only Path B Positroid progress through round 59.

The bundle inherits the kernel-only status of its components: only the
axioms `propext`, `Classical.choice`, `Quot.sound` are used. None of
the five clauses depends on the upstream
`exists_amplituhedron_gauge_for_sat_decider` axiom or any other custom
axiom.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Round-59 deep positroid progress (kernel-only).**

    A 5-fold conjunction summarizing structural facts. None depend on the
    upstream `exists_amplituhedron_gauge_for_sat_decider` axiom. -/
theorem round_59_deep_progress :
    -- (1) Identity is principal-TNN at any n
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (2) For all n ≥ 2 and α, compiledGadget α n is non-identity
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (3) For all n ≥ 1 and α > 0, compiledGadget α n is PosDef
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    -- (4) The §28.3 compiledGadget at α=√2-1, n=2 is a non-trivial gauge for satFamily 2
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (5) Identity gauges any family
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · intros α n hn
    exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · exact ⟨compiledGadget_n2_isGauge_satFamily,
           compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB.Positroid
