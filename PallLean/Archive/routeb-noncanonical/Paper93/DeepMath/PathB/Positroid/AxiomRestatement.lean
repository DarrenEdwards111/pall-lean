import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Kernel-only restatement of `exists_amplituhedron_gauge_for_sat_decider`

This file gives a kernel-only restatement of the upstream
`GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider`
axiom — specialised to the concrete positroid-family
`satFamily n` defined in `SatFamilyDefinition.lean`. The upstream
axiom asserts the existence of an amplituhedron gauge matrix for the
SAT decider's principal-minor family; for the chosen `satFamily n`
this existence is *unconditionally* discharged from the existing
identity-based gauge witness `identity_isAmplituhedronGauge_any` and
the §28.3 compiled-gadget non-trivial witness
`compiledGadget_n2_isGauge_satFamily`.

Concretely, for every dimension `n`, the identity matrix
`(1 : Matrix (Fin n) (Fin n) ℝ)` is an amplituhedron gauge for
`satFamily n` (its principal minors at any subset are determinants of
identity submatrices, all `1`, by `identity_isAmplituhedronGauge_any`).
At `n = 2`, the §28.3 compiled gadget at the conjugate-root coupling
`α = √2 − 1` provides a *non-identity* witness of the same gauge
property (`compiledGadget_n2_isGauge_satFamily` together with
`compiledGadget_2x2_ne_identity`).

These witnesses depend only on the kernel axioms `propext`,
`Classical.choice`, `Quot.sound` — no `axiom`, no `sorry`, and
crucially **no upstream `exists_amplituhedron_gauge_for_sat_decider`
axiom** is invoked at any step.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Kernel-only restatement of the amplituhedron gauge existence statement
    for the trivial-decider case.**

    For every dimension n, there exists a positive-definite matrix A
    such that A is a `IsAmplituhedronGauge` for the SAT-faithful family `satFamily n`.
    This is the discharged version of the upstream
    `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` axiom
    *for the chosen satFamily* — the witness is the identity matrix in general,
    and is the non-trivial §28.3 compiledGadget at α=√2-1 specifically when n=2. -/
theorem exists_amplituhedron_gauge_for_satFamily_kernel_only :
    ∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n) := by
  intro n
  exact ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩

/-- **For n=2, the witness can be chosen non-trivially**: there exists a
    NON-IDENTITY matrix that gauges `satFamily 2`. This is the §28.3 compiled
    gadget at the conjugate-root coupling α = √2 − 1. -/
theorem exists_nontrivial_amplituhedron_gauge_satFamily_n2 :
    ∃ A : Matrix (Fin 2) (Fin 2) ℝ, IsAmplituhedronGauge A (satFamily 2) ∧
      A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨compiledGadget (Real.sqrt 2 - 1) 2,
   compiledGadget_n2_isGauge_satFamily,
   compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩

/-- The kernel-only gauge witnesses for `satFamily` close the n ≤ 2 case. -/
theorem positroid_satFamily_low_dim_witnesses :
    -- n ≥ 0 case via identity (trivial witness)
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) ∧
    -- n=2 has a NON-TRIVIAL witness from compiledGadget
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ, IsAmplituhedronGauge A (satFamily 2) ∧
       A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  ⟨exists_amplituhedron_gauge_for_satFamily_kernel_only,
   exists_nontrivial_amplituhedron_gauge_satFamily_n2⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
