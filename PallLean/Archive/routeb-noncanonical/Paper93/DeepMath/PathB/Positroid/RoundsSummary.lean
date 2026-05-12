import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Identity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.SATGaugeStructuralBarrier
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Path B + Positroid kernel-only progress, all rounds 51-55

This file bundles seven concrete kernel-only facts established across rounds
51-55 of Path B + Positroid work into a single substantive conjunction
theorem `path_B_positroid_all_rounds_kernel_only`.

The bundle records:

1. The identity matrix is an amplituhedron gauge for *any* family at any
   dimension (`identity_isAmplituhedronGauge_any`).

2. The §28.3 compiled gadget `compiledGadget α n` is positive definite
   when `α > 0` and `n ≥ 1` (`compiledGadget_posDef`).

3. The compiled gadget has full rank `n` whenever `α > 0` and `n ≥ 1`
   (`compiledGadget_rank_full`).

4. At `n = 1, α = 1`, the compiled gadget collapses to the identity
   matrix and gauges `satFamily 1`
   (`compiledGadget_one_one_is_identity`,
    `compiledGadget_one_one_isGauge_satFamily`).

5. At `n = 2, α = √2 − 1`, the compiled gadget is a *non-trivial*
   gauge for `satFamily 2`: it gauges the family but is not equal to
   the identity matrix (its off-diagonal entries are `−1`)
   (`compiledGadget_n2_isGauge_satFamily`,
    `compiledGadget_2x2_ne_identity`).

6. Structural barrier at `n ≥ 3` with `α > 0`: the literal compiled
   gadget cannot have any unit singleton minor — its diagonal entries
   are `α + (n − 1) > 1`
   (`compiledGadget_singleton_minor_obstruction`).

7. Non-trivial gauge existence at `n = 2`: there is a positive `α`
   (namely `√2 − 1`) such that the compiled gadget at that `α` is a
   non-identity gauge for `satFamily 2`.

The bundle inherits the kernel-only status of its components: only the
axioms `propext`, `Classical.choice`, `Quot.sound` are used, with no
custom axioms or upstream stubs.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Path B + Positroid kernel-only progress, all rounds.**

    Bundles seven concrete kernel-only facts established across rounds 51-55:
    (1)-(2) Identity gauges any family; compiledGadget is PosDef.
    (3) compiledGadget has full rank n.
    (4) n=1: compiledGadget collapses to identity, gauges satFamily 1.
    (5) n=2: compiledGadget (√2-1) 2 is a NON-TRIVIAL gauge for satFamily 2.
    (6) Structural barrier at n ≥ 3 with α > 0: cannot have unit singleton minors.
    (7) Non-trivial existence at n=2 from §28.3 construction. -/
theorem path_B_positroid_all_rounds_kernel_only :
    -- (1) Identity gauges any family
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    -- (2) compiledGadget α n is PosDef when α > 0, n ≥ 1
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    -- (3) compiledGadget α n has rank n when α > 0, n ≥ 1
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).rank = n) ∧
    -- (4) n=1: compiledGadget 1 1 = identity AND gauges satFamily 1
    (compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
     IsAmplituhedronGauge (compiledGadget 1 1) (satFamily 1)) ∧
    -- (5) n=2: compiledGadget (√2-1) 2 is a non-trivial gauge for satFamily 2
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (6) Structural barrier at n ≥ 3
    (∀ (n : ℕ), 3 ≤ n → ∀ (α : ℝ) (i : Fin n), 0 < α →
       compiledGadget α n i i ≠ 1) ∧
    -- (7) Existence at n=2 from §28.3
    (∃ (α : ℝ), 0 < α ∧
       IsAmplituhedronGauge (compiledGadget α 2) (satFamily 2) ∧
       compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Identity gauges any family
    exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · -- (2) compiledGadget α n is PosDef
    exact compiledGadget_posDef
  · -- (3) compiledGadget α n has rank n
    exact compiledGadget_rank_full
  · -- (4) n=1 collapse and gauge
    exact ⟨compiledGadget_one_one_is_identity,
           compiledGadget_one_one_isGauge_satFamily⟩
  · -- (5) n=2 non-trivial gauge
    exact ⟨compiledGadget_n2_isGauge_satFamily,
           compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · -- (6) Structural barrier at n ≥ 3
    intros n hn α i hα
    exact compiledGadget_singleton_minor_obstruction n hn α i hα
  · -- (7) Non-trivial existence at n=2
    exact ⟨Real.sqrt 2 - 1, sqrt_two_minus_one_pos,
           compiledGadget_n2_isGauge_satFamily,
           compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
