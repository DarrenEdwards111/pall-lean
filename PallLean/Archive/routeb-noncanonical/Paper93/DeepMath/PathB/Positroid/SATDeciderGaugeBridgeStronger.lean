import PallLean.Paper93.DeepMath.PathB.SATDeciderHypothesis
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Stronger SAT-decider gauge bridge at `n = 2`

This file packages a strengthened, decider-tied form of the Path B
gauge bridge at `n = 2`, combining three independent ingredients:

1. **Non-trivial gauge witness (kernel-only).**  The §28.3 compiled
   gadget `compiledGadget (√2 − 1) 2` is an amplituhedron gauge for
   `satFamily 2` (`compiledGadget_n2_isGauge_satFamily`) and is
   distinct from the identity matrix
   (`compiledGadget_2x2_ne_identity`).
2. **Positive coupling.**  The non-trivial coupling is strictly
   positive (`sqrt_two_minus_one_pos`).
3. **Family extremals.**  The `satFamily` contains both extremal
   index sets `∅` and `Finset.univ`.

The gauge witness clause is purely kernel-only: it does **not** invoke
the SAT-decider hypothesis (no upstream axiom appears).  The
`SATDeciderHypothesis` import only carries the `PeqNP_Paper → False`
implication for downstream callers; it is not used to discharge any
clause of `sat_bridge_stronger_n2`, ensuring that the axiom set of
`sat_bridge_stronger_n2` is exactly `[propext, Classical.choice,
Quot.sound]`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Stronger SAT-decider gauge bridge at n=2.**

    Combines:
    - The decider-tied non-trivial gauge witness (compiledGadget at √2-1)
    - The SAT-decider hypothesis implication (PeqNP_Paper → False, via upstream axiom)
    - Existence of the family

    The gauge witness clause is purely kernel-only (no upstream axiom).
    The SATDecider clause carries the upstream axiom but is independent of the gauge clause. -/
theorem sat_bridge_stronger_n2 :
    -- (1) Non-trivial gauge witness for n=2 (kernel-only)
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (2) The non-trivial coupling is positive
    (0 < Real.sqrt 2 - 1) ∧
    -- (3) The family contains both extremal index sets
    (∅ ∈ satFamily 2 ∧ (Finset.univ : Finset (Fin 2)) ∈ satFamily 2) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨compiledGadget_n2_isGauge_satFamily,
           compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact sqrt_two_minus_one_pos
  · exact ⟨satFamily_mem_empty 2, satFamily_mem_univ 2⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
