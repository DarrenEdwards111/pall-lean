import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Decider-tied non-trivial gauge extraction (round 58)

This file packages a **5-fold conjunction** that certifies the
decider-tied non-trivial amplituhedron-gauge extraction at dimension
`n = 2`, bundling together:

1. **Non-trivial gauge witness.** The §28.3 compiled gadget
   `compiledGadget (Real.sqrt 2 − 1) 2` is an amplituhedron gauge for
   `satFamily 2` and is *not* the identity matrix. The non-identity
   property follows structurally from the off-diagonal entry
   `(0,1) = -1`, which is independent of `α`. The gauge property is
   `compiledGadget_n2_isGauge_satFamily`, which combines positive
   definiteness at `α = √2 − 1` with the two principal-minor
   computations on the family `{∅, Finset.univ}`.

2. **Tableau-indexed existence.** For every `m, n = 2` SAT decider
   tableau `T : SATDeciderTableau m 2`, there is a non-trivial gauge
   witness for `satFamily 2`. The witness is the same compiled gadget,
   but its existence is now *typed by* the tableau — making the
   extraction "decider-tied" in the variable sense (the tableau is an
   ambient hypothesis that may carry extra data downstream).

3. **Family non-emptiness.** The gauge family `satFamily 2` is
   non-empty (it contains `∅` and `Finset.univ`).

4. **Decider coupling positivity.** The decider-specific coupling
   `α = √2 − 1` is strictly positive (this is the kernel-only fact
   `sqrt_two_minus_one_pos`).

5. **Identity fallback.** The identity matrix is an amplituhedron gauge
   for *any* family `𝒥` at any dimension `n`. This guarantees a
   trivial fallback witness whenever no non-trivial extraction is
   needed.

Kernel-only: the only axioms used are `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, no custom `axiom`, no `True` placeholder, and
no upstream gauge axiom.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Decider-tied non-trivial gauge extraction (round 58).**

    A 5-fold conjunction certifying:
    1. The §28.3 compiledGadget at α=√2-1, n=2 is a non-trivial amplituhedron
       gauge for satFamily 2 (matrix ≠ identity).
    2. For every n=2 SAT decider tableau, there exists a non-trivial gauge witness
       (the same compiledGadget — independent of tableau but typed by it).
    3. The non-trivial gauge family `satFamily 2` is non-empty.
    4. The decider-specific coupling α = √2 - 1 is positive.
    5. Identity matrices gauge all families (fallback).
-/
theorem decider_tied_nontrivial_extraction :
    -- (1) Compiled gadget at √2-1, n=2 is non-trivial gauge
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (2) For every n=2 tableau, a non-trivial gauge witness exists
    (∀ (m : ℕ) (_T : SATDeciderTableau m 2),
       ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
         IsAmplituhedronGauge A (satFamily 2) ∧
         A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (3) satFamily 2 is non-empty
    ((satFamily 2).Nonempty) ∧
    -- (4) α = √2 - 1 > 0
    (0 < Real.sqrt 2 - 1) ∧
    -- (5) Identity gauges any family at any n
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨compiledGadget_n2_isGauge_satFamily,
           compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · intros m _T
    exact ⟨compiledGadget (Real.sqrt 2 - 1) 2,
           compiledGadget_n2_isGauge_satFamily,
           compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · refine ⟨∅, ?_⟩
    exact satFamily_mem_empty 2
  · exact sqrt_two_minus_one_pos
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB.Positroid
