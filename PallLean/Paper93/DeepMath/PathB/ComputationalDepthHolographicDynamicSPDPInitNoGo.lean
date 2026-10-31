import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicDynamicSPDP

/-!
# Holographic dynamic SPDP: the unrestricted-initialiser no-go

The fixed-observer construction is causal and its innovation is bounded by runtime, but the underlying
`ClockedMachine` interface has a prior modelling defect: `init : List Bool → Config` is an unrestricted Lean
function whose computational cost is not charged.  It may therefore evaluate an arbitrary language during
initialisation, store the answer, and use runtime zero.

This file formalises the resulting countermodel:

* `oracleInitMachine L` decides every language `L` in zero charged steps;
* consequently `every_language_InP` and even `PeqNP_in_model` hold in the current interface;
* every causal projected-innovation resource is zero on that decider;
* hence `holographic_SATLower_impossible` shows that no language can satisfy the required lower bound.

This does not refute holographic dynamic SPDP.  It rejects the current *machine model* as a basis for a
P-vs-NP separation.  The repair is to replace unrestricted `init` by a fixed finite machine description and a
locally charged input-loading transition system (or reuse the repository's concrete Turing/RAM semantics),
then rebuild `PUpper` and the observer theory over that model.

## Honest scope

A machine-checked no-go/correction.  No complexity-class separation is proved.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolographicDynamicSPDPInitNoGo

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant
open PallLean.Paper93.DeepMath.PathB.HolographicDynamicSPDP

/-- The free-initialiser countermodel: compute `L x` inside the uncharged `init` function. -/
def oracleInitMachine (L : List Bool → Bool) : ClockedMachine where
  Config := Bool
  init := L
  next := id
  output := id
  runtime := fun _ => 0

theorem oracleInitMachine_polyTime (L : List Bool → Bool) : IsPolyTime (oracleInitMachine L) :=
  ⟨0, 0, fun _ => Nat.zero_le _⟩

theorem oracleInitMachine_decides (L : List Bool → Bool) : Decides (oracleInitMachine L) L :=
  fun _ => rfl

/-- The present `InP` model contains every Boolean language. -/
theorem every_language_InP (L : List Bool → Bool) : InP L :=
  ⟨oracleInitMachine L, oracleInitMachine_polyTime L, oracleInitMachine_decides L⟩

/-- In the present model, `P = NP` holds trivially because every language is in `P`. -/
theorem PeqNP_in_model : PeqNP :=
  fun L _ => every_language_InP L

/-- A canonical fixed causal observer for the zero-step oracle-initialiser machine. -/
def oracleObserver (L : List Bool → Bool) : CausalObserver (oracleInitMachine L) where
  Observer := Bool
  observerFintype := inferInstance
  observerDecEq := inferInstance
  observe := id
  observedNext := id
  observedOutput := id
  step_commutes := fun _ => rfl
  output_factors := fun _ => rfl

theorem oracle_projectedInnovation_zero (L : List Bool → Bool) (x : List Bool) :
    projectedInnovation (oracleObserver L) x = 0 := by
  rfl

/-- Any observer family assigns zero projected innovation to the oracle-initialiser decider, simply because
the machine has no charged transitions. -/
theorem Rprojected_oracle_zero (F : ObserverFamily) (L : List Bool → Bool) (n : Nat) :
    Rprojected F (oracleInitMachine L) n = 0 := by
  unfold Rprojected RprojectedFor projectedInnovation
  simp [oracleInitMachine]

/-- The required holographic lower bound is impossible for every language in the present machine model. -/
theorem holographic_SATLower_impossible (F : ObserverFamily) (L : List Bool → Bool) :
    ¬ SATLower (Rprojected F) L := by
  apply polyR_decider_breaks_SATLower (Rprojected F) L (oracleInitMachine L)
  · exact oracleInitMachine_decides L
  · refine ⟨0, 0, fun n => ?_⟩
    rw [Rprojected_oracle_zero]
    exact Nat.zero_le _

end PallLean.Paper93.DeepMath.PathB.HolographicDynamicSPDPInitNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDynamicSPDPInitNoGo.every_language_InP
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDynamicSPDPInitNoGo.PeqNP_in_model
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDynamicSPDPInitNoGo.Rprojected_oracle_zero
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDynamicSPDPInitNoGo.holographic_SATLower_impossible
