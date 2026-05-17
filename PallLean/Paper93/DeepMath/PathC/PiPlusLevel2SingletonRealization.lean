import PallLean.Paper93.DeepMath.PathC.PiPlusLevel2BridgeEquivalence

/-!
# Singleton-domain Level-2 realization for Pi+

This file makes the Level-2 bridge *usable* rather than merely conditional.

Given the Route-C SAT-gauge fields for a concrete `Pi+` transform, we build a
canonical degenerate variational realization: the admissible matrix domain is
the singleton `{I}` and the selected positroid family is empty.  Then the
identity matrix is trivially a log-det/N-frame minimizer on that singleton
domain and is an amplituhedron gauge for the empty family.

This is intentionally modest: it does not prove that the paper-faithful
nondegenerate log-det problem selects `Pi+`.  It proves that the existing
Level-2 bridge hypothesis is no longer a mysterious standalone assumption — it
can be filled from the same concrete SAT-gauge fields already used by Route C.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open MultilinearSPDP

attribute [local instance] Classical.dec

/-- On the singleton admissible domain `{I}`, the identity matrix is a trivial
log-det/N-frame minimizer. -/
theorem identity_isLogDetNFrameMinimizer_singleton
    (n : Nat) :
    IsLogDetNFrameMinimizer
      (0 : ℝ) (0 : ℝ) (0 : ℝ)
      (∅ : Finset (Fin n × Fin n))
      (fun _ : Fin n => (0 : ℤ))
      (fun _ : Fin n => (0 : ℝ))
      (∅ : Finset (Finset (Fin n)))
      (fun A : Matrix (Fin n) (Fin n) ℝ => A = 1)
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨rfl, ?_⟩
  intro A hA
  rw [hA]

/-- Any SAT-gauge subgoal package is realized by the identity matrix over the
empty amplituhedron family.  The variational part is degenerate, but the
matrix-to-SAT realization fields are the real Route-C fields. -/
theorem matrixGaugeRealizesSATGauge_identity_empty_of_satDeciderGaugeSubgoals
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hsub : SATDeciderGaugeSubgoals M n hn2 htb hns gauge) :
    MatrixGaugeRealizesSATGauge M n hn hn2 htb hns
      (1 : Matrix (Fin n) (Fin n) ℝ) ∅ gauge where
  matrix_gauge := identity_isAmplituhedronGauge_empty
  rank_monotone := hsub.1
  p_side_bound := hsub.2.1
  preserves_identity_minor := hsub.2.2

/-- Concrete minimizer realization for `Pi+` from its Route-C admissibility
fields, using the singleton identity-domain variational problem. -/
def piPlusNFrameMinimizerRealization_singleton_of_admissible
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP) :
    PiPlusNFrameMinimizerRealization M n hn hn2 htb hns piP where
  alpha := 0
  beta := 0
  lambdaCoeff := 0
  E := ∅
  chi := fun _ => 0
  phi := fun _ => 0
  𝒥 := ∅
  AdmissibleMatrix := fun A => A = 1
  Astar := 1
  minimizer := identity_isLogDetNFrameMinimizer_singleton n
  realizes_piPlus_gauge :=
    matrixGaugeRealizesSATGauge_identity_empty_of_satDeciderGaugeSubgoals
      M n hn hn2 htb hns piP.gauge
      (satDeciderGaugeSubgoals_of_piPlusAdmissible
        M n hn2 htb hns piP hadm)

/-- Therefore admissibility alone fills the named Level-2 minimizer bridge via
the canonical singleton-domain variational realization. -/
def piPlusGaugeMinimizesNFrameLagrangian_singleton_of_admissible
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP) :
    PiPlusGaugeMinimizesNFrameLagrangian M n hn hn2 htb hns piP :=
  piPlusGaugeMinimizesNFrameLagrangian_of_admissible_realization
    M n hn hn2 htb hns piP hadm
    (piPlusNFrameMinimizerRealization_singleton_of_admissible
      M n hn hn2 htb hns piP hadm)

/-- Admissibility alone now yields the separated Level-2 bridge fields. -/
theorem piPlusLevel2BridgeFields_of_admissible
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hadm : PiPlusNFrameAdmissible M n hn2 htb hns piP) :
    PiPlusLevel2BridgeFields M n hn hn2 htb hns :=
  ⟨piP, hadm.block_local, hadm.rank_invariant, hadm.width_rank_p_side,
    hadm.identity_minor_preservation,
    ⟨piPlusGaugeMinimizesNFrameLagrangian_singleton_of_admissible
      M n hn hn2 htb hns piP hadm⟩⟩

/-- Uniform admissible `Pi+` data gives the uniform separated Level-2 bridge
fields. -/
def Step247UniformPiPlusAdmissible : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ∃ piP : PiPlusSATTransform M n hn2 htb hns,
      PiPlusNFrameAdmissible M n hn2 htb hns piP

/-- Uniform admissibility is enough for the full structural Level-2 bridge. -/
theorem uniformPiPlusLevel2BridgeFields_of_admissible
    (h : Step247UniformPiPlusAdmissible) :
    Step247UniformPiPlusLevel2BridgeFields := by
  intro M n hn hn2 htb hns hdec
  rcases h M n hn hn2 htb hns hdec with ⟨piP, hadm⟩
  exact piPlusLevel2BridgeFields_of_admissible
    M n hn hn2 htb hns piP hadm

/-- Thus, at the structural bridge level, uniform admissible `Pi+` data now
closes both Route B and Route C. -/
theorem routeB_routeC_equivalence_of_uniformPiPlusAdmissible
    (h : Step247UniformPiPlusAdmissible) :
    RouteBVariationalClosure ∧ RouteCFinalSocketClosure ∧
      (RouteBVariationalClosure ↔ RouteCFinalSocketClosure) :=
  routeB_routeC_equivalence_of_piPlusLevel2BridgeFields
    (uniformPiPlusLevel2BridgeFields_of_admissible h)

/-! ## Axiom audit anchors -/

#print axioms identity_isLogDetNFrameMinimizer_singleton
#print axioms matrixGaugeRealizesSATGauge_identity_empty_of_satDeciderGaugeSubgoals
#print axioms piPlusNFrameMinimizerRealization_singleton_of_admissible
#print axioms piPlusGaugeMinimizesNFrameLagrangian_singleton_of_admissible
#print axioms piPlusLevel2BridgeFields_of_admissible
#print axioms uniformPiPlusLevel2BridgeFields_of_admissible
#print axioms routeB_routeC_equivalence_of_uniformPiPlusAdmissible

end PallLean.Paper93.DeepMath.PathC
