import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementExpandedRestrictedClass
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSATBoundaryFoolingWidthLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResidualInvariantNoGo

/-!
# A third restricted entanglement architecture: polynomial one-cut SAT observers

The previous restricted union contains small `AC0[p]` parity-family realizations
and fixed bounded-MERA independent-query realizations.  This file adds a third,
structurally different solver architecture backed by the repository's genuine
equality-CNF fooling lower bound.

A `PolynomialOneCutEqualityFactorization` says that one decision machine's
answers on the ordinary formulas `equalityCNF a b` factor through a fixed-order
left-to-right boundary observer with only polynomially many states.  The
factorization is tied to the machine's actual `decisionRun`; it is not an
independently appended sheet.  If the machine decided SAT, the equality-CNF
semantics would force `2^n` states at every width, contradicting the polynomial
state bound at a sufficiently large `n`.

This gives a real third restricted lower bound.  It still does not claim that
arbitrary polynomial-time machines have such a one-cut factorization: a
linear-time equality scan already explains why that claim would be false.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier
open PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass
open PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo

/-! ## Machine-linked polynomial one-cut factorization -/

/-- A machine architecture whose actual answers on the equality-CNF family
factor through polynomially many one-way boundary states. -/
structure PolynomialOneCutEqualityFactorization
    (U : MachineModel) (D : DecisionMachine U) where
  constant : Nat
  degree : Nat
  boundary : forall n : Nat, LayeredBoundaryDecider n n
  agrees : forall (n : Nat) (a b : Fin n -> Bool),
    (boundary n).eval a b = U.decisionRun D.code (equalityCNF a b)
  states_le : forall n : Nat,
    @Fintype.card (boundary n).State (boundary n).fintype <=
      constant * (n + 1) ^ degree

/-- The corresponding restricted solver class. -/
def PolynomialOneCutEqualityClass (U : MachineModel) : SolverClass U :=
  fun D => Nonempty (PolynomialOneCutEqualityFactorization U D)

/-- No SAT decider can have a polynomial-state one-cut factorization on the
concrete equality-CNF family. -/
theorem no_SATDecisionInClass_polynomialOneCutEquality
    (U : MachineModel) :
    ¬ SATDecisionInClass (PolynomialOneCutEqualityClass U) := by
  rintro ⟨D, ⟨hfactor⟩, hsat⟩
  obtain ⟨n, hn⟩ := exists_lt_two_pow hfactor.constant hfactor.degree
  let B := hfactor.boundary n
  have hcorrect : ComputesEqualitySAT B := by
    intro a b
    rw [hfactor.agrees n a b]
    exact hsat (equalityCNF a b)
  have hlower : 2 ^ n <= @Fintype.card B.State B.fintype :=
    card_ge_two_pow_of_computes_equalitySAT n B hcorrect
  have hupper : @Fintype.card B.State B.fintype <=
      hfactor.constant * (n + 1) ^ hfactor.degree := by
    exact hfactor.states_le n
  omega

/-! ## Three-architecture union -/

/-- The previous two-model class enlarged by polynomial one-cut equality
factorizations. -/
def ThreeArchitectureEntanglementClass
    (U : MachineModel) (p m d lower : Nat) : SolverClass U :=
  SolverClassUnion
    (ExpandedEntanglementClass U p m d lower)
    (PolynomialOneCutEqualityClass U)

theorem expanded_subset_threeArchitecture
    (U : MachineModel) (p m d lower : Nat) :
    forall D, ExpandedEntanglementClass U p m d lower D ->
      ThreeArchitectureEntanglementClass U p m d lower D :=
  fun _ h => Or.inl h

theorem polynomialOneCut_subset_threeArchitecture
    (U : MachineModel) (p m d lower : Nat) :
    forall D, PolynomialOneCutEqualityClass U D ->
      ThreeArchitectureEntanglementClass U p m d lower D :=
  fun _ h => Or.inr h

/-- Three independent capstones exclude SAT deciders from the enlarged union:
Razborov--Smolensky, bounded dynamic MERA, and equality-CNF one-cut width. -/
theorem no_SATDecisionInClass_threeArchitecture
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    ¬ SATDecisionInClass
      (ThreeArchitectureEntanglementClass U p m d lower) :=
  no_SATDecisionInClass_union
    (no_SATDecisionInClass_expandedEntanglement
      U p m t d lower hp2 ht1 hpt hlow hm)
    (no_SATDecisionInClass_polynomialOneCutEquality U)

/-- The real three-model lower bound yields the downstream restricted dynamic
trace interface. -/
theorem threeArchitecture_restrictedInvariant_inhabited
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (DynamicTraceInvariantForClass U
      (ThreeArchitectureEntanglementClass U p m d lower)) :=
  (dynamicTraceInvariantForClass_iff_no_SATDecisionInClass).2
    (no_SATDecisionInClass_threeArchitecture
      U p m t d lower hp2 ht1 hpt hlow hm)

/-- Promoting even this three-model union to all polynomial machines remains
exactly equivalent to the unrestricted SAT lower bound. -/
theorem threeArchitectureLift_iff_no_SATDecisionInP
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (RestrictedToAllDynamicEntanglementLift U
      (ThreeArchitectureEntanglementClass U p m d lower)) <->
      ¬ SATDecisionInP U :=
  restrictedEntanglementLift_iff_no_SATDecisionInP
    (threeArchitecture_restrictedInvariant_inhabited
      U p m t d lower hp2 ht1 hpt hlow hm)

end PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass.no_SATDecisionInClass_polynomialOneCutEquality
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass.no_SATDecisionInClass_threeArchitecture
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass.threeArchitecture_restrictedInvariant_inhabited
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass.threeArchitectureLift_iff_no_SATDecisionInP
