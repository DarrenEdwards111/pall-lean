import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEntanglementThreeArchitectureClass
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPInteractiveCoupling

/-!
# A fourth restricted entanglement architecture: interactive SAT protocols

The one-cut observer class sees only a prefix state before the suffix arrives.
This file adds a more adaptive architecture: a deterministic two-way protocol
whose complete transcript may depend on both halves of an input.  Transcript
classes satisfy the rectangle law, and the machine's actual answers on the
ordinary `equalityCNF` family must be the protocol outputs.

If the total number of transcripts is polynomial, the concrete equality-CNF
fooling theorem gives a contradiction: SAT correctness forces at least `2^n`
transcripts, while elementary growth supplies a scale where that exceeds the
claimed polynomial bound.

This is a genuine interactive-communication lower bound, but not a time lower
bound.  General polynomial-time machines can communicate or retain linearly
many bits on this easy family, yielding exponentially many possible complete
transcripts without using exponential time.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPRestrictedDynamicTraceInvariant
open PallLean.Paper93.DeepMath.PathB.PvsNPSATBoundaryFoolingWidthLB
open PallLean.Paper93.DeepMath.PathB.PvsNPInteractiveCoupling
open PallLean.Paper93.DeepMath.PathB.ResidualInvariantNoGo
open PallLean.Paper93.DeepMath.PathB.EntanglementRestrictedLiftBarrier
open PallLean.Paper93.DeepMath.PathB.EntanglementExpandedRestrictedClass
open PallLean.Paper93.DeepMath.PathB.EntanglementThreeArchitectureClass

/-! ## Machine-linked interactive factorization -/

/-- A machine architecture whose actual decisions on equality-CNF instances
factor through a rectangle-faithful interactive protocol with polynomially
many complete transcripts. -/
structure PolynomialInteractiveEqualityFactorization
    (U : MachineModel) (D : DecisionMachine U) where
  constant : Nat
  degree : Nat
  protocol : forall n : Nat, CommProtocol n n
  agrees : forall (n : Nat) (a b : Fin n -> Bool),
    (protocol n).eval a b = U.decisionRun D.code (equalityCNF a b)
  transcripts_le : forall n : Nat,
    @Fintype.card (protocol n).Transcript (protocol n).fintype <=
      constant * (n + 1) ^ degree

/-- The restricted class of polynomial-total-transcript interactive machines. -/
def PolynomialInteractiveEqualityClass (U : MachineModel) : SolverClass U :=
  fun D => Nonempty (PolynomialInteractiveEqualityFactorization U D)

/-- The equality-CNF communication fooling set excludes correct SAT deciders
from the polynomial-total-transcript interactive class. -/
theorem no_SATDecisionInClass_polynomialInteractiveEquality
    (U : MachineModel) :
    ¬ SATDecisionInClass (PolynomialInteractiveEqualityClass U) := by
  rintro ⟨D, ⟨hfactor⟩, hsat⟩
  obtain ⟨n, hn⟩ := exists_lt_two_pow hfactor.constant hfactor.degree
  let P := hfactor.protocol n
  have hcorrect : forall a b,
      P.eval a b = true <-> Satisfiable (equalityCNF a b) := by
    intro a b
    rw [hfactor.agrees n a b]
    exact hsat (equalityCNF a b)
  have hlower : 2 ^ n <= @Fintype.card P.Transcript P.fintype :=
    equalitySAT_interactive_lower_bound n P hcorrect
  have hupper : @Fintype.card P.Transcript P.fintype <=
      hfactor.constant * (n + 1) ^ hfactor.degree := by
    exact hfactor.transcripts_le n
  omega

/-! ## Four-architecture union -/

/-- Add polynomial-total-transcript interactive protocols to the previous
three restricted architectures. -/
def FourArchitectureEntanglementClass
    (U : MachineModel) (p m d lower : Nat) : SolverClass U :=
  SolverClassUnion
    (ThreeArchitectureEntanglementClass U p m d lower)
    (PolynomialInteractiveEqualityClass U)

theorem threeArchitecture_subset_fourArchitecture
    (U : MachineModel) (p m d lower : Nat) :
    forall D, ThreeArchitectureEntanglementClass U p m d lower D ->
      FourArchitectureEntanglementClass U p m d lower D :=
  fun _ h => Or.inl h

theorem polynomialInteractive_subset_fourArchitecture
    (U : MachineModel) (p m d lower : Nat) :
    forall D, PolynomialInteractiveEqualityClass U D ->
      FourArchitectureEntanglementClass U p m d lower D :=
  fun _ h => Or.inr h

/-- Four class-specific capstones exclude correct SAT deciders from the union. -/
theorem no_SATDecisionInClass_fourArchitecture
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    ¬ SATDecisionInClass
      (FourArchitectureEntanglementClass U p m d lower) :=
  no_SATDecisionInClass_union
    (no_SATDecisionInClass_threeArchitecture
      U p m t d lower hp2 ht1 hpt hlow hm)
    (no_SATDecisionInClass_polynomialInteractiveEquality U)

/-- The four-model lower bound yields its restricted dynamic-trace interface. -/
theorem fourArchitecture_restrictedInvariant_inhabited
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (DynamicTraceInvariantForClass U
      (FourArchitectureEntanglementClass U p m d lower)) :=
  (dynamicTraceInvariantForClass_iff_no_SATDecisionInClass).2
    (no_SATDecisionInClass_fourArchitecture
      U p m t d lower hp2 ht1 hpt hlow hm)

/-- An unrestricted promotion of the four-model invariant remains exactly the
full SAT lower bound. -/
theorem fourArchitectureLift_iff_no_SATDecisionInP
    (U : MachineModel) (p m t d lower : Nat)
    [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (ht1 : 1 <= t) (hpt : 1 <= (p - 1) * t)
    (hlow : 4 * lower <= p ^ t)
    (hm : 8 * (((p - 1) * t) ^ (d + 1)) ^ 2 <= m) :
    Nonempty (RestrictedToAllDynamicEntanglementLift U
      (FourArchitectureEntanglementClass U p m d lower)) <->
      ¬ SATDecisionInP U :=
  restrictedEntanglementLift_iff_no_SATDecisionInP
    (fourArchitecture_restrictedInvariant_inhabited
      U p m t d lower hp2 ht1 hpt hlow hm)

end PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass.no_SATDecisionInClass_polynomialInteractiveEquality
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass.no_SATDecisionInClass_fourArchitecture
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass.fourArchitecture_restrictedInvariant_inhabited
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementInteractiveProtocolClass.fourArchitectureLift_iff_no_SATDecisionInP
