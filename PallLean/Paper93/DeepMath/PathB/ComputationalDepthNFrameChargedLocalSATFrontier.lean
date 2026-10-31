import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalMachineRepair
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmit

/-!
# The concrete SAT frontier in the charged local machine model

The repaired model is now non-vacuous, but it still needs a concrete language.
This file uses the repository's proved self-delimiting Cook–Levin formula codec
`encodeFormula` / `decodeFormula`.  The codec round trip is exact and its
output-length bounds are already proved in `ComputationalDepthCookLevinEmit`.

We define the Boolean language whose inputs are bit-encoded CNFs and whose
value is their semantic satisfiability.  The canonical encoding of every
formula has exactly the correct language value.  The language is nonconstant,
so the repaired local model cannot decide it with zero transitions.

Finally we state and prove the exact frontier: saying that every correct local
SAT decider has a non-polynomial clock is equivalent to saying this encoded
SAT language is not in `ComposableMachine.InP`.  This is a calibration, not a
lower bound; either side is the genuine P-vs-NP-strength obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalMachineRepair

/-! ## A faithful bit-encoded SAT language -/

/-- SAT truth for the formula decoded from a self-delimiting bitstring.  The
noncomputable definition specifies the semantic language; membership in the
local machine class is the computational question. -/
noncomputable def encodedSATLanguage (bits : List Bool) : Bool :=
  by
    classical
    exact if Satisfiable (decodeFormula bits) then true else false

@[simp] theorem encodedSATLanguage_eq_true_iff (bits : List Bool) :
    encodedSATLanguage bits = true ↔ Satisfiable (decodeFormula bits) := by
  classical
  simp [encodedSATLanguage]

/-- Every abstract formula is represented faithfully by its canonical bit
encoding. -/
theorem encodedSATLanguage_encodeFormula_iff (formula : Formula) :
    encodedSATLanguage (encodeFormula formula) = true ↔
      Satisfiable formula := by
  rw [encodedSATLanguage_eq_true_iff, decodeFormula_encodeFormula]

/-- The encoded empty conjunction is accepted. -/
@[simp] theorem encodedSATLanguage_encode_nil :
    encodedSATLanguage (encodeFormula []) = true :=
  (encodedSATLanguage_encodeFormula_iff []).2 satisfiable_nil

/-- A formula containing one empty clause is rejected. -/
@[simp] theorem encodedSATLanguage_encode_emptyClause :
    encodedSATLanguage (encodeFormula [[]]) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  have hsat : Satisfiable ([[]] : Formula) :=
    (encodedSATLanguage_encodeFormula_iff [[]]).1 htrue
  exact not_sat_of_mem_empty_clause (by simp) hsat

/-- Therefore encoded SAT is genuinely nonconstant. -/
theorem encodedSATLanguage_nonconstant :
    ∃ x y, encodedSATLanguage x ≠ encodedSATLanguage y := by
  refine ⟨encodeFormula [], encodeFormula [[]], ?_⟩
  simp

/-! ## Immediate consequence of the repaired initialization semantics -/

/-- No finite-control local machine decides encoded SAT at zero clock. -/
theorem no_zeroClock_encodedSAT_decider :
    ¬ ∃ M : Machine,
      Decides M encodedSATLanguage (fun _ => 0) := by
  rintro ⟨M, hdec⟩
  have hconstant := zeroClock_decides_constant
    M encodedSATLanguage hdec
  have hbad := hconstant (encodeFormula []) (encodeFormula [[]])
  simp at hbad

/-! ## The exact superpolynomial frontier -/

/-- Concrete repaired-model statement that encoded CNF SAT has a polynomial
local decider. -/
def LocalSATDecisionInP : Prop := InP encodedSATLanguage

/-- Universal clock lower bound for correct finite-control local SAT
deciders. -/
def LocalSATSuperpolynomialClockLowerBound : Prop :=
  ∀ (M : Machine) (T : Nat -> Nat),
    Decides M encodedSATLanguage T -> ¬ PolyBounded T

/-- The universal superpolynomial clock lower bound is exactly non-membership
of encoded SAT in the repaired local polynomial-time class. -/
theorem localSAT_superpolyClock_iff_not_inP :
    LocalSATSuperpolynomialClockLowerBound ↔
      ¬ LocalSATDecisionInP := by
  constructor
  · intro hlower
    rintro ⟨M, T, hpoly, hdec⟩
    exact hlower M T hdec hpoly
  · intro hnot M T hdec hpoly
    exact hnot ⟨M, T, hpoly, hdec⟩

/-- Equivalently, failure of the universal lower bound is exactly existence
of a polynomial-clock local SAT decider. -/
theorem not_superpolyClock_iff_localSAT_inP :
    ¬ LocalSATSuperpolynomialClockLowerBound ↔
      LocalSATDecisionInP := by
  constructor
  · intro hnotLower
    by_contra hnotP
    exact hnotLower (localSAT_superpolyClock_iff_not_inP.mpr hnotP)
  · intro hP hlower
    exact (localSAT_superpolyClock_iff_not_inP.mp hlower) hP

/-- A purported proof package containing the universal clock lower bound
contains no weaker hidden endpoint: it immediately refutes local SAT in P. -/
theorem no_localSATDecisionInP_of_superpolyClock
    (hlower : LocalSATSuperpolynomialClockLowerBound) :
    ¬ LocalSATDecisionInP :=
  localSAT_superpolyClock_iff_not_inP.mp hlower

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier.encodedSATLanguage_encodeFormula_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier.encodedSATLanguage_nonconstant
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier.no_zeroClock_encodedSAT_decider
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier.localSAT_superpolyClock_iff_not_inP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier.not_superpolyClock_iff_localSAT_inP
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalSATFrontier.no_localSATDecisionInP_of_superpolyClock
