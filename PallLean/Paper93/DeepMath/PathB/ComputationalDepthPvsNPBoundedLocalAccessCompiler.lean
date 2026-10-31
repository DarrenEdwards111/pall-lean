import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPRamanujanQueryMERACompiler
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPOperationalCausalQuotientBarrier

/-!
# Bounded-local-access / bounded-fan-in SAT trajectory compiler

This file states the concrete restricted operational class requested after the
run-indexed `TΦ` audit.  A profile has:

* a fixed local alphabet;
* fixed fan-in per local update;
* a fixed number of causal-cone cells per layer;
* at most logarithmically many layers;
* an exposed-rank bound by the number of local causal-cone profiles.

The profile compiles directly into the existing bounded-bond MERA interface.  A SAT
machine carrying an exact Ramanujan-routed query transcript in this profile is therefore
ruled out by the already proved dynamic holonomy lower bound.

This is an unconditional theorem for the explicitly restricted class.  It does not say
that arbitrary polynomial-time machines satisfy the locality/profile certificate.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy
open PallLean.Paper93.DeepMath.PathB.PvsNPDynamicHolonomyQueryTranscriptBridge
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanQueryMERACompiler

/-- Fixed-parameter bounded-local-access dynamics.

`effectiveLocalStates` counts one cell together with all values visible to one
bounded-fan-in update.  `exposedRank_le_profiles` is the concrete operational counting
law: the accessible task rank is no larger than the assignments to the active local
profiles crossing the logarithmic-depth causal cone. -/
structure BoundedLocalAccessProfile where
  alphabetStates : Nat
  fanIn : Nat
  coneCellsPerLayer : Nat
  alphabetStates_pos : 1 ≤ alphabetStates
  rounds : Nat → Nat
  exposedRank : Nat → Nat
  rounds_le_log : ∀ n, rounds n ≤ Nat.log 2 n
  exposedRank_le_profiles : ∀ n,
    exposedRank n ≤
      (alphabetStates ^ (fanIn + 1)) ^ (coneCellsPerLayer * rounds n)

namespace BoundedLocalAccessProfile

/-- Number of possible bounded-fan-in local views. -/
def effectiveLocalStates (P : BoundedLocalAccessProfile) : Nat :=
  P.alphabetStates ^ (P.fanIn + 1)

theorem effectiveLocalStates_pos (P : BoundedLocalAccessProfile) :
    1 ≤ P.effectiveLocalStates := by
  exact Nat.one_le_pow (P.fanIn + 1) P.alphabetStates P.alphabetStates_pos

/-- Compile the operational profile to the existing fixed-bond local-MERA profile. -/
def toMERA (P : BoundedLocalAccessProfile) :
    BoundedBondLocalMERADecoderFamily where
  bondStates := P.effectiveLocalStates
  coneFactor := P.coneCellsPerLayer
  bondStates_pos := P.effectiveLocalStates_pos
  layers := P.rounds
  accessibleRank := P.exposedRank
  layers_le_log := P.rounds_le_log
  rank_causal_cone := by
    intro n
    exact P.exposedRank_le_profiles n

/-- Hence bounded local access, bounded fan-in and logarithmic depth give a polynomial
operational rank ceiling. -/
theorem exposedRank_le_poly (P : BoundedLocalAccessProfile)
    (n : Nat) (hn : 1 ≤ n) :
    P.exposedRank n ≤ n ^ P.toMERA.polyExponent :=
  P.toMERA.accessibleRank_le_poly n hn

/-- Non-vacuity: the profile bound can be saturated exactly. -/
def saturated (alphabetStates fanIn coneCellsPerLayer : Nat)
    (hpos : 1 ≤ alphabetStates) : BoundedLocalAccessProfile where
  alphabetStates := alphabetStates
  fanIn := fanIn
  coneCellsPerLayer := coneCellsPerLayer
  alphabetStates_pos := hpos
  rounds := fun n => Nat.log 2 n
  exposedRank := fun n =>
    (alphabetStates ^ (fanIn + 1)) ^ (coneCellsPerLayer * Nat.log 2 n)
  rounds_le_log := fun _ => le_rfl
  exposedRank_le_profiles := fun _ => le_rfl

end BoundedLocalAccessProfile

/-! ## Explicit restricted machine class -/

/-- A SAT decision machine equipped with the concrete bounded-local-access compiler.

The transcript field is deliberately operational and load-bearing: it says the actual
complete independent-query execution is realized within `profile.exposedRank`.  It is
not inferred from SAT correctness alone. -/
structure BoundedLocalAccessSATCompiler
    (U : MachineModel) (D : DecisionMachine U) where
  profile : BoundedLocalAccessProfile
  layout : ∀ n, RamanujanExpanderQueryLayout n
  compile : DecidesSAT U D → ∀ n,
    Nonempty (RamanujanMERAQueryTranscript
      (n := n) D profile.toMERA)

namespace BoundedLocalAccessSATCompiler

/-- Forget the explicit local-access parameters to the Ramanujan/MERA compiler. -/
def toRamanujan
    {U : MachineModel} {D : DecisionMachine U}
    (C : BoundedLocalAccessSATCompiler U D) :
    RamanujanQueryMERACompiler U D where
  mera := C.profile.toMERA
  layout := C.layout
  compile := C.compile

/-- **Restricted bounded-local-access SAT lower bound.**  No machine carrying this
fixed-alphabet, bounded-fan-in, logarithmic-depth exact compiler decides SAT. -/
theorem not_decidesSAT
    {U : MachineModel} {D : DecisionMachine U}
    (C : BoundedLocalAccessSATCompiler U D) :
    ¬ DecidesSAT U D :=
  C.toRamanujan.not_decidesSAT

end BoundedLocalAccessSATCompiler

/-- Class-level statement: there is no SAT decider in the explicitly certified
bounded-local-access trajectory class. -/
theorem no_SAT_decider_with_boundedLocalAccessCompiler (U : MachineModel) :
    ¬ ∃ D : DecisionMachine U,
      Nonempty (BoundedLocalAccessSATCompiler U D) ∧ DecidesSAT U D := by
  rintro ⟨D, ⟨C⟩, hD⟩
  exact C.not_decidesSAT hD

/-!
## Honest endpoint

The requested restricted theorem is now closed: fixed local alphabet, fixed fan-in,
fixed causal-cone width, logarithmic depth, and exact Ramanujan-routed SAT-query
transcripts are incompatible with SAT correctness.

The theorem does not extend to all of `P`: general polynomial-time machines may have
polynomially many sequential rounds, growing/random-access workspaces, and adaptive
global accesses, and no theorem here compiles them into this fixed local profile.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler.BoundedLocalAccessProfile.effectiveLocalStates_pos
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler.BoundedLocalAccessProfile.exposedRank_le_poly
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler.BoundedLocalAccessSATCompiler.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler.no_SAT_decider_with_boundedLocalAccessCompiler
