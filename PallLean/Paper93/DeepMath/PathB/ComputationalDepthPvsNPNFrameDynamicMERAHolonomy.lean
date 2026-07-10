import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameMERAHolonomyBridge

/-!
# Dynamic holographic MERA holonomy

The previous restricted-MERA files compared an input-size rank demand with a static accessible-rank
ceiling.  This file supplies the missing *dynamic* layer for the restricted model.

A `DynamicHolonomyMERADecoder M n` has a finite boundary state type, an encoder for the `n`-bit
holonomy signature, a time-indexed boundary transition, and a decoder after `M.layers n` steps.  Exact
recovery makes the end-to-end map a left-invertible encoding.  More strongly, determinism implies that
the map from signatures to the reachable boundary state after **every intermediate step** is injective:
once two signatures merge, no common deterministic suffix can separate them again.

Consequently every time slice, including the final holographic boundary, needs at least `2^n` states.
The restricted MERA family bounds that boundary by its polynomial accessible rank, so at the size where
`2^n` exceeds the MERA ceiling no exact dynamic holonomy decoder exists.

This closes dynamic preservation for the explicitly restricted exact-holonomy task.  It does not prove
that SAT correctness supplies such an encoder/decoder for a genuine NP-complete residual family, nor
that arbitrary polynomial-time machines compile to this fixed-bond local MERA dynamics.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameMERAHolonomyBridge

abbrev MERAFamily := BoundedBondLocalMERADecoderFamily

/-- Iterate a time-indexed deterministic transition for `count` steps beginning at time `start`. -/
def runFrom {State : Type*} (step : Nat → State → State) : Nat → Nat → State → State
  | _, 0, state => state
  | start, count + 1, state => step (start + count) (runFrom step start count state)

/-- Splitting a deterministic trajectory at time `first` gives a prefix followed by the corresponding
shifted suffix. -/
theorem runFrom_add {State : Type*} (step : Nat → State → State)
    (start first second : Nat) (state : State) :
    runFrom step start (first + second) state =
      runFrom step (start + first) second (runFrom step start first state) := by
  induction second with
  | zero => simp [runFrom]
  | succ second ih =>
      simp only [runFrom]
      simpa only [Nat.add_assoc] using
        congrArg (step (start + first + second)) ih

/-- A dynamic bounded-MERA decoder for the complete `n`-bit holonomy signature.

`boundary_card_le` connects the concrete finite state space to the causal-cone accessible-rank budget
already proved polynomial for `M`. -/
structure DynamicHolonomyMERADecoder (M : MERAFamily) (n : Nat) where
  BoundaryState : Type
  [stateFintype : Fintype BoundaryState]
  [stateDecidableEq : DecidableEq BoundaryState]
  encode : (Fin n → Bool) → BoundaryState
  step : Nat → BoundaryState → BoundaryState
  decode : BoundaryState → (Fin n → Bool)
  correct : ∀ signature,
    decode (runFrom step 0 (M.layers n) (encode signature)) = signature
  boundary_card_le : Fintype.card BoundaryState ≤ M.accessibleRank n

namespace DynamicHolonomyMERADecoder

/-- Reachable boundary state after `time` transitions. -/
def stateAt {M : MERAFamily} {n : Nat} (D : DynamicHolonomyMERADecoder M n)
    (time : Nat) (signature : Fin n → Bool) : D.BoundaryState :=
  runFrom D.step 0 time (D.encode signature)

/-- **Dynamic no-merging theorem.**  At every time up to the final MERA layer, distinct holonomy
signatures occupy distinct reachable boundary states.  If they merged at time `t`, the shared
deterministic suffix would give the same final decoded signature, contradicting exact recovery. -/
theorem stateAt_injective {M : MERAFamily} {n : Nat}
    (D : DynamicHolonomyMERADecoder M n) (time : Nat) (htime : time ≤ M.layers n) :
    Function.Injective (D.stateAt time) := by
  intro x y hxy
  have hlayers : M.layers n = time + (M.layers n - time) := by omega
  have hfinal :
      runFrom D.step 0 (M.layers n) (D.encode x) =
        runFrom D.step 0 (M.layers n) (D.encode y) := by
    rw [hlayers, runFrom_add, runFrom_add]
    simpa [stateAt] using
      congrArg (runFrom D.step time (M.layers n - time)) hxy
  rw [← D.correct x, ← D.correct y, hfinal]

/-- Every intermediate reachable boundary slice contains at least `2^n` states. -/
theorem two_pow_le_boundary_card_at_time {M : MERAFamily} {n : Nat}
    (D : DynamicHolonomyMERADecoder M n) (time : Nat) (htime : time ≤ M.layers n) :
    2 ^ n ≤ @Fintype.card D.BoundaryState D.stateFintype := by
  letI : Fintype D.BoundaryState := D.stateFintype
  letI : DecidableEq D.BoundaryState := D.stateDecidableEq
  have hcard := Fintype.card_le_of_injective (D.stateAt time) (D.stateAt_injective time htime)
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hcard

/-- Exact dynamic holonomy recovery forces the exponential signature count into the MERA family's
accessible rank. -/
theorem two_pow_le_accessibleRank {M : MERAFamily} {n : Nat}
    (D : DynamicHolonomyMERADecoder M n) :
    2 ^ n ≤ M.accessibleRank n := by
  exact le_trans (D.two_pow_le_boundary_card_at_time (M.layers n) le_rfl) D.boundary_card_le

/-- Pointwise dynamic contradiction: above the restricted MERA ceiling, no exact dynamic holonomy
decoder exists. -/
theorem no_dynamicDecoder_at_size (M : MERAFamily) (n : Nat) (hn : 1 ≤ n)
    (hgap : n ^ M.polyExponent < 2 ^ n) :
    ¬ Nonempty (DynamicHolonomyMERADecoder M n) := by
  rintro ⟨D⟩
  have hupper : M.accessibleRank n ≤ n ^ M.polyExponent := M.accessibleRank_le_poly n hn
  exact (not_lt_of_ge (le_trans D.two_pow_le_accessibleRank hupper)) hgap

/-- **Dynamic restricted-MERA lower bound.**  Every fixed-bond, fixed-cone, logarithmic-depth MERA
family fails to exactly decode all holonomy signatures at some input size. -/
theorem exists_size_without_dynamicHolonomyDecoder (M : MERAFamily) :
    ∃ n : Nat, 1 ≤ n ∧ ¬ Nonempty (DynamicHolonomyMERADecoder M n) := by
  obtain ⟨n, hn, hgap⟩ := exists_holonomyRank_exceeds_MERA_ceiling M
  refine ⟨n, hn, ?_⟩
  apply no_dynamicDecoder_at_size M n hn
  simpa [holonomyPatternRank_eq_two_pow] using hgap

/-! ## Exact restricted SAT frontier -/

/-- The still-missing compiler/transport statement for one SAT machine: if it decides SAT, it yields
an exact dynamic holonomy decoder in the bounded-MERA family at every size.

This is named rather than assumed.  Proving it from generic SAT correctness would require a genuine
NP-complete residual-to-holonomy construction and decision invariance. -/
def SATCorrectnessCompilesToDynamicHolonomy
    (U : MachineModel) (D : DecisionMachine U) (M : MERAFamily) : Prop :=
  DecidesSAT U D → ∀ n, Nonempty (DynamicHolonomyMERADecoder M n)

/-- A SAT machine cannot have a fixed restricted-MERA dynamic-holonomy compiler at every size. -/
theorem not_decidesSAT_of_dynamicHolonomy_compiler
    {U : MachineModel} {D : DecisionMachine U} (M : MERAFamily)
    (hcompile : SATCorrectnessCompilesToDynamicHolonomy U D M) :
    ¬ DecidesSAT U D := by
  intro hD
  obtain ⟨n, _, hnone⟩ := exists_size_without_dynamicHolonomyDecoder M
  exact hnone (hcompile hD n)

/-- Explicit restricted class: machines accompanied by a fixed bounded-MERA family and the dynamic
holonomy compiler/transport certificate. -/
def HasDynamicHolonomyRestrictedMERA
    (U : MachineModel) (D : DecisionMachine U) : Prop :=
  ∃ M : MERAFamily, SATCorrectnessCompilesToDynamicHolonomy U D M

/-- No machine in the dynamic-holonomy restricted MERA class decides SAT. -/
theorem no_SAT_decider_with_dynamicHolonomyRestrictedMERA {U : MachineModel} :
    ¬ ∃ D : DecisionMachine U,
      HasDynamicHolonomyRestrictedMERA U D ∧ DecidesSAT U D := by
  rintro ⟨D, ⟨M, hcompile⟩, hD⟩
  exact (not_decidesSAT_of_dynamicHolonomy_compiler M hcompile) hD

end DynamicHolonomyMERADecoder

/-!
## Honest endpoint

Dynamic preservation is now derived, not postulated, for deterministic exact decoding in the
restricted holographic model: every intermediate reachable state map is injective.  The contradiction
with fixed-bond logarithmic-depth MERA is therefore a real trajectory theorem.

The open step is upstream: ordinary SAT correctness returns one decision bit and does not automatically
provide exact recovery of all holonomy labels.  `SATCorrectnessCompilesToDynamicHolonomy` isolates that
NP-complete residual/decision-invariance theorem.  Extending the restricted conclusion to all P would
also require compiling arbitrary polynomial-time machines into this MERA architecture.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.runFrom_add
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder.stateAt_injective
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder.two_pow_le_boundary_card_at_time
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder.two_pow_le_accessibleRank
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder.no_dynamicDecoder_at_size
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder.exists_size_without_dynamicHolonomyDecoder
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder.not_decidesSAT_of_dynamicHolonomy_compiler
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameDynamicMERAHolonomy.DynamicHolonomyMERADecoder.no_SAT_decider_with_dynamicHolonomyRestrictedMERA
