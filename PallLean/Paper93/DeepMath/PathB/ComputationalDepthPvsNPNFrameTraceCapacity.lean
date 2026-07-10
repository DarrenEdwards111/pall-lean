import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPTranscriptObserver

/-!
# N-Frame trace channels: stabilized decoding and the bit-capacity pressure test

This file extracts the discrete information-theoretic core of the N-Frame Observer-Boundary Trace model:

```text
latent branch --trace channel--> finite observer boundary --stabilizer--> semantic label.
```

The intended correspondence is:

* a latent structure/branch is an `m`-bit residual label;
* the N-Frame projection is `trace`;
* variational stabilization is represented extensionally by `stabilize`;
* `stabilization_correct` says that the stabilized trace recovers the task-relevant label;
* `capacityBits` bounds the number of boundary states by `2^capacityBits`.

The pressure test has two sides, both proved here:

1. stabilized recovery of an injective `m`-bit label forces `m ≤ capacityBits`;
2. this is tight: the identity trace uses exactly `m` bits and has `2^m` states.

Therefore a polynomial **bit** bound is not a polynomial **state-count** bound.  Polynomial time/space alone
does not supply the old H4 hypothesis `card boundary ≤ m^k`; a P-vs-NP application needs a genuinely stronger
task-relevant compression theorem, such as `capacityBits < m`.  Nothing in this file is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open SATDepthMachine

/-- A finite N-Frame trace channel on the `2^m` latent residual branches.

The channel may compress or distort arbitrary latent information, but `stabilization_correct` requires it to
retain the chosen injective task label. -/
structure StabilizedNFrameTraceChannel (m : Nat) where
  boundary : Type
  fintypeBoundary : Fintype boundary
  trace : Assignment m → boundary
  label : Assignment m → Assignment m
  label_injective : Function.Injective label
  stabilize : boundary → Assignment m
  stabilization_correct : ∀ a, stabilize (trace a) = label a
  capacityBits : Nat
  stateCapacity : @Fintype.card boundary fintypeBoundary ≤ 2 ^ capacityBits

namespace StabilizedNFrameTraceChannel

/-- Number of available observer-boundary states. -/
def stateCount {m : Nat} (C : StabilizedNFrameTraceChannel m) : Nat :=
  @Fintype.card C.boundary C.fintypeBoundary

/-- Correct stabilization of injective labels forces the trace channel itself to be injective. -/
theorem trace_injective {m : Nat} (C : StabilizedNFrameTraceChannel m) :
    Function.Injective C.trace := by
  intro a b htrace
  have ha := C.stabilization_correct a
  have hb := C.stabilization_correct b
  rw [htrace] at ha
  exact C.label_injective (ha.symm.trans hb)

/-- A stabilized trace channel for `m`-bit labels needs at least `2^m` boundary states. -/
theorem stateCount_ge_labels {m : Nat} (C : StabilizedNFrameTraceChannel m) :
    2 ^ m ≤ C.stateCount := by
  letI : Fintype C.boundary := C.fintypeBoundary
  exact boundary_card_ge_exp C.trace C.trace_injective

/-- **N-Frame bit-capacity lower bound.** Recovering an injective `m`-bit task label after boundary
projection requires at least `m` bits of boundary capacity. -/
theorem label_bits_le_capacity {m : Nat} (C : StabilizedNFrameTraceChannel m) :
    m ≤ C.capacityBits := by
  have hpow : 2 ^ m ≤ 2 ^ C.capacityBits :=
    le_trans C.stateCount_ge_labels C.stateCapacity
  by_contra hnot
  have hlt : C.capacityBits < m := Nat.lt_of_not_ge hnot
  exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hlt)) hpow

/-- Any proposed trace channel with fewer than `m` capacity bits cannot stably recover an injective
`m`-bit residual label. -/
theorem sublinear_capacity_impossible {m : Nat} (C : StabilizedNFrameTraceChannel m)
    (hsmall : C.capacityBits < m) : False :=
  (not_le_of_gt hsmall) C.label_bits_le_capacity

/-- Package an existing residual-family transcript, decoder, and state-capacity bound as an N-Frame channel. -/
def ofTranscript {m bits : Nat} {α : Type} [Fintype α]
    (obs : TranscriptObserver α) (fam : FoolingResidualFamily m)
    (decode : α → Assignment m)
    (hdecode : ∀ a, decode (obs (fam.instanceOf a)) = fam.label a)
    (hcapacity : Fintype.card α ≤ 2 ^ bits) :
    StabilizedNFrameTraceChannel m where
  boundary := α
  fintypeBoundary := inferInstance
  trace := fun a => obs (fam.instanceOf a)
  label := fam.label
  label_injective := fam.label_injective
  stabilize := decode
  stabilization_correct := hdecode
  capacityBits := bits
  stateCapacity := hcapacity

/-- The full, uncompressed trace is a valid stabilized N-Frame channel using exactly `m` bits. -/
def identityTraceChannel (m : Nat) : StabilizedNFrameTraceChannel m where
  boundary := Assignment m
  fintypeBoundary := inferInstance
  trace := id
  label := id
  label_injective := fun _ _ h => h
  stabilize := id
  stabilization_correct := fun _ => rfl
  capacityBits := m
  stateCapacity := by
    simpa [card_assignment]

/-- The identity trace has exactly `2^m` observer-boundary states. -/
theorem identityTrace_stateCount (m : Nat) :
    (identityTraceChannel m).stateCount = 2 ^ m := by
  exact card_assignment m

/-- The identity trace meets the capacity lower bound exactly. -/
theorem identityTrace_capacityBits (m : Nat) :
    (identityTraceChannel m).capacityBits = m := rfl

/-- The information-theoretic lower bound is tight: an exact-recovery stabilized quotient with
exactly `m` capacity bits exists at every label width. -/
theorem exact_capacity_achievable (m : Nat) :
    ∃ C : StabilizedNFrameTraceChannel m, C.capacityBits = m :=
  ⟨identityTraceChannel m, rfl⟩

/-- Any exact-recovery channel whose advertised capacity is at most the label width is optimal:
its capacity is exactly `m`. -/
theorem capacity_eq_label_bits_of_le {m : Nat} (C : StabilizedNFrameTraceChannel m)
    (hupper : C.capacityBits ≤ m) : C.capacityBits = m := by
  exact Nat.le_antisymm hupper C.label_bits_le_capacity

/-- **Capacity pressure-test countermodel.** Even a linear `m`-bit boundary has exponentially many states.
Thus replacing `card boundary ≤ poly(m)` by `capacityBits ≤ poly(m)` destroys the pigeonhole contradiction. -/
theorem identityTrace_states_exceed_bit_count (m : Nat) :
    (identityTraceChannel m).capacityBits < (identityTraceChannel m).stateCount := by
  rw [identityTrace_capacityBits, identityTrace_stateCount]
  exact Nat.lt_two_pow_self

/-! ## The proposed all-P capacity-deficit theorem is exactly the separation

The sharpened N64 proposal says that SAT correctness should produce an exact-recovery stabilized
quotient but also force that quotient below the `m` bits required by its injective task label.  The
following interface records precisely that proposal for one machine.  Its two fields are deliberately
kept separate: the first is the trace/stabilization construction, while the second is the genuinely
load-bearing solver-specific capacity deficit.
-/

/-- A conditional N-Frame capacity-deficit claim for one alleged SAT decision machine. -/
structure CapacityDeficitFromCorrectnessFor (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  channel_of_decides : DecidesSAT U D → StabilizedNFrameTraceChannel m
  deficit_of_decides :
    ∀ hD : DecidesSAT U D, (channel_of_decides hD).capacityBits < m

namespace CapacityDeficitFromCorrectnessFor

/-- Such a deficit theorem rules out the alleged SAT decider immediately. -/
theorem not_decidesSAT {U : MachineModel} {D : DecisionMachine U}
    (F : CapacityDeficitFromCorrectnessFor U D) : ¬ DecidesSAT U D := by
  intro hD
  exact (F.channel_of_decides hD).sublinear_capacity_impossible (F.deficit_of_decides hD)

/-- If a particular machine is already known not to decide SAT, the conditional deficit interface
is inhabited vacuously.  This direction is used only to calibrate the logical strength of the global
proposal; it is not a trace construction. -/
noncomputable def of_not_decidesSAT {U : MachineModel} (D : DecisionMachine U)
    (hD : ¬ DecidesSAT U D) : CapacityDeficitFromCorrectnessFor U D where
  m := 1
  channel_of_decides := fun h => False.elim (hD h)
  deficit_of_decides := fun h => False.elim (hD h)

end CapacityDeficitFromCorrectnessFor

/-- The proposed capacity-deficit theorem for every machine in the model. -/
abbrev CapacityDeficitFromCorrectnessForAllMachines (U : MachineModel) : Type 1 :=
  ∀ D : DecisionMachine U, CapacityDeficitFromCorrectnessFor U D

/-- A global N-Frame capacity-deficit theorem implies that SAT has no polynomial-time decider in
the abstract machine model. -/
theorem no_SATDecisionInP_of_capacityDeficit {U : MachineModel}
    (hDeficit : CapacityDeficitFromCorrectnessForAllMachines U) : ¬ SATDecisionInP U := by
  intro hP
  rcases hP with ⟨D, hD⟩
  exact (hDeficit D).not_decidesSAT hD

/-- Conversely, absence of a SAT decider vacuously inhabits the conditional global interface. -/
noncomputable def capacityDeficit_of_no_SATDecisionInP {U : MachineModel}
    (hNo : ¬ SATDecisionInP U) : CapacityDeficitFromCorrectnessForAllMachines U := by
  intro D
  refine CapacityDeficitFromCorrectnessFor.of_not_decidesSAT D ?_
  intro hD
  exact hNo ⟨D, hD⟩

/-- **Exact calibration of the N64 route.**  Producing the proposed sub-`m` exact-recovery
task quotient for every alleged SAT decider is logically equivalent to proving that the model has no
polynomial-time SAT decider.  Hence the solver-specific deficit is not a smaller remaining lemma: it is
the separation itself. -/
theorem capacityDeficit_iff_no_SATDecisionInP {U : MachineModel} :
    Nonempty (CapacityDeficitFromCorrectnessForAllMachines U) ↔ ¬ SATDecisionInP U := by
  constructor
  · rintro ⟨hDeficit⟩
    exact no_SATDecisionInP_of_capacityDeficit hDeficit
  · intro hNo
    exact ⟨capacityDeficit_of_no_SATDecisionInP hNo⟩

/-!
## Verdict for the unrestricted trace route

The N-Frame channel supplies a clean formal language for projection and stabilized decoding.  Its correct
information-theoretic lower bound is `m ≤ capacityBits`, not `2^m ≤ capacityBits`.  Since polynomial-time
machines may use at least linear (indeed polynomial) trace bits, this bound is compatible with perfect label
recovery.  A P-vs-NP contradiction would require an additional theorem forcing the **task-relevant stabilized
quotient** below `m` bits for every alleged P-time SAT solver.  That theorem is not implied by finiteness,
polynomial time, Markovianity, support projection, or hierarchical compression alone.
-/

end StabilizedNFrameTraceChannel
end PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.trace_injective
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.stateCount_ge_labels
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.label_bits_le_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.sublinear_capacity_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.identityTrace_states_exceed_bit_count
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.exact_capacity_achievable
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.capacity_eq_label_bits_of_le
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.CapacityDeficitFromCorrectnessFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel.capacityDeficit_iff_no_SATDecisionInP
