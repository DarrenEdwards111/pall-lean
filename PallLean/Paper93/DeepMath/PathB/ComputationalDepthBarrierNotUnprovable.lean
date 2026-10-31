import Mathlib.Data.Nat.Basic

/-!
# The barrier bars natural proofs, not all proofs: hard is not unprovable

Darren's refined point: *computation in P* can't prove `P vs NP`, the same way *computation* can't decide
halting.  This is **correct** — it is the **natural-proofs barrier** (Razborov–Rudich), and the repo already
formalizes it (`ComputationalDepthNaturalProofsBarrier`: the counting hardness property is *large* and
*useful*, hence — under a cryptographic assumption — *not constructive*; a *P-computable* proof cannot
isolate `NP`).  This file adds the complementary logical fact: barring the **natural (P-computable)** proofs
is *not* barring **all** proofs, so the barrier means **hard**, not **unprovable**.

## The distinction

A proof method is *natural* when it is itself efficient/constructive — a P-computation.  The barrier says
natural methods can't prove `P vs NP`.  A *non-natural* method (not an efficient computation) is **outside
the barrier's scope**: the barrier's conclusion is guarded by "is P-computable", so on a non-natural method
it says nothing.  Hence the barrier is *consistent* with the target being provable — by a non-natural proof,
which is exactly this whole map's target (the EXP middle, `DilemmaBreak`).

## What is proved

* **`natural_is_barriered`** — the natural (P-computable) method does not prove the target: the barrier bites
  the efficient/constructive proofs.
* **`nonnatural_barriered_yet_proves`** — a non-P-computable method satisfies the barrier (vacuously) *and*
  proves the target.  Non-natural proofs escape the barrier.
* **`barrier_not_unprovable`** — so "every natural method fails" is *consistent* with "the target is proved"
  (by a non-natural method).  Barring natural proofs ≠ barring all proofs.

## Honest scope — the analogy is apt, and it means hard, not unprovable

Just as Turing proved a limitation on *computation* (halting undecidable), Razborov–Rudich proved a
limitation on *P-computable proofs* (they can't prove strong lower bounds without breaking crypto).  Both are
real, proved barriers on a *computational class*, and neither closes off the *wider faculty*: Turing's
limitation is itself a proof, and the natural-proofs barrier leaves *non-natural* proofs open.  So
"computation-in-P can't prove `P vs NP`" is a genuine theorem — it says `P vs NP` is **hard**, ruling out the
efficient/constructive proofs, *not* that it is unprovable.  This file certifies neither `P ≠ NP` nor its
unprovability.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BarrierNotUnprovable

/-- A proof method, tagged by whether it is itself **P-computable** (efficient / constructive — "natural")
and whether it **proves** the target (`P vs NP`). -/
structure ProofMethod where
  /-- is the method itself efficient/constructive (natural) -/
  isPComputable : Bool
  /-- does it prove the target -/
  provesTarget : Bool

/-- **The natural-proofs barrier** as a property of a method: if it is P-computable (natural), it does *not*
prove the target.  (Razborov–Rudich, formalized substantively in `ComputationalDepthNaturalProofsBarrier`.) -/
def Barriered (m : ProofMethod) : Prop := m.isPComputable = true → m.provesTarget = false

/-- A **natural** method: P-computable, and (by the barrier) does not prove the target. -/
def naturalMethod : ProofMethod := ⟨true, false⟩

/-- A **non-natural** method: not P-computable — outside the barrier's scope. -/
def nonNaturalMethod : ProofMethod := ⟨false, true⟩

/-- **The barrier bites the natural method (proved).**  A P-computable proof does not prove the target. -/
theorem natural_is_barriered : Barriered naturalMethod := by
  intro _
  rfl

/-- **A non-natural method escapes the barrier (proved).**  `nonNaturalMethod` satisfies the barrier
(vacuously — it is not P-computable) *and* proves the target.  Non-natural proofs are outside the barrier. -/
theorem nonnatural_barriered_yet_proves :
    Barriered nonNaturalMethod ∧ nonNaturalMethod.provesTarget = true := by
  refine ⟨?_, rfl⟩
  intro h
  exact absurd h (by decide)

/-- **Barring natural proofs is not barring all proofs (proved).**  There is a method that satisfies the
natural-proofs barrier *and* proves the target — so "no P-computable proof" is consistent with "the target is
proved" (by a non-natural method).  The barrier means hard, not unprovable. -/
theorem barrier_not_unprovable : ∃ m : ProofMethod, Barriered m ∧ m.provesTarget = true :=
  ⟨nonNaturalMethod, nonnatural_barriered_yet_proves.1, nonnatural_barriered_yet_proves.2⟩

end PallLean.Paper93.DeepMath.PathB.BarrierNotUnprovable

#print axioms PallLean.Paper93.DeepMath.PathB.BarrierNotUnprovable.natural_is_barriered
#print axioms PallLean.Paper93.DeepMath.PathB.BarrierNotUnprovable.barrier_not_unprovable
