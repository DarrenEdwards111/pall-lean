import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCNFContextualBubbleRestrictedObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchCostLowerBound

/-!
# Contextual-bubble adaptive-memory audit

The CNF contextual-bubble calibration gives a `2^m` crossing-state lower bound
when an observer must cross a fixed one-way boundary.  This file performs the
next required stress test: allow the observer a polynomial bit-memory encoding
of the outer bubble before it evaluates future continuations.

For the genuine unit-clause CNF family, the exponential state count compresses
exactly to `m` bits.  We construct the observer, prove its correctness directly
from CNF evaluation, prove its generated formula has exactly `m` literals, and
prove that `m` bits are optimal among faithful bit-memory encodings.  Hence this
family causes neither superlinear memory nor forced recomputation.

This is an informative no-go result.  It shows that contextual fibers plus a
fixed-order state lower bound still do not survive the polynomial-memory escape.
Any successful Route-G invariant must detect a cost not removed by materializing
the outer assignment once—such as context changes that invalidate stored
summaries or force repeated reconstruction under genuinely interacting SAT
continuations.
-/

namespace PallLean.Paper93.DeepMath.PathB.ContextualBubbleAdaptiveMemoryAudit

open CNFSelfReduction
open CNFContextualBubbleRestrictedObserver

/-- A continuation observer with an explicit `w`-bit memory boundary.  The
encoding may retain any function of the outer state; the answer map then sees
that memory and the future continuation. -/
structure BitMemoryObserver {Left Right : Type}
    (f : Left → Right → Bool) (w : ℕ) where
  encode : Left → (Fin w → Bool)
  answer : (Fin w → Bool) → Right → Bool
  correct : ∀ x y, answer (encode x) y = f x y

/-- Correctness forces the memory encoding to distinguish any two outer states
whose continuation sections differ. -/
theorem encode_injective_of_continuation_injective
    {Left Right : Type} {f : Left → Right → Bool} {w : ℕ}
    (hf : Function.Injective f) (O : BitMemoryObserver f w) :
    Function.Injective O.encode := by
  intro x x' hencode
  apply hf
  funext y
  rw [← O.correct x y, ← O.correct x' y, hencode]

/-- The exact observer for the unit-CNF continuation family simply remembers
the outer assignment. -/
def unitCNFBitMemoryObserver (m : ℕ) :
    BitMemoryObserver (unitCNFContinuation m) m where
  encode := fun a ↦ a
  answer := fun memory future ↦ eval (unitAssignmentCNF memory) future
  correct := by
    intro _ _
    rfl

/-- The stored `m` bits are sufficient to recover every genuine CNF
continuation answer. -/
theorem unitCNFBitMemoryObserver_correct (m : ℕ)
    (a b : Fin m → Bool) :
    (unitCNFBitMemoryObserver m).answer
      ((unitCNFBitMemoryObserver m).encode a) b =
      unitCNFContinuation m a b :=
  (unitCNFBitMemoryObserver m).correct a b

/-- The generated continuation formula has exactly one literal per stored bit,
so materialization and direct checking have linear encoded size. -/
theorem unitAssignmentCNF_descLen (m : ℕ) (a : Fin m → Bool) :
    descLen (unitAssignmentCNF a) = m := by
  unfold descLen unitAssignmentCNF
  rw [List.map_ofFn]
  have hfun : (List.length ∘ fun i : Fin m ↦ [(i, a i)]) =
      (fun _ : Fin m ↦ 1) := by
    funext i
    rfl
  rw [hfun]
  rw [List.ofFn_const, List.sum_replicate]
  simp

/-- Any faithful `w`-bit observer for this family needs at least as many memory
states as there are outer assignments. -/
theorem unitCNFBitMemoryObserver_state_lower_bound
    (m w : ℕ) (O : BitMemoryObserver (unitCNFContinuation m) w) :
    2 ^ m ≤ 2 ^ w := by
  have hinj : Function.Injective O.encode :=
    encode_injective_of_continuation_injective
      (unitCNFContinuation_injective m) O
  have hcard : Fintype.card (Fin m → Bool) ≤
      Fintype.card (Fin w → Bool) :=
    Fintype.card_le_of_injective O.encode hinj
  simpa [Fintype.card_bool] using hcard

/-- Therefore `m` bits are not merely sufficient but optimal. -/
theorem unitCNFBitMemoryObserver_width_lower_bound
    (m w : ℕ) (O : BitMemoryObserver (unitCNFContinuation m) w) :
    m ≤ w := by
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1
    (unitCNFBitMemoryObserver_state_lower_bound m w O)

/-- A proposed superlinear memory-forcing statement already fails on the
genuine CNF family: the exact-width observer is a counterexample. -/
def ForcesMoreThanLinearMemory (m : ℕ) : Prop :=
  ∀ (w : ℕ), Nonempty (BitMemoryObserver (unitCNFContinuation m) w) → m < w

theorem unitCNF_not_forcesMoreThanLinearMemory (m : ℕ) :
    ¬ ForcesMoreThanLinearMemory m := by
  intro h
  exact (Nat.lt_irrefl m) (h m ⟨unitCNFBitMemoryObserver m⟩)

/-- Complete adaptive-memory calibration: the family has an exact `m`-bit
realization, all faithful realizations need at least `m` bits, and its direct
CNF materialization has linear literal count. -/
structure AdaptiveMemoryCalibration (m : ℕ) : Prop where
  existsExactWidth : Nonempty (BitMemoryObserver (unitCNFContinuation m) m)
  widthOptimal : ∀ (w : ℕ),
    BitMemoryObserver (unitCNFContinuation m) w → m ≤ w
  directSyntaxLinear : ∀ a : Fin m → Bool,
    descLen (unitAssignmentCNF a) = m
  noSuperlinearForcing : ¬ ForcesMoreThanLinearMemory m

theorem unitCNFAdaptiveMemoryCalibration (m : ℕ) :
    AdaptiveMemoryCalibration m where
  existsExactWidth := ⟨unitCNFBitMemoryObserver m⟩
  widthOptimal := unitCNFBitMemoryObserver_width_lower_bound m
  directSyntaxLinear := unitAssignmentCNF_descLen m
  noSuperlinearForcing := unitCNF_not_forcesMoreThanLinearMemory m

/-!
## Audit verdict

The fixed-order `2^m` crossing-state bound is real, but it is exactly the state
space of an `m`-bit memory.  A stronger observer stores the outer assignment
once and evaluates the corresponding `m`-literal CNF continuation directly.
There is no superlinear thermodynamic deficit on this family.

Consequently, the next candidate cannot merely count contextual sections.  It
must use a SAT family in which cheap context changes destroy or invalidate a
polynomial stored summary, and it must prove that repeated repair is expensive
without assuming the desired SAT lower bound.  That is the surviving adaptive
Route-G frontier.
-/

end PallLean.Paper93.DeepMath.PathB.ContextualBubbleAdaptiveMemoryAudit

#print axioms PallLean.Paper93.DeepMath.PathB.ContextualBubbleAdaptiveMemoryAudit.encode_injective_of_continuation_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualBubbleAdaptiveMemoryAudit.unitAssignmentCNF_descLen
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualBubbleAdaptiveMemoryAudit.unitCNFBitMemoryObserver_width_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualBubbleAdaptiveMemoryAudit.unitCNF_not_forcesMoreThanLinearMemory
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualBubbleAdaptiveMemoryAudit.unitCNFAdaptiveMemoryCalibration
