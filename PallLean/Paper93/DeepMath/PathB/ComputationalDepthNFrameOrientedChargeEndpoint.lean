import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRamanujanActionSymmetryAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKannanTruthTableOrder

/-!
# Gauge-fixed oriented N-frame charge endpoint

The concrete Ramanujan action has translation and sign symmetries.  This file
implements the natural repair in two stages.

1. `anchorCoord` removes global translation freedom by subtracting one chosen
   root coordinate.
2. `weightedOrientationAction` records the complete oriented sign label in
   binary order.  Unlike an unweighted scalar hinge/Hamming count, it is
   injective on all `2^m` labels.

The repaired charge separates labels unconditionally.  The amplituhedron
question can therefore be tested without hiding the hard step in an abstract
`ramanujanActionSeparates` field.  The final theorem proves that no projection
to polynomially many positive cells can conserve this complete oriented charge
below the exponential gap.

Thus gauge-fixing and orientation solve the *raw separation* problem, but they
make the remaining obstruction exact: a hypothetical polynomial SAT solver
would have to induce a polynomial positive-cell projection that conserves all
`2^m` oriented charges.  Proving that solver-to-conservation theorem is the
load-bearing lower-bound step.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint

open PallLean.Paper93.Concrete
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.PvsNPTranscriptObserver
open PallLean.Paper93.DeepMath.PathB.PvsNPRamanujanHolographicAmplituhedronExtraction
open PallLean.Paper93.DeepMath.PathB.KannanTT

/-! ## Translation gauge fixing -/

/-- Fix global translation freedom by anchoring the field at one vertex. -/
def anchorCoord {N : Nat} (root : Fin N) (coord : CoordMap N) : CoordMap N where
  values := fun v => coord.values v - coord.values root

@[simp] theorem anchorCoord_at_root
    {N : Nat} (root : Fin N) (coord : CoordMap N) :
    (anchorCoord root coord).values root = 0 := by
  simp [anchorCoord]

/-- Anchoring quotients out exactly the global translations found in the
preceding symmetry audit. -/
theorem anchorCoord_shift_invariant
    {N : Nat} (root : Fin N) (c : Real) (coord : CoordMap N) :
    anchorCoord root
        (NFrameRamanujanActionSymmetryAudit.shiftCoord c coord) =
      anchorCoord root coord := by
  apply congrArg CoordMap.mk
  funext v
  simp only [NFrameRamanujanActionSymmetryAudit.shiftCoord]
  ring

/-! ## Why the unweighted hinge is insufficient -/

/-- The unweighted Boolean orientation count, the discrete scalar carried by
an unweighted local hinge on canonical signed fields. -/
def unweightedOrientation {N : Nat} (label : Assignment N) : Nat :=
  (Finset.univ.filter fun v => label v).card

def firstOne : Assignment 2 := fun v => v = 0
def secondOne : Assignment 2 := fun v => v = 1

theorem firstOne_ne_secondOne : firstOne ≠ secondOne := by
  intro h
  have hv := congrFun h (0 : Fin 2)
  simp [firstOne, secondOne] at hv

/-- Two different orientations already collide under the unweighted scalar
hinge at dimension two. -/
theorem unweightedOrientation_collision :
    unweightedOrientation firstOne = unweightedOrientation secondOne := by
  decide

theorem unweightedOrientation_not_injective :
    ¬ Function.Injective (unweightedOrientation : Assignment 2 -> Nat) := by
  intro hInjective
  exact firstOne_ne_secondOne
    (hInjective unweightedOrientation_collision)

/-! ## Complete weighted orientation charge -/

/-- Binary weighted orientation code.  This is the minimal scalar refinement
that retains the complete oriented sign pattern rather than only its Hamming
weight. -/
def weightedOrientationCode {N : Nat} (label : Assignment N) : Nat :=
  natOfBools (List.ofFn label)

theorem weightedOrientationCode_injective {N : Nat} :
    Function.Injective (weightedOrientationCode : Assignment N -> Nat) := by
  intro a b hCode
  apply List.ofFn_injective
  exact natOfBools_inj (List.ofFn a) (List.ofFn b) (by simp) hCode

/-- Real-valued presentation suitable for the N-frame action interface. -/
noncomputable def weightedOrientationAction {N : Nat}
    (label : Assignment N) : Real :=
  weightedOrientationCode label

theorem weightedOrientationAction_injective {N : Nat} :
    Function.Injective (weightedOrientationAction : Assignment N -> Real) := by
  intro a b h
  apply weightedOrientationCode_injective
  change (weightedOrientationCode a : Real) = weightedOrientationCode b at h
  exact Nat.cast_inj.mp h

/-! ## Exact amplituhedron conservation endpoint -/

/-- Conservation of the complete oriented charge through a positive-cell
projection derives the full fooling-label preservation law. -/
theorem sound_of_orientedAction_conservation
    {m : Nat} {raw screen cell : Type}
    (rawObserver : TranscriptObserver raw)
    (H : HolographicProjectionStage raw screen)
    (A : AmplituhedronPositiveCellStage screen cell)
    (fam : FoolingResidualFamily m)
    (cellAction : cell -> Real)
    (hConserve : forall a : Assignment m,
      weightedOrientationAction (fam.label a) =
        cellAction
          (composedPositiveProjection H A (rawObserver (fam.instanceOf a)))) :
    SoundOnFoolingFamily
      (fun x => composedPositiveProjection H A (rawObserver x)) fam := by
  intro a b hCell
  apply weightedOrientationAction_injective
  have hCell' :
      composedPositiveProjection H A (rawObserver (fam.instanceOf a)) =
        composedPositiveProjection H A (rawObserver (fam.instanceOf b)) := by
    simpa only using hCell
  calc
    weightedOrientationAction (fam.label a) =
        cellAction
          (composedPositiveProjection H A
            (rawObserver (fam.instanceOf a))) := hConserve a
    _ = cellAction
          (composedPositiveProjection H A
            (rawObserver (fam.instanceOf b))) := by rw [hCell']
    _ = weightedOrientationAction (fam.label b) := (hConserve b).symm

/-- A polynomial positive-cell boundary below the exponential gap cannot
conserve the complete gauge-fixed oriented charge. -/
theorem no_polynomial_amplituhedron_conserves_orientedAction
    {m k : Nat} {raw screen cell : Type} [Fintype cell]
    (rawObserver : TranscriptObserver raw)
    (H : HolographicProjectionStage raw screen)
    (A : AmplituhedronPositiveCellStage screen cell)
    (fam : FoolingResidualFamily m)
    (cellAction : cell -> Real)
    (hpoly : Fintype.card cell <= m ^ k)
    (hgap : m ^ k < 2 ^ m) :
    ¬ (forall a : Assignment m,
      weightedOrientationAction (fam.label a) =
        cellAction
          (composedPositiveProjection H A (rawObserver (fam.instanceOf a)))) := by
  intro hConserve
  exact transcript_fooling_contradicts_poly_boundary
    (fun x => composedPositiveProjection H A (rawObserver x)) fam
    (sound_of_orientedAction_conservation
      rawObserver H A fam cellAction hConserve)
    hpoly hgap

end PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint.anchorCoord_shift_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint.unweightedOrientation_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint.weightedOrientationAction_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameOrientedChargeEndpoint.no_polynomial_amplituhedron_conserves_orientedAction
