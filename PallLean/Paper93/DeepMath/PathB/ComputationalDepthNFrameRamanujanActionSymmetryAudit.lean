import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRamanujanAmplituhedronConservationBridge
import PallLean.Paper93.Concrete.FullLagrangianFixed

/-!
# Ramanujan N-frame action: affine-symmetry audit

The preceding conservation bridge reduced the proposed
Ramanujan--N-frame--amplituhedron route to a family-sensitive action that
separates all hard residual labels and is conserved by the positive-cell
projection.  This file tests the repository's most concrete candidate:

```text
edge Dirichlet energy + projection rank + log-det barrier.
```

The result is a structural obstruction, not merely a missing estimate.

* Dirichlet edge energy depends only on coordinate differences, so it is
  invariant under a global translation of the field.
* Squaring those differences also makes it invariant under global sign
  reversal.
* The rank and log-det terms depend only on the projection and are unchanged
  by either coordinate transformation.

Consequently the full concrete action is not injective on observer gauges for
any nonempty vertex set, any graph, and any couplings.  In particular it cannot
by itself furnish the `ramanujanActionSeparates` field of the conservation
bridge.

This pinpoints the manuscript's parity/orientation hinge term as essential.
The final theorem below proves that whenever an augmented action separates a
translated or sign-reversed pair, the distinction must come from that added
orientation term; none can come from the existing three-term core.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameRamanujanActionSymmetryAudit

open PallLean.Paper93.Concrete

/-! ## Coordinate symmetries -/

/-- Translate every observer coordinate by the same real constant. -/
def shiftCoord {N : Nat} (c : Real) (coord : CoordMap N) : CoordMap N where
  values := fun v => coord.values v + c

/-- Retain the projection exactly while translating its coordinate field. -/
noncomputable def shiftGauge {N : Nat} (c : Real)
    (gauge : ObserverGauge N) : ObserverGauge N where
  projection := gauge.projection
  is_idempotent := gauge.is_idempotent
  rank_finite := gauge.rank_finite
  coord := shiftCoord c gauge.coord

/-- Reverse the sign of every observer coordinate. -/
def negateCoord {N : Nat} (coord : CoordMap N) : CoordMap N where
  values := fun v => -coord.values v

/-- Retain the projection exactly while reversing its coordinate field. -/
noncomputable def negateGauge {N : Nat}
    (gauge : ObserverGauge N) : ObserverGauge N where
  projection := gauge.projection
  is_idempotent := gauge.is_idempotent
  rank_finite := gauge.rank_finite
  coord := negateCoord gauge.coord

@[simp] theorem shiftGauge_projection {N : Nat} (c : Real)
    (gauge : ObserverGauge N) :
    (shiftGauge c gauge).toCandidateGauge = gauge.toCandidateGauge :=
  rfl

@[simp] theorem negateGauge_projection {N : Nat}
    (gauge : ObserverGauge N) :
    (negateGauge gauge).toCandidateGauge = gauge.toCandidateGauge :=
  rfl

/-! ## Exact invariance of the concrete action -/

/-- The complete concrete N-frame action is invariant under a global
coordinate translation.  This holds for every graph and every choice of
couplings; no expansion hypothesis is relevant. -/
theorem fullLagrangianFixed_shift_invariant
    {N d : Nat} (alpha beta gamma c : Real)
    (G : RegularGraphFixed N d) (gauge : ObserverGauge N) :
    fullLagrangianFixed alpha beta gamma G (shiftGauge c gauge) =
      fullLagrangianFixed alpha beta gamma G gauge := by
  unfold fullLagrangianFixed
  have hEnergy :
      (∑ e ∈ G.edges,
        ((shiftGauge c gauge).coord.values e.1 -
          (shiftGauge c gauge).coord.values e.2) ^ 2) =
        ∑ e ∈ G.edges,
          (gauge.coord.values e.1 - gauge.coord.values e.2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro e he
    dsimp [shiftGauge, shiftCoord]
    ring
  rw [hEnergy]
  rfl

/-- Squared Ramanujan edge differences also make the complete concrete action
invariant under global sign reversal. -/
theorem fullLagrangianFixed_negate_invariant
    {N d : Nat} (alpha beta gamma : Real)
    (G : RegularGraphFixed N d) (gauge : ObserverGauge N) :
    fullLagrangianFixed alpha beta gamma G (negateGauge gauge) =
      fullLagrangianFixed alpha beta gamma G gauge := by
  unfold fullLagrangianFixed
  have hEnergy :
      (∑ e ∈ G.edges,
        ((negateGauge gauge).coord.values e.1 -
          (negateGauge gauge).coord.values e.2) ^ 2) =
        ∑ e ∈ G.edges,
          (gauge.coord.values e.1 - gauge.coord.values e.2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro e he
    dsimp [negateGauge, negateCoord]
    ring
  rw [hEnergy]
  rfl

/-! ## Concrete collisions -/

/-- On a nonempty vertex set, translation by one genuinely changes every
observer gauge's coordinate field. -/
theorem shiftGauge_one_ne
    {N : Nat} (hN : 0 < N) (gauge : ObserverGauge N) :
    shiftGauge 1 gauge ≠ gauge := by
  intro h
  let v : Fin N := ⟨0, hN⟩
  have hv := congrArg (fun g : ObserverGauge N => g.coord.values v) h
  dsimp [shiftGauge, shiftCoord] at hv
  linarith

/-- Hence the full concrete action is never injective on observer gauges for a
nonempty graph, independently of expansion, the identity minor, or couplings. -/
theorem fullLagrangianFixed_not_injective
    {N d : Nat} (hN : 0 < N) (alpha beta gamma : Real)
    (G : RegularGraphFixed N d) :
    ¬ Function.Injective (fullLagrangianFixed alpha beta gamma G) := by
  intro hInjective
  let gauge := trivialObserverGauge N
  exact shiftGauge_one_ne hN gauge
    (hInjective (fullLagrangianFixed_shift_invariant
      alpha beta gamma 1 G gauge))

/-! ## The exact role of the missing orientation term -/

/-- Add an arbitrary parity/orientation term to the existing concrete core. -/
noncomputable def orientedRamanujanAction
    {N d : Nat} (alpha beta gamma : Real) (G : RegularGraphFixed N d)
    (orientation : ObserverGauge N -> Real) (gauge : ObserverGauge N) : Real :=
  fullLagrangianFixed alpha beta gamma G gauge + orientation gauge

/-- If the augmented action distinguishes a translated pair, the added
orientation term must distinguish it.  The Ramanujan edge energy, rank, and
log-det terms contribute exactly zero to this distinction. -/
theorem translation_separation_requires_orientation
    {N d : Nat} (alpha beta gamma c : Real)
    (G : RegularGraphFixed N d) (orientation : ObserverGauge N -> Real)
    (gauge : ObserverGauge N)
    (hSeparate :
      orientedRamanujanAction alpha beta gamma G orientation (shiftGauge c gauge) ≠
        orientedRamanujanAction alpha beta gamma G orientation gauge) :
    orientation (shiftGauge c gauge) ≠ orientation gauge := by
  intro hOrientation
  apply hSeparate
  unfold orientedRamanujanAction
  rw [fullLagrangianFixed_shift_invariant, hOrientation]

/-- Even after fixing translation freedom, separation of a sign-reversed pair
must likewise be supplied by the orientation/parity term. -/
theorem sign_separation_requires_orientation
    {N d : Nat} (alpha beta gamma : Real)
    (G : RegularGraphFixed N d) (orientation : ObserverGauge N -> Real)
    (gauge : ObserverGauge N)
    (hSeparate :
      orientedRamanujanAction alpha beta gamma G orientation (negateGauge gauge) ≠
        orientedRamanujanAction alpha beta gamma G orientation gauge) :
    orientation (negateGauge gauge) ≠ orientation gauge := by
  intro hOrientation
  apply hSeparate
  unfold orientedRamanujanAction
  rw [fullLagrangianFixed_negate_invariant, hOrientation]

end PallLean.Paper93.DeepMath.PathB.NFrameRamanujanActionSymmetryAudit

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanActionSymmetryAudit.fullLagrangianFixed_shift_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanActionSymmetryAudit.fullLagrangianFixed_negate_invariant
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanActionSymmetryAudit.fullLagrangianFixed_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameRamanujanActionSymmetryAudit.translation_separation_requires_orientation
