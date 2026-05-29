import PallLean.Paper93.DeepMath.PathB.ComputationalDepthThresholdCompositionFrontier

/-!
# Layered threshold invariants: the honest climb shape

**STATUS: CONDITIONAL FRAMEWORK, NOT A TC⁰ LOWER BOUND.**

A single invariant such as sign-rank controls the depth-2 / UPP bottleneck, but
there is no known theorem saying it survives arbitrary threshold composition.
The honest way to phrase a possible climb is a *layered* invariant system:

```text
I₀, I₁, I₂, ...
```

with transfer rules

```text
threshold of I_d-bounded children  ⇒  I_{d+1}-bounded parent.
```

This file formalizes exactly that.  The main theorem is a real induction over
layered threshold circuits: if the base layer and all transfer rules are supplied,
then every depth-`d` threshold circuit is controlled by `I_d`.

The file does **not** supply the hard transfer rules for TC⁰.  Those rules are the
open problem.  This is a clean target/interface for future real invariants, not a
filled rung.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace ThresholdLayer

/-- A hierarchy of observer invariants, one for each threshold depth. -/
structure LayeredInvariant (n : Nat) where
  I : Nat -> TCObserverInvariant n

/-- Depth-indexed budgets for a layered invariant hierarchy.  `B d` bounds the
allowed value of invariant `I_d` at depth `d`. -/
abbrev LayerBudget := Nat -> Nat

/-- Base-layer preservation: variables and constants are bounded by the depth-0
invariant and budget. -/
def LayeredLeafPreserved {n : Nat} (L : LayeredInvariant n) (B : LayerBudget) : Prop :=
  (∀ i : Fin n, (L.I 0).Q (eval (var i)) ≤ B 0) ∧
  (∀ b : Bool, (L.I 0).Q (eval (cst b)) ≤ B 0)

/-- Layer transfer rule.  If every child at depth `d` is bounded by invariant
`I_d`, then any threshold gate over those children is bounded by invariant
`I_{d+1}`.

This is the honest hard part of the climb.  For full TC⁰, supplying these rules
for a non-natural hierarchy and an explicit hard target is the open breakthrough. -/
def LayerTransferStable {n : Nat} (L : LayeredInvariant n) (B : LayerBudget) : Prop :=
  ∀ {d fanin : Nat} (θ : Nat) (child : Fin fanin -> ThresholdLayer n d),
    (∀ i, (L.I d).Q (eval (child i)) ≤ B d) ->
      (L.I (d + 1)).Q (eval (gate θ child)) ≤ B (d + 1)

/-- Finite-prefix layer transfer.  To rule out depth `D` circuits, one does not
need an infinite hierarchy of transfer theorems; it is enough to prove the steps
`0 → 1`, ..., `D-1 → D`.  This is the practical "climb the ladder one rung at a
time" interface. -/
def LayerTransferStableUpTo {n : Nat}
    (L : LayeredInvariant n) (B : LayerBudget) (D : Nat) : Prop :=
  ∀ {d fanin : Nat}, d < D -> (θ : Nat) ->
    (child : Fin fanin -> ThresholdLayer n d) ->
      (∀ i, (L.I d).Q (eval (child i)) ≤ B d) ->
        (L.I (d + 1)).Q (eval (gate θ child)) ≤ B (d + 1)

/-- Global layer transfer immediately gives any finite prefix. -/
theorem layerTransferStableUpTo_of_global {n : Nat}
    (L : LayeredInvariant n) (B : LayerBudget) (D : Nat)
    (htransfer : LayerTransferStable L B) :
    LayerTransferStableUpTo L B D := by
  intro d fanin _ θ child hchild
  exact htransfer θ child hchild

/-- **Layered composition theorem.**  A base bound plus transfer rules controls
every layered threshold circuit at its own depth.  This is the formal climb
principle for a changing/enriched invariant hierarchy `I₀, I₁, ...`. -/
theorem layered_threshold_preservation {n : Nat}
    (L : LayeredInvariant n) (B : LayerBudget)
    (hleaf : LayeredLeafPreserved L B)
    (htransfer : LayerTransferStable L B) :
    ∀ {d : Nat} (C : ThresholdLayer n d), (L.I d).Q (eval C) ≤ B d := by
  intro d C
  induction C with
  | var i => exact hleaf.1 i
  | cst b => exact hleaf.2 b
  | gate θ child ih =>
      exact htransfer θ child ih

/-- **Finite-prefix layered composition theorem.**  Depth `D` lower-bound work
can be climbed one step at a time: leaf preservation plus transfer only below
`D` controls every circuit of depth at most `D`. -/
theorem layered_threshold_preservation_upTo {n D : Nat}
    (L : LayeredInvariant n) (B : LayerBudget)
    (hleaf : LayeredLeafPreserved L B)
    (htransfer : LayerTransferStableUpTo L B D) :
    ∀ {d : Nat}, d ≤ D -> ∀ (C : ThresholdLayer n d), (L.I d).Q (eval C) ≤ B d := by
  intro d hD C
  induction C with
  | var i => exact hleaf.1 i
  | cst b => exact hleaf.2 b
  | gate θ child ih =>
      have hd : _ := Nat.lt_of_succ_le hD
      exact htransfer hd θ child (fun i => ih i (Nat.le_of_lt hd))

/-- A target gap at layer `d`: the explicit target exceeds the allowed budget for
invariant `I_d`. -/
def LayeredTargetGap {n : Nat} (L : LayeredInvariant n) (B : LayerBudget)
    (f : BoolFun n) (d : Nat) : Prop :=
  B d < (L.I d).Q f

/-- If the layered invariant hierarchy preserves all depth-`d` circuits but the
target has a depth-`d` gap, then no depth-`d` layered threshold circuit computes
that target. -/
theorem no_thresholdLayer_of_layered_gap {n d : Nat}
    (L : LayeredInvariant n) (B : LayerBudget)
    (hleaf : LayeredLeafPreserved L B)
    (htransfer : LayerTransferStable L B)
    {f : BoolFun n}
    (hgap : LayeredTargetGap L B f d) :
    ¬ ∃ C : ThresholdLayer n d, eval C = f := by
  rintro ⟨C, hCf⟩
  have hpres := layered_threshold_preservation L B hleaf htransfer C
  rw [hCf] at hpres
  exact Nat.not_lt.mpr hpres hgap

/-- Finite-prefix version: to rule out depth `d`, transfer rules only below `d`
are required. -/
theorem no_thresholdLayer_of_layered_gap_upTo {n d : Nat}
    (L : LayeredInvariant n) (B : LayerBudget)
    (hleaf : LayeredLeafPreserved L B)
    (htransfer : LayerTransferStableUpTo L B d)
    {f : BoolFun n}
    (hgap : LayeredTargetGap L B f d) :
    ¬ ∃ C : ThresholdLayer n d, eval C = f := by
  rintro ⟨C, hCf⟩
  have hpres := layered_threshold_preservation_upTo (D := d) L B hleaf htransfer (Nat.le_refl d) C
  rw [hCf] at hpres
  exact Nat.not_lt.mpr hpres hgap

/-- A completed layered route for one target/depth.  To prove a real depth-`d`
threshold lower bound by this route, one must instantiate every field with
non-vacuous mathematics, especially `transfer_stable` and `target_gap`. -/
structure LayeredThresholdRoute {n : Nat} (f : BoolFun n) (d : Nat) where
  L : LayeredInvariant n
  B : LayerBudget
  leaf_preserved : LayeredLeafPreserved L B
  transfer_stable : LayerTransferStable L B
  target_gap : LayeredTargetGap L B f d

/-- A finite-depth route: only the transfer steps needed up to the target depth
are required.  This is the operational version for incremental formalization. -/
structure LayeredThresholdRouteUpTo {n : Nat} (f : BoolFun n) (d : Nat) where
  L : LayeredInvariant n
  B : LayerBudget
  leaf_preserved : LayeredLeafPreserved L B
  transfer_stable_upTo : LayerTransferStableUpTo L B d
  target_gap : LayeredTargetGap L B f d

/-- Any completed layered route gives the lower-bound conclusion. -/
theorem lower_bound_of_layeredThresholdRoute {n d : Nat}
    {f : BoolFun n} (R : LayeredThresholdRoute f d) :
    ¬ ∃ C : ThresholdLayer n d, eval C = f :=
  no_thresholdLayer_of_layered_gap R.L R.B R.leaf_preserved R.transfer_stable R.target_gap

/-- Any completed finite-depth route gives the same lower-bound conclusion. -/
theorem lower_bound_of_layeredThresholdRouteUpTo {n d : Nat}
    {f : BoolFun n} (R : LayeredThresholdRouteUpTo f d) :
    ¬ ∃ C : ThresholdLayer n d, eval C = f :=
  no_thresholdLayer_of_layered_gap_upTo R.L R.B R.leaf_preserved
    R.transfer_stable_upTo R.target_gap

/-- A global route can always be viewed as a finite-depth route. -/
def layeredThresholdRouteUpTo_of_global {n d : Nat}
    {f : BoolFun n} (R : LayeredThresholdRoute f d) :
    LayeredThresholdRouteUpTo f d where
  L := R.L
  B := R.B
  leaf_preserved := R.leaf_preserved
  transfer_stable_upTo := layerTransferStableUpTo_of_global R.L R.B d R.transfer_stable
  target_gap := R.target_gap

/-- Constant-invariant hierarchies recover the one-invariant threshold-composition
framework as a special case.  This is useful for checking that the layered system
strictly generalizes the previous signpost rather than replacing it. -/
def constantLayeredInvariant {n : Nat} (I : TCObserverInvariant n) : LayeredInvariant n where
  I := fun _ => I

/-- A one-invariant transfer rule induces the layered transfer rule for the
constant hierarchy. -/
theorem layerTransferStable_of_thresholdLayerStable {n : Nat}
    (I : TCObserverInvariant n) (B : LayerBudget)
    (hstable : ThresholdLayerStable I B) :
    LayerTransferStable (constantLayeredInvariant I) B := by
  intro d fanin θ child hchild
  exact hstable θ child hchild

/-- The old one-invariant preservation theorem is recovered from the layered
framework by taking `I_d = I` for every `d`. -/
theorem thresholdCircuit_preservation_from_layered_constant {n : Nat}
    (I : TCObserverInvariant n) (B : LayerBudget)
    (hleaf : LeafPreserved I B)
    (hstable : ThresholdLayerStable I B) :
    ∀ {d : Nat} (C : ThresholdLayer n d), I.Q (eval C) ≤ B d := by
  intro d C
  exact layered_threshold_preservation (constantLayeredInvariant I) B hleaf
    (layerTransferStable_of_thresholdLayerStable I B hstable) C

/-- The exact future target for depth `d`: produce a non-natural layered invariant
hierarchy with transfer rules and an explicit target gap.  This is intentionally a
target definition, not a proof that such a hierarchy exists. -/
def LayeredTC0Target {n : Nat} (f : BoolFun n) (d : Nat) : Prop :=
  Nonempty (LayeredThresholdRoute f d)

#print axioms layered_threshold_preservation
#print axioms layered_threshold_preservation_upTo
#print axioms no_thresholdLayer_of_layered_gap
#print axioms no_thresholdLayer_of_layered_gap_upTo
#print axioms lower_bound_of_layeredThresholdRoute
#print axioms lower_bound_of_layeredThresholdRouteUpTo
#print axioms thresholdCircuit_preservation_from_layered_constant

end ThresholdLayer

end PallLean.Paper93.DeepMath.PathB
