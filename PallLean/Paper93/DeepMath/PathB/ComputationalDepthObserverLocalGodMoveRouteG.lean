import Mathlib.Data.Nat.Basic

/-!
# Observer-local Route G

This file states the non-circular shape that a rebuilt Route G must have.

The construction follows the observer-centric reading in N-Frame Book 1:

* rank is not an unqualified rank of the inaccessible bulk; it is the rank exposed
  through one fixed observer frame;
* the P-side compilation and the hard target are compared in that same frame;
* the God-Move is local to the compiled instance produced under `P = NP`;
* its overhead is explicit rather than hidden behind global rank monotonicity.

The theorem below is only the logical beam.  It does not construct the local
transport.  The load-bearing research obligation is `buildLocalMove`: it must be
implemented from the assumed polynomial solver and the physical compiler, without
using the target separation, the outside lower bound, or a frontier hypothesis.

This corrects two earlier failure modes:

1. a global rank-nonincreasing extractor, whose existence can encode the desired
   separation; and
2. comparing ranks reported by unrelated observer projections.

Nothing in this file proves `P != NP` by itself.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverLocalGodMoveRouteG

/-- One N-Frame observer projection.  Every rank comparison in the local route is
made through this single projection. -/
structure ObserverFrame (Obj : Type*) where
  accessibleRank : Obj → ℕ

/-- An instance-specific God-Move inside one observer frame.

`transport` is visible data, `landsOnTarget` identifies the transported object, and
`rankOverhead` gives the exact resource loss allowed by the construction. -/
structure LocalGodMove {Obj : Type*} (F : ObserverFrame Obj)
    (source target : Obj) (overhead : ℕ) where
  transport : Obj → Obj
  landsOnTarget : transport source = target
  rankOverhead :
    F.accessibleRank (transport source) ≤ F.accessibleRank source + overhead

/-- The local move transports the target's observer-accessible rank back to the
source, with precisely the declared overhead. -/
theorem target_rank_le_source_add_overhead {Obj : Type*}
    {F : ObserverFrame Obj} {source target : Obj} {overhead : ℕ}
    (E : LocalGodMove F source target overhead) :
    F.accessibleRank target ≤ F.accessibleRank source + overhead := by
  simpa [E.landsOnTarget] using E.rankOverhead

/-- Complete data surface for the rebuilt observer-local Route G.

The proposition `Collapse` is the formal `P = NP` assumption.  The source object is
therefore allowed to depend on a proof of collapse: operationally it is the concrete
compiled object obtained from the polynomial solver supplied by that assumption.

Crucially, `buildLocalMove` also depends only on that collapse witness.  The lower
bound is a separate field and is not an input to construction of the move. -/
structure RouteGData (Collapse : Prop) where
  Obj : Type*
  frame : ObserverFrame Obj
  source : Collapse → Obj
  target : Collapse → Obj
  sourceCap : ℕ
  targetFloor : ℕ
  overhead : ℕ
  gap : sourceCap + overhead < targetFloor
  insideLow : ∀ h : Collapse, frame.accessibleRank (source h) ≤ sourceCap
  buildLocalMove : ∀ h : Collapse,
    LocalGodMove frame (source h) (target h) overhead
  outsideHigh : ∀ h : Collapse, targetFloor ≤ frame.accessibleRank (target h)

/-- The observer-consistent local Route G beam.

Assuming collapse constructs one source and one explicit local transport.  Because
both endpoint ranks are measured through the same observer frame, the transported
lower bound and the P-side upper bound form a genuine inequality chain. -/
theorem routeG_refutes_collapse {Collapse : Prop} (G : RouteGData Collapse) :
    ¬ Collapse := by
  intro h
  have htransport :
      G.frame.accessibleRank (G.target h) ≤
        G.frame.accessibleRank (G.source h) + G.overhead :=
    target_rank_le_source_add_overhead (G.buildLocalMove h)
  have hupper :
      G.frame.accessibleRank (G.source h) + G.overhead ≤
        G.sourceCap + G.overhead :=
    Nat.add_le_add_right (G.insideLow h) G.overhead
  have hlower := G.outsideHigh h
  have hgap := G.gap
  omega

/-- Pointwise audit lemma: at a scale where the lower bound exceeds the source
budget plus overhead, no such observer-local move can exist.  This is useful when
testing candidate constructions before wiring them into `RouteGData`. -/
theorem no_local_move_across_proved_gap {Obj : Type*}
    (F : ObserverFrame Obj) (source target : Obj) (low high overhead : ℕ)
    (hsource : F.accessibleRank source ≤ low)
    (htarget : high ≤ F.accessibleRank target)
    (hgap : low + overhead < high) :
    ¬ Nonempty (LocalGodMove F source target overhead) := by
  rintro ⟨E⟩
  have htransport := target_rank_le_source_add_overhead E
  omega

end PallLean.Paper93.DeepMath.PathB.ObserverLocalGodMoveRouteG

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverLocalGodMoveRouteG.target_rank_le_source_add_overhead
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverLocalGodMoveRouteG.routeG_refutes_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverLocalGodMoveRouteG.no_local_move_across_proved_gap
