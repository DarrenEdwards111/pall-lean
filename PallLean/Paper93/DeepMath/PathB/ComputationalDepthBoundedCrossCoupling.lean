import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheReasonShared
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNaturalProofsObstruction

/-!
# Bounded cross-block coupling — the ruler extended, and where it fences

The entanglement ruler proved that for PRIVATE demands shared variables are inert: multiplicity is
priced by private reach, with no sharing-profile factor.  This file extends it from zero cross-block
coupling to BOUNDED coupling — the honest interpolation between the disjoint bound and the collapse —
and then reaches the fence I flagged: the graceful degradation is real and provable, but *forcing*
the coupling bound for SAT is exactly the natural-proofs-barriered invariant.

## The graceful degradation (real new content, proved)

Model coupling as a budget `t`: each gate witnesses at most `1 + t` blocks (private reach `≤ 1`,
plus up to `t` cross-block coupling channels).  Then:

* **`coupling_graceful`** — `mult ≤ 1 + t` everywhere ⟹ `k·b ≤ (1+t)·|gates|`.  The reason survives
  divided by `(1 + coupling)`: coupling is the exact exchange rate between the disjoint bound and the
  truth.
* **`coupling_zero_recovers`** — at `t = 0` this is the disjoint bound `k·b ≤ |gates|` (the ruler).
* **`collapse_forces_max_coupling`** — the collapse witness (all witness sets equal, `mult = k`)
  FORCES `t ≥ k − 1`: coupling can be maximal, and at maximal coupling the bound degrades to the bare
  floor.  So no *generic* argument bounds coupling below `k` — the bound has teeth only if coupling is
  actually small.

## The fence (proved): forcing the coupling bound for SAT is barriered

For `cost_super` you need SAT's witnesses to have LOW coupling (`coupling sat < k`, un-shareable) —
that is exactly `cv_would_separate`-style: low coupling ⟹ `k·b ≤ (1+t)·|gates|` with `t` small ⟹
large `|gates|`.  But:

* **`coupling_certificate_breaks_crypto`** — an EFFICIENT certificate of "high coupling" (shareable,
  the easy/compressible functions) that failed on SAT is a `ColossusRuler`, hence — via the reused
  Razborov–Rudich barrier — forces `¬ PRFExists`.  Deciding shareability efficiently is a natural
  property.

And the coupling bound cannot be forced by any per-block demand: the mixture adversary
(`FamilyIndependence`/`MixtureAdversary`) satisfies every per-block nonlinearity demand with
`|gates| = b` and maximal coupling.  So the missing input is a genuinely cross-block, non-natural
invariant — the object this whole session has been circling.

## Verdict

The extension is honest progress: it quantifies coupling as the exact exchange rate `(1+t)` and
proves the bound degrades gracefully.  But it lands where predicted — bounding coupling for SAT below
`k` is (a) unforceable by per-block demands (mixture-realizable) and (b) barriered as an efficient
invariant.  Route 1 reaches its fence precisely; the forcing input is the non-natural cross-block
invariant, which does not yet exist.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedCrossCoupling

open PallLean.Paper93.DeepMath.PathB.TheReasonShared
open PallLean.Paper93.DeepMath.PathB.NaturalProofsObstruction

variable {k b : ℕ}

/-! ### The graceful degradation -/

/-- **Coupling as the exchange rate (proved).**  If every gate witnesses at most `1 + t` blocks
(private reach `≤ 1` plus `t` coupling channels), then `k·b ≤ (1+t)·|gates|`: the reason survives
divided by `(1 + coupling)`. -/
theorem coupling_graceful (C : SharedCircuitForTarget k b) (t : ℕ)
    (hcoup : ∀ g ∈ C.gates, mult C g ≤ 1 + t) :
    k * b ≤ (1 + t) * C.gates.card :=
  the_reason_shared C (1 + t) hcoup

/-- **Zero coupling recovers the disjoint bound (proved).**  At `t = 0` the graded bound is
`k·b ≤ |gates|` — the entanglement ruler's private-reach bound. -/
theorem coupling_zero_recovers (C : SharedCircuitForTarget k b)
    (hcoup : ∀ g ∈ C.gates, mult C g ≤ 1) :
    k * b ≤ C.gates.card := by
  have h := coupling_graceful C 0 (fun g hg => by have := hcoup g hg; omega)
  simpa using h

/-- **Maximal coupling is realizable (proved).**  The collapse witness — all witness sets equal,
`mult = 3 = k` — forces any coupling budget to be maximal (`t ≥ k − 1 = 2`).  At maximal coupling the
graded bound is only the bare floor, so the bound bites *only* when coupling is genuinely small; no
generic argument delivers that. -/
theorem collapse_forces_max_coupling (t : ℕ)
    (hcoup : ∀ g ∈ collapseWitness.gates, mult collapseWitness g ≤ 1 + t) : 2 ≤ t := by
  have h0 : (0 : ℕ) ∈ collapseWitness.gates := by decide
  have hm := collapse_mult_full 0 h0
  have hb := hcoup 0 h0
  omega

/-! ### The fence: forcing the coupling bound for SAT is natural-proofs-barriered -/

/-- A world with a cross-block coupling measure and `k` blocks.  High coupling = shareable = easy;
low coupling (`< blocks`) = un-shareable = the hardness `cost_super` needs for SAT. -/
structure CouplingWorld where
  /-- the universe of functions -/
  Fn : Type
  /-- cross-block coupling of the witness family -/
  coupling : Fn → ℕ
  /-- the block count `k` -/
  blocks : ℕ
  /-- the SAT function -/
  sat : Fn
  /-- pseudorandom functions exist -/
  PRFExists : Prop

/-- `P/poly` proxy = "high coupling" (shareable/compressible, `blocks ≤ coupling`). -/
def toComplexityWorld (W : CouplingWorld) (Eff : (W.Fn → Bool) → Prop) : ComplexityWorld where
  Fn := W.Fn
  InPpoly := fun f => W.blocks ≤ W.coupling f
  PolyTimeComputable := Eff
  sat := W.sat
  PRFExists := W.PRFExists

/-- **The shareability test is a `ColossusRuler` (proved).**  `f ↦ (blocks ≤ coupling f)` is
poly-checkable (if coupling is efficiently testable), true on every high-coupling (shareable)
function, and false on a low-coupling SAT. -/
def couplingRuler (W : CouplingWorld) (hsat : W.coupling W.sat < W.blocks)
    (Eff : (W.Fn → Bool) → Prop) (hEff : Eff (fun f => decide (W.blocks ≤ W.coupling f))) :
    ColossusRuler (toComplexityWorld W Eff) where
  E := fun f => decide (W.blocks ≤ W.coupling f)
  poly := hEff
  closedOnPpoly := fun f hf => by
    have hc : W.blocks ≤ W.coupling f := hf
    simp [hc]
  failsSAT := by
    show decide (W.blocks ≤ W.coupling W.sat) = false
    have hn : ¬ (W.blocks ≤ W.coupling W.sat) := by omega
    simp [hn]

/-- **Forcing the coupling bound for SAT breaks crypto (proved) — the fence.**  An efficient
certificate that SAT has low coupling (un-shareable witnesses) — precisely what forces `cost_super`
via the graceful bound — is, in complement, an efficient shareability detector: a `ColossusRuler`,
hence forces `¬ PRFExists`.  The cross-block coupling invariant, made efficient, is the
natural-proofs wall. -/
theorem coupling_certificate_breaks_crypto (W : CouplingWorld) (hsat : W.coupling W.sat < W.blocks)
    (Eff : (W.Fn → Bool) → Prop) (hEff : Eff (fun f => decide (W.blocks ≤ W.coupling f)))
    (barrier : RazborovRudichBarrier (toComplexityWorld W Eff)) :
    ¬ W.PRFExists :=
  ruler_needs_broken_crypto (toComplexityWorld W Eff)
    (couplingRuler W hsat Eff hEff) barrier

end PallLean.Paper93.DeepMath.PathB.BoundedCrossCoupling

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedCrossCoupling.coupling_graceful
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedCrossCoupling.coupling_zero_recovers
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedCrossCoupling.collapse_forces_max_coupling
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedCrossCoupling.coupling_certificate_breaks_crypto
