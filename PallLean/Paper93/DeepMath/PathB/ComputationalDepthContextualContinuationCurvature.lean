import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNoncommutativeActionHolonomyAudit

/-!
# Contextual continuation curvature: nested observer bubbles

The preceding holonomy audit used one globally fixed Boolean residual fiber.
That cube is exponentially large but globally trivial: coordinate transport is
commuting, succinct, and path independent.  This file formalizes the next
Route-G object suggested by the N-Frame "bubbles within bubbles" picture.

An observer bubble is represented by a context.  Its fiber is the information
that remains operationally distinguishable in that context.  A local square
compares two nested routes from one outer context to a common inner context.
Curvature is disagreement of the induced observations at the common endpoint.
It is therefore an obstruction to a single observer-compatible global
trivialization, rather than merely a count of latent states.

The file proves three calibration facts:

* any observer-compatible global trivialization forces every local square flat;
* the old Boolean residual hypercube is flat, exactly as the previous audit found;
* context-dependent projection can have genuine nonzero curvature, even in a
  four-context finite toy system with different fibers at different bubbles.

The toy system establishes non-vacuity only.  It is deliberately not presented
as a SAT lower bound.  A P-versus-NP consequence would still require an
independent polynomial conservation theorem for all polynomial-time traces and
a superpolynomial forcing theorem for a solver-independent SAT family.
-/

namespace PallLean.Paper93.DeepMath.PathB.ContextualContinuationCurvature

open NoncommutativeActionHolonomyAudit

universe u v

/-- The four contexts of a local nested-bubble square.  The two middle bubbles
are alternative refinements of the outer bubble and share an inner endpoint. -/
structure BubbleSquare (Context : Type u) where
  outer : Context
  left : Context
  right : Context
  inner : Context

/-- Information visible to an observer depends on its current context. -/
structure ContextualBundle (Context : Type u) where
  Fiber : Context → Type v

/-- Four context-sensitive transports around one local square.  No functorial
law is assumed: path independence is the property being measured. -/
structure LocalTransport {Context : Type u}
    (B : ContextualBundle Context) (S : BubbleSquare Context) where
  outerLeft : B.Fiber S.outer → B.Fiber S.left
  outerRight : B.Fiber S.outer → B.Fiber S.right
  leftInner : B.Fiber S.left → B.Fiber S.inner
  rightInner : B.Fiber S.right → B.Fiber S.inner

def leftComposite {Context : Type u} {B : ContextualBundle Context}
    {S : BubbleSquare Context} (T : LocalTransport B S) :
    B.Fiber S.outer → B.Fiber S.inner :=
  fun x ↦ T.leftInner (T.outerLeft x)

def rightComposite {Context : Type u} {B : ContextualBundle Context}
    {S : BubbleSquare Context} (T : LocalTransport B S) :
    B.Fiber S.outer → B.Fiber S.inner :=
  fun x ↦ T.rightInner (T.outerRight x)

/-- Local contextual flatness: both nested routes induce the same effective
observation in the common inner bubble. -/
def Flat {Context : Type u} {B : ContextualBundle Context}
    {S : BubbleSquare Context} (T : LocalTransport B S) : Prop :=
  ∀ x, leftComposite T x = rightComposite T x

/-- Curvature at an outer state is path dependence after both routes arrive at
the same inner context. -/
def CurvedAt {Context : Type u} {B : ContextualBundle Context}
    {S : BubbleSquare Context} (T : LocalTransport B S)
    (x : B.Fiber S.outer) : Prop :=
  leftComposite T x ≠ rightComposite T x

/-- A local observer-compatible trivialization is a common outer-to-inner
meaning with which both contextual routes agree. -/
structure ObserverCompatibleTrivialization {Context : Type u}
    {B : ContextualBundle Context} {S : BubbleSquare Context}
    (T : LocalTransport B S) where
  globalMeaning : B.Fiber S.outer → B.Fiber S.inner
  left_agrees : ∀ x, leftComposite T x = globalMeaning x
  right_agrees : ∀ x, rightComposite T x = globalMeaning x

/-- Global observer-compatible meaning eliminates contextual holonomy. -/
theorem flat_of_trivialization {Context : Type u}
    {B : ContextualBundle Context} {S : BubbleSquare Context}
    {T : LocalTransport B S}
    (h : ObserverCompatibleTrivialization T) : Flat T := by
  intro x
  exact (h.left_agrees x).trans (h.right_agrees x).symm

/-- Nonzero contextual curvature obstructs a global observer-compatible
trivialization. -/
theorem no_trivialization_of_curvedAt {Context : Type u}
    {B : ContextualBundle Context} {S : BubbleSquare Context}
    {T : LocalTransport B S} {x : B.Fiber S.outer}
    (hcurved : CurvedAt T x) :
    ¬ Nonempty (ObserverCompatibleTrivialization T) := by
  rintro ⟨h⟩
  exact hcurved (flat_of_trivialization h x)

/-- Finite local thermodynamic deficit: the number of outer states on which
the two context routes remain operationally distinguishable. -/
def contextualDeficit {Context : Type u} {B : ContextualBundle Context}
    {S : BubbleSquare Context} (T : LocalTransport B S)
    [Fintype (B.Fiber S.outer)] [DecidableEq (B.Fiber S.inner)] : ℕ :=
  (Finset.univ.filter fun x ↦ leftComposite T x ≠ rightComposite T x).card

theorem contextualDeficit_eq_zero_iff_flat {Context : Type u}
    {B : ContextualBundle Context} {S : BubbleSquare Context}
    (T : LocalTransport B S)
    [Fintype (B.Fiber S.outer)] [DecidableEq (B.Fiber S.inner)] :
    contextualDeficit T = 0 ↔ Flat T := by
  simp [contextualDeficit, Flat, leftComposite, rightComposite]

/-! ## Flat hypercube calibration -/

def cubeContexts : BubbleSquare (Fin 4) where
  outer := 0
  left := 1
  right := 2
  inner := 3

def constantCubeBundle (r : ℕ) : ContextualBundle (Fin 4) where
  Fiber := fun _ ↦ Assignment r

instance constantCubeFiberFintype (r : ℕ) (c : Fin 4) :
    Fintype ((constantCubeBundle r).Fiber c) := by
  dsimp [constantCubeBundle]
  infer_instance

instance constantCubeFiberDecidableEq (r : ℕ) (c : Fin 4) :
    DecidableEq ((constantCubeBundle r).Fiber c) := by
  dsimp [constantCubeBundle]
  infer_instance

/-- The old coordinate cube viewed as a contextual square. -/
def coordinateCubeTransport {r : ℕ}
    (i j : Fin r) (a b : Fin 2) :
    LocalTransport (constantCubeBundle r) cubeContexts where
  outerLeft := coordinateAction i a
  outerRight := coordinateAction j b
  leftInner := coordinateAction j b
  rightInner := coordinateAction i a

/-- The full Boolean residual cube has zero contextual curvature because its
coordinate transports commute. -/
theorem coordinateCubeTransport_flat {r : ℕ}
    (i j : Fin r) (a b : Fin 2) :
    Flat (coordinateCubeTransport i j a b) := by
  intro state
  exact (coordinateAction_commute i j a b state).symm

theorem coordinateCube_contextualDeficit_eq_zero {r : ℕ}
    (i j : Fin r) (a b : Fin 2) :
    contextualDeficit (coordinateCubeTransport i j a b) = 0 := by
  exact (contextualDeficit_eq_zero_iff_flat _).2
    (coordinateCubeTransport_flat i j a b)

/-! ## A genuinely context-dependent non-flat finite model -/

inductive ToyContext
  | outer
  | leftBubble
  | rightBubble
  | inner
  deriving DecidableEq, Fintype

def toySquare : BubbleSquare ToyContext where
  outer := .outer
  left := .leftBubble
  right := .rightBubble
  inner := .inner

/-- Different bubbles retain differently shaped observer-visible data. -/
def toyFiber : ToyContext → Type
  | .outer => Bool
  | .leftBubble => Bool × Unit
  | .rightBubble => Unit × Bool
  | .inner => Bool

def toyBundle : ContextualBundle ToyContext where
  Fiber := toyFiber

instance toyFiberFintype (c : ToyContext) : Fintype (toyFiber c) := by
  cases c <;> simp [toyFiber] <;> infer_instance

instance toyFiberDecidableEq (c : ToyContext) : DecidableEq (toyFiber c) := by
  cases c <;> simp [toyFiber] <;> infer_instance

instance toyBundleFiberFintype (c : ToyContext) :
    Fintype (toyBundle.Fiber c) := by
  change Fintype (toyFiber c)
  infer_instance

instance toyBundleFiberDecidableEq (c : ToyContext) :
    DecidableEq (toyBundle.Fiber c) := by
  change DecidableEq (toyFiber c)
  infer_instance

/-- The left refinement preserves the latent bit while the right refinement
records it in a context whose final interpretation reverses polarity.  This is
a minimal model of operational meaning changing with the observation context. -/
def toyTransport : LocalTransport toyBundle toySquare where
  outerLeft := fun b ↦ (b, ())
  outerRight := fun b ↦ ((), b)
  leftInner := fun p ↦ p.1
  rightInner := fun p ↦ !p.2

theorem toy_curvedAt_false : CurvedAt toyTransport false := by
  simp [CurvedAt, leftComposite, rightComposite, toyTransport,
    toyBundle, toySquare, toyFiber]

theorem toy_curvedAt_true : CurvedAt toyTransport true := by
  simp [CurvedAt, leftComposite, rightComposite, toyTransport,
    toyBundle, toySquare, toyFiber]

theorem toy_not_flat : ¬ Flat toyTransport := by
  intro h
  exact toy_curvedAt_false (h false)

theorem toy_no_observerCompatibleTrivialization :
    ¬ Nonempty (ObserverCompatibleTrivialization toyTransport) :=
  no_trivialization_of_curvedAt toy_curvedAt_false

theorem toy_contextualDeficit_eq_two :
    contextualDeficit toyTransport = 2 := by
  decide

/-!
## Audit boundary

`contextualDeficit` detects something that residual cardinality and ordinary
commutators erase: context-dependent disagreement at a shared endpoint.  The
flat cube has deficit zero, while the finite nested-bubble model has positive
deficit and cannot be globally trivialized.

This is the correct formal slot for the N-Frame functional-contextualist idea,
but it is not yet the P-versus-NP lower bound.  The load-bearing future work is
to derive transports from genuine, solver-independent CNF restriction syntax;
prove a polynomial bound for a specified restricted observer class; and then
test whether any such bound survives adaptive rereading and polynomial memory.
-/

end PallLean.Paper93.DeepMath.PathB.ContextualContinuationCurvature

#print axioms PallLean.Paper93.DeepMath.PathB.ContextualContinuationCurvature.flat_of_trivialization
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualContinuationCurvature.coordinateCubeTransport_flat
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualContinuationCurvature.toy_no_observerCompatibleTrivialization
#print axioms PallLean.Paper93.DeepMath.PathB.ContextualContinuationCurvature.toy_contextualDeficit_eq_two
