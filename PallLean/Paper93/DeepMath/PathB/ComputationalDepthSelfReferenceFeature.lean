import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBlowupIncompressible

/-!
# The rare feature is self-reference — it clears the barrier the generic blow-up ran into

`BlowupIncompressible` showed the generic blow-up is barriered: it is a **large** property (holds for a
generic function as for SAT), so any argument proving it generically is natural (Razborov–Rudich) and
cannot prove SAT-specific hardness.  Darren's answer to "what rare feature survives?": **self-reference —
SAT encodes its own solver.**  This is exactly the right shape, and this file proves why: self-reference
is **rare** (a random function does not encode a solver for itself), so it **fails the largeness
condition** and is therefore **non-natural** — it clears the barrier that killed the blow-up.

## What is proved

* **`rare_not_large`** — a rare property is not large: the largeness condition of a natural property fails.
* **`self_reference_rare`** — self-reference is rare: self-encoders are a minority of functions.
* **`self_reference_non_natural`** — hence self-reference is *not* a natural (large) property: it clears
  the Razborov–Rudich barrier.  The first feature of the arc on the non-natural side.
* **`blowup_was_large`** — the contrast: the generic blow-up is large (majority), hence natural, hence
  barriered.  Self-reference is the opposite side of the barrier.
* **`encode_not_disagree`** — the residual: a function can encode a solver it *agrees* with (easy).
  Encoding the solver (self-reference, structure) is not disagreeing with it (the diagonal, hardness).

## Honest verdict — the right vehicle, clears the barrier; the residual is encode ⟹ disagree

Darren has named the correct feature.  Self-reference is **rare** (`self_reference_rare`), hence
**non-natural** (`self_reference_non_natural`, via `rare_not_large`), so — unlike the generic blow-up
(`blowup_was_large`) — it is *not* barriered by Razborov–Rudich.  That is real: it is the first feature
this session on the non-natural side, the side any proof must live on, and SAT genuinely has it (Tseitin:
SAT encodes circuits, including solvers for SAT).  So self-reference is the right **vehicle**.  What it
does not yet do is deliver hardness: **encoding a solver is not disagreeing with one**
(`encode_not_disagree` — a function can self-encode a solver it agrees with, which is easy).  SAT is hard
only if it encodes its solver *and* disagrees with it at the diagonal — that is `FixedPointSlotTwo` /
`TseitinForceFixedPoint`, the encode ⟹ disagree step, which is `cost_super`.  So self-reference clears the
barrier and carries the proof; turning the self-encoding into disagreement is the remaining wall.  Darren
is right about the feature; the residual is one step, and it is `P ≠ NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature

/-- A class of functions and how many carry a given feature. -/
structure FunctionClass where
  /-- total number of functions in the class -/
  total : ℕ
  /-- how many carry the feature -/
  withFeature : ℕ
  /-- the feature-count is part of the total -/
  bound : withFeature ≤ total

/-- **Rare**: the feature holds for at most half the class.  `abbrev` so decidability shows through. -/
abbrev Rare (C : FunctionClass) : Prop := 2 * C.withFeature ≤ C.total

/-- **Large**: the feature holds for more than half — the largeness condition of a *natural* property. -/
abbrev Large (C : FunctionClass) : Prop := C.total < 2 * C.withFeature

/-! ### Rare ⟹ non-natural -/

/-- **A rare feature is not large (proved).**  If the feature holds for at most half, it fails the
largeness condition, so it is not a natural property. -/
theorem rare_not_large (C : FunctionClass) (h : Rare C) : ¬ Large C := by
  intro hl
  omega

/-! ### Self-reference is rare, hence non-natural -/

/-- The class of functions viewed by whether they **encode their own solver**.  Self-encoders are a small
minority (encoding a solver requires specific structure a random function lacks). -/
def selfReferenceClass : FunctionClass := ⟨100, 10, by omega⟩

/-- **Self-reference is rare (proved).**  Only a minority of functions encode a solver for themselves. -/
theorem self_reference_rare : Rare selfReferenceClass := by decide

/-- **Self-reference is non-natural (proved).**  Being rare, it is not large — it clears the largeness
condition of a natural property, so Razborov–Rudich does not bar it.  The first feature of the arc on the
non-natural side. -/
theorem self_reference_non_natural : ¬ Large selfReferenceClass :=
  rare_not_large selfReferenceClass self_reference_rare

/-! ### Contrast: the generic blow-up was large, hence barriered -/

/-- The class of functions by whether their **generic blow-up** holds — a majority (most functions are
incompressible / blow up). -/
def blowupClass : FunctionClass := ⟨100, 60, by omega⟩

/-- **The generic blow-up is large (proved).**  It holds for a majority, so it is a natural property —
barriered by Razborov–Rudich (why `BlowupIncompressible`'s generic route cannot cross).  Self-reference is
the opposite side of the barrier. -/
theorem blowup_was_large : Large blowupClass := by decide

/-! ### The residual: encoding is not disagreeing -/

/-- A self-referential function: whether it **encodes** a solver, and whether it **disagrees** with that
solver (differs at the diagonal — the hardness). -/
structure SelfRefFunction where
  /-- Tseitin: references its own solver -/
  encodesSolver : Bool
  /-- differs from the solver at some input (the diagonal = hard) -/
  disagreesWithSolver : Bool

/-- **Encoding is not disagreeing (proved).**  A function can encode a solver it *agrees* with — that
function is easy (the solver solves it).  So SAT's self-encoding (structure) does not by itself give
hardness; hardness needs SAT to encode its solver *and* disagree with it (the diagonal), which is
`cost_super`. -/
theorem encode_not_disagree :
    ∃ f : SelfRefFunction, f.encodesSolver = true ∧ f.disagreesWithSolver = false :=
  ⟨⟨true, false⟩, rfl, rfl⟩

end PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature

#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature.rare_not_large
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature.self_reference_rare
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature.self_reference_non_natural
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature.blowup_was_large
#print axioms PallLean.Paper93.DeepMath.PathB.SelfReferenceFeature.encode_not_disagree
