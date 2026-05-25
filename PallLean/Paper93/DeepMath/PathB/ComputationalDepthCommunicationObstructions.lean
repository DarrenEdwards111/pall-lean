import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinObstructions

/-
# Communication / rectangle obstruction skeleton

This file makes the next lower-bound attack concrete without asserting the hard
communication lower bound.

It introduces finite Boolean communication matrices, combinatorial rectangles,
rectangle covers of the 1-entries, and the exact contradiction shape needed to
block a SAT witness generator:

* the Cook-Levin family member induces a communication matrix `M`;
* every valid witness output by a generator induces a small rectangle cover;
* an independent communication lower bound says every 1-cover of `M` is large;
* small < large contradicts the lower bound, so the generator cannot output a
  satisfying witness on that family member.

The final theorem packages this as a `CookLevinCommunicationObstruction`, which
already implies the hard metacomplexity socket and the route closure.
-/

namespace SATDepthMachine

/-! ## Finite Boolean communication matrices -/

/-- A finite Boolean communication matrix with `rows × cols` entries. -/
def BoolMatrix (rows cols : Nat) : Type :=
  Fin rows -> Fin cols -> Bool

/-- A combinatorial rectangle in a finite communication matrix. -/
structure Rectangle (rows cols : Nat) where
  rowSet : Fin rows -> Prop
  colSet : Fin cols -> Prop

/-- A rectangle contains a matrix position. -/
def Rectangle.Contains
    {rows cols : Nat}
    (R : Rectangle rows cols)
    (i : Fin rows) (j : Fin cols) : Prop :=
  R.rowSet i ∧ R.colSet j

/-- A list of rectangles covers all 1-entries of a Boolean matrix. -/
def CoversOneEntries
    {rows cols : Nat}
    (M : BoolMatrix rows cols)
    (cover : List (Rectangle rows cols)) : Prop :=
  ∀ (i : Fin rows) (j : Fin cols),
    M i j = true -> ∃ R : Rectangle rows cols, R ∈ cover ∧ R.Contains i j

/-- Rectangle-cover lower bound for a matrix. -/
def RectangleCoverLowerBound
    {rows cols : Nat}
    (M : BoolMatrix rows cols)
    (lower : Nat) : Prop :=
  ∀ cover : List (Rectangle rows cols),
    CoversOneEntries M cover -> lower ≤ cover.length

/-- A strict upper bound on a generator-induced cover contradicts a rectangle
cover lower bound. -/
theorem no_cover_below_rectangleCoverLowerBound
    {rows cols : Nat}
    {M : BoolMatrix rows cols}
    {lower : Nat}
    (hLower : RectangleCoverLowerBound M lower)
    (cover : List (Rectangle rows cols))
    (hCover : CoversOneEntries M cover)
    (hSmall : cover.length < lower) : False := by
  exact Nat.not_lt_of_ge (hLower cover hCover) hSmall

/-! ## Generator-induced communication covers -/

/-- Data saying that, if a particular short-fast generator outputs a satisfying
assignment for `F.formula n`, then that output induces a rectangle cover that is
smaller than the independent communication lower bound.

This is the proof obligation a real communication lower-bound argument should
supply.  The present file only uses it as an interface. -/
structure GeneratorInducedRectangleCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    (n rows cols lower : Nat) where
  matrix : BoolMatrix rows cols
  cover : List (Rectangle rows cols)
  covers : CoversOneEntries matrix cover
  lowerBound : RectangleCoverLowerBound matrix lower
  small_if_witness :
    (∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a) -> cover.length < lower

/-- A generator-induced small cover plus an independent rectangle-cover lower
bound blocks witness output on the chosen Cook-Levin family member. -/
theorem no_witness_of_generatorInducedRectangleCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    {n rows cols lower : Nat}
    (C : GeneratorInducedRectangleCover D F L G n rows cols lower) :
    ¬ ∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a := by
  intro hwit
  exact no_cover_below_rectangleCoverLowerBound
    C.lowerBound C.cover C.covers (C.small_if_witness hwit)

/-- Convert a generator-induced rectangle-cover contradiction into the generic
family-generator obstruction certificate used by the Cook-Levin layer. -/
def familyGeneratorObstruction_of_rectangleCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    {n rows cols lower : Nat}
    (C : GeneratorInducedRectangleCover D F L G n rows cols lower) :
    FamilyGeneratorObstruction D F L G n where
  measure := C.cover.length
  lowerBound := C.cover.length + 1
  violatesBound := Nat.lt_succ_self C.cover.length
  blocked := no_witness_of_generatorInducedRectangleCover D F L G C

/-! ## Family-level communication lower-bound socket -/

/-- Communication rectangle obstruction for every short-fast generator on a
fixed Cook-Levin trace family.

For every code-length budget and generator, there is some family member and some
communication matrix such that any witness output would induce a too-small
rectangle cover. -/
def CookLevinRectangleCoverObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      ∃ (n rows cols lower : Nat),
        Nonempty (GeneratorInducedRectangleCover D F L G n rows cols lower)

/-- A rectangle-cover obstruction gives the generic Cook-Levin communication
obstruction used by the previous layer. -/
theorem CookLevinCommunicationObstruction_of_rectangleCoverObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinRectangleCoverObstruction D F) :
    CookLevinCommunicationObstruction D F := by
  intro L G
  rcases h L G with ⟨n, rows, cols, lower, hC⟩
  refine ⟨n, ?_⟩
  exact ⟨familyGeneratorObstruction_of_rectangleCover D F L G (Classical.choice hC)⟩

/-- Rectangle-cover obstruction implies the hard metacomplexity socket. -/
theorem hardSocket_of_CookLevinRectangleCoverObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinRectangleCoverObstruction D F) :
    HardMetacomplexitySocket D :=
  hardSocket_of_CookLevinCommunicationObstruction D F
    (CookLevinCommunicationObstruction_of_rectangleCoverObstruction D F h)

/-- Rectangle-cover obstruction closes the route to no canonical SAT decider and
failure of all polynomial length-scheduled generators. -/
theorem ktRoute_finalClosure_of_CookLevinRectangleCoverObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinRectangleCoverObstruction D F) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardSocket_of_CookLevinRectangleCoverObstruction D F h)

/-! ## Axiom trace -/

#print axioms no_cover_below_rectangleCoverLowerBound
#print axioms no_witness_of_generatorInducedRectangleCover
#print axioms familyGeneratorObstruction_of_rectangleCover
#print axioms CookLevinCommunicationObstruction_of_rectangleCoverObstruction
#print axioms hardSocket_of_CookLevinRectangleCoverObstruction
#print axioms ktRoute_finalClosure_of_CookLevinRectangleCoverObstruction

end SATDepthMachine
