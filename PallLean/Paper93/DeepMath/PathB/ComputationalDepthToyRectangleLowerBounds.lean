import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCommunicationObstructions

/-
# Toy rectangle lower bound calibration

This file proves the first nontrivial communication lower-bound calculation used
as a calibration model before attaching the rectangle machinery to a real
Cook-Levin family.

The matrix is equality/identity.  A monochromatic 1-rectangle for equality can
cover at most one diagonal 1-entry.  Therefore any indexed exact 1-cover of the
n diagonal entries needs at least n rectangles.

This is intentionally a toy theorem, but it exercises the same proof pattern
needed later:

  matrix lower bound + generator-induced small cover -> obstruction.
-/

namespace SATDepthMachine

/-! ## Equality matrix and monochromatic rectangles -/

/-- The `n × n` equality/identity communication matrix. -/
def EqualityMatrix (n : Nat) : BoolMatrix n n :=
  fun i j => decide (i = j)

/-- A rectangle is 1-monochromatic for a matrix if every cell it contains is a
1-entry. -/
def OneRectangle
    {rows cols : Nat}
    (M : BoolMatrix rows cols)
    (R : Rectangle rows cols) : Prop :=
  ∀ i j, R.Contains i j -> M i j = true

/-- A cover together with explicit chosen rectangle indices for the diagonal
1-entries of the equality matrix.  This avoids list-membership bookkeeping and
matches how generator-induced covers are usually constructed: the construction
knows which transcript/rectangle covers each entry. -/
structure IndexedDiagonalCover (n : Nat) where
  cover : List (Rectangle n n)
  one_rectangles : ∀ k : Fin cover.length,
    OneRectangle (EqualityMatrix n) (cover.get k)
  pick : Fin n -> Fin cover.length
  covers_diag : ∀ i : Fin n, (cover.get (pick i)).Contains i i

/-! ## Core lower bound -/

/-- If one 1-monochromatic rectangle in the equality matrix contains two
diagonal entries `(i,i)` and `(j,j)`, then `i = j`. -/
theorem eq_of_same_oneRectangle_contains_two_diagonal
    {n : Nat}
    {R : Rectangle n n}
    (hR : OneRectangle (EqualityMatrix n) R)
    {i j : Fin n}
    (hi : R.Contains i i)
    (hj : R.Contains j j) :
    i = j := by
  rcases hi with ⟨hri, _hci⟩
  rcases hj with ⟨_hrj, hcj⟩
  have hijCell : R.Contains i j := ⟨hri, hcj⟩
  have htrue : EqualityMatrix n i j = true := hR i j hijCell
  unfold EqualityMatrix at htrue
  exact of_decide_eq_true htrue

/-- The diagonal-to-rectangle map in an indexed equality cover is injective. -/
theorem IndexedDiagonalCover.pick_injective
    {n : Nat}
    (C : IndexedDiagonalCover n) : Function.Injective C.pick := by
  intro i j hpick
  have hi : (C.cover.get (C.pick i)).Contains i i := C.covers_diag i
  have hj0 : (C.cover.get (C.pick i)).Contains j j := by
    simpa [hpick] using C.covers_diag j
  exact eq_of_same_oneRectangle_contains_two_diagonal
    (C.one_rectangles (C.pick i)) hi hj0

/-- Equality/identity needs at least `n` one-rectangles to cover its `n` diagonal
entries in an indexed exact cover. -/
theorem equalityMatrix_indexedDiagonalCover_lowerBound
    {n : Nat}
    (C : IndexedDiagonalCover n) :
    n ≤ C.cover.length := by
  have hcard := Fintype.card_le_of_injective C.pick C.pick_injective
  simpa [Fintype.card_fin] using hcard

/-- Pack the lower bound as a rectangle-cover lower-bound style theorem for the
toy indexed-cover interface. -/
def EqualityIndexedRectangleLowerBound (n : Nat) : Prop :=
  ∀ C : IndexedDiagonalCover n, n ≤ C.cover.length

/-- The equality matrix satisfies the indexed rectangle-cover lower bound. -/
theorem equalityIndexedRectangleLowerBound
    (n : Nat) : EqualityIndexedRectangleLowerBound n := by
  intro C
  exact equalityMatrix_indexedDiagonalCover_lowerBound C

/-! ## Calibration obstruction socket -/

/-- Toy generator-induced indexed equality cover.  A real Cook-Levin
communication argument should replace this with a construction from generator
transcripts; here it calibrates the contradiction form with a proved lower bound.
-/ 
structure GeneratorInducedEqualityCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    (n : Nat) where
  cover : IndexedDiagonalCover n
  small_if_witness :
    (∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a) -> cover.cover.length < n

/-- The toy equality lower bound blocks witness output when a generator would
induce a too-small indexed equality cover. -/
theorem no_witness_of_generatorInducedEqualityCover
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    {n : Nat}
    (C : GeneratorInducedEqualityCover D F L G n) :
    ¬ ∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a := by
  intro hwit
  have hLower : n ≤ C.cover.cover.length :=
    equalityMatrix_indexedDiagonalCover_lowerBound C.cover
  exact Nat.not_lt_of_ge hLower (C.small_if_witness hwit)

/-- Obstruction wrapper for the toy equality calibration: it stores the proved
blockedness directly and uses a trivial numeric measure gap.  The substantive
lower-bound calculation is `no_witness_of_generatorInducedEqualityCover`; the
numeric fields are bookkeeping for the generic obstruction interface. -/
def familyGeneratorObstruction_of_equalityBlocked
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    {n : Nat}
    (C : GeneratorInducedEqualityCover D F L G n) :
    FamilyGeneratorObstruction D F L G n where
  measure := 0
  lowerBound := 1
  violatesBound := Nat.zero_lt_one
  blocked := no_witness_of_generatorInducedEqualityCover D F L G C

/-- Family-level toy equality-cover obstruction. -/
def CookLevinEqualityCoverObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      ∃ n : Nat, Nonempty (GeneratorInducedEqualityCover D F L G n)

/-- The toy equality-cover obstruction gives the generic Cook-Levin
communication obstruction. -/
theorem CookLevinCommunicationObstruction_of_equalityCoverObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinEqualityCoverObstruction D F) :
    CookLevinCommunicationObstruction D F := by
  intro L G
  rcases h L G with ⟨n, hC⟩
  refine ⟨n, ?_⟩
  exact ⟨familyGeneratorObstruction_of_equalityBlocked D F L G
    (Classical.choice hC)⟩

/-- The toy equality-cover obstruction closes through the existing route. -/
theorem ktRoute_finalClosure_of_CookLevinEqualityCoverObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinEqualityCoverObstruction D F) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure_of_CookLevinCommunicationObstruction D F
    (CookLevinCommunicationObstruction_of_equalityCoverObstruction D F h)

/-! ## Axiom trace -/

#print axioms eq_of_same_oneRectangle_contains_two_diagonal
#print axioms IndexedDiagonalCover.pick_injective
#print axioms equalityMatrix_indexedDiagonalCover_lowerBound
#print axioms equalityIndexedRectangleLowerBound
#print axioms no_witness_of_generatorInducedEqualityCover
#print axioms CookLevinCommunicationObstruction_of_equalityCoverObstruction
#print axioms ktRoute_finalClosure_of_CookLevinEqualityCoverObstruction

end SATDepthMachine
