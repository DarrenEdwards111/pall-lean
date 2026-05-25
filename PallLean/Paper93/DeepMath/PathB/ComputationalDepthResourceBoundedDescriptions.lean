import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFinalLowerBoundTarget

/-
# Resource-bounded descriptions and the precise K^t lower-bound socket

This file makes the metacomplexity target explicit.

It adds a genuine resource-bounded description layer on top of the existing
machine semantics:

* `programLength` records description length of machine codes;
* `ShortFastCandidateGenerator` packages a short code with a polynomial runtime
  bound and search semantics;
* `KtWitnessDescription` is the Levin/K^t-style per-instance predicate: a short
  program outputs a satisfying witness within a time bound;
* `ShortFastGeneratorComplete` is the uniform lower-bound target: a short fast
  generator covers every satisfiable CNF;
* `NoShortFastCompleteGenerator` says every such generator fails on some
  satisfiable CNF.

The hard socket is isolated cleanly:

  `DeepSATSearch U` iff every length bound excludes complete short-fast
  generators.

No lower bound is proved here.  The file proves the exact equivalences and
bridges: a complete short-fast generator gives shallow search; deep search rules
out every short-fast complete generator; and conversely, ruling them out at all
length bounds is exactly deep search.
-/

namespace SATDepthMachine

/-! ## Description length on top of machine semantics -/

/-- A machine model with an explicit description-length function for codes. -/
structure DescriptionMachineModel where
  toMachineModel : MachineModel
  programLength : Nat -> Nat

instance : Coe DescriptionMachineModel MachineModel where
  coe V := V.toMachineModel

/-- Description length of a search machine's code. -/
def SearchMachine.descriptionLength
    (V : DescriptionMachineModel)
    (M : SearchMachine V.toMachineModel) : Nat :=
  V.programLength M.code

/-- A code is short relative to a concrete length budget.  For uniform machines,
this is a constant-code-size bound; quantifying over all `L` recovers the full
polynomial-time search class because every concrete code has some finite length.
-/
def CodeLengthAtMost (V : DescriptionMachineModel) (L code : Nat) : Prop :=
  V.programLength code ≤ L

/-! ## K^t / Levin-style per-instance witness descriptions -/

/-- A per-instance K^t-style witness description.

For a fixed formula `φ`, there is a program of length at most `L` that runs
within `timeBound φ.size` and outputs a satisfying assignment.  This is useful
as a local metacomplexity predicate, but by itself it is not the P-vs-NP search
lower bound because a single witness can always be described directly.  The
uniform generator predicates below are the load-bearing objects. -/
def KtWitnessDescription
    (V : DescriptionMachineModel)
    (L : Nat) (timeBound : Nat -> Nat)
    (φ : CNF) : Prop :=
  ∃ code a,
    CodeLengthAtMost V L code ∧
    V.toMachineModel.searchSteps code φ ≤ timeBound φ.size ∧
    V.toMachineModel.searchRun code φ = some a ∧
    Satisfies φ a

/-- A formula is K^t-shallow at `(L,timeBound)` if every satisfiable instance
has such a short timed witness description. -/
def KtWitnessShallowOn
    (V : DescriptionMachineModel)
    (L : Nat) (timeBound : Nat -> Nat)
    (φ : CNF) : Prop :=
  Satisfiable φ -> KtWitnessDescription V L timeBound φ

/-- Local K^t-depth at `(L,timeBound)`: the formula is satisfiable but has no
short timed witness description at that resource level. -/
def KtWitnessDeepAt
    (V : DescriptionMachineModel)
    (L : Nat) (timeBound : Nat -> Nat)
    (φ : CNF) : Prop :=
  Satisfiable φ ∧ ¬ KtWitnessDescription V L timeBound φ

/-! ## Uniform short-fast candidate generators -/

/-- A short fast candidate generator: one coded polynomial-time search machine
whose code length is bounded by `L`.

This is the uniform candidate-generator object corresponding to the SAT-search
function, not just a one-off witness description for one formula. -/
structure ShortFastCandidateGenerator
    (V : DescriptionMachineModel) (L : Nat) where
  machine : SearchMachine V.toMachineModel
  short_code : CodeLengthAtMost V L machine.code

/-- The generator covers all satisfiable formulas. -/
def ShortFastGeneratorComplete
    (V : DescriptionMachineModel) (L : Nat)
    (G : ShortFastCandidateGenerator V L) : Prop :=
  SearchCorrect V.toMachineModel G.machine

/-- The generator fails on some satisfiable formula. -/
def ShortFastGeneratorFails
    (V : DescriptionMachineModel) (L : Nat)
    (G : ShortFastCandidateGenerator V L) : Prop :=
  ∃ φ : CNF,
    Satisfiable φ ∧
      ¬ ∃ a : RawAssignment,
        V.toMachineModel.searchRun G.machine.code φ = some a ∧ Satisfies φ a

/-- At length budget `L`, there is no complete short-fast generator. -/
def NoShortFastCompleteGeneratorAt
    (V : DescriptionMachineModel) (L : Nat) : Prop :=
  ∀ G : ShortFastCandidateGenerator V L, ShortFastGeneratorFails V L G

/-- The exact uniform lower-bound target: every code-length budget fails. -/
def NoShortFastCompleteGenerator
    (V : DescriptionMachineModel) : Prop :=
  ∀ L : Nat, NoShortFastCompleteGeneratorAt V L

/-! ## Bridges to shallow/deep SAT search -/

/-- A complete short-fast generator is a shallow SAT search machine. -/
theorem shallowSearch_of_shortFastGeneratorComplete
    (V : DescriptionMachineModel) (L : Nat)
    (G : ShortFastCandidateGenerator V L)
    (hG : ShortFastGeneratorComplete V L G) :
    ShallowSATSearch V.toMachineModel :=
  ⟨G.machine, hG⟩

/-- Negating completeness is exactly generator failure. -/
theorem not_shortFastGeneratorComplete_iff_fails
    (V : DescriptionMachineModel) (L : Nat)
    (G : ShortFastCandidateGenerator V L) :
    ¬ ShortFastGeneratorComplete V L G ↔ ShortFastGeneratorFails V L G := by
  classical
  constructor
  · intro hnot
    by_contra hnofail
    apply hnot
    intro φ hsat
    by_contra hnowitness
    exact hnofail ⟨φ, hsat, hnowitness⟩
  · intro hfail hcomplete
    rcases hfail with ⟨φ, hsat, hnowitness⟩
    exact hnowitness (hcomplete φ hsat)

/-- Deep SAT search rules out complete short-fast generators at every length
budget. -/
theorem noShortFastCompleteGenerator_of_deepSATSearch
    (V : DescriptionMachineModel)
    (hdeep : DeepSATSearch V.toMachineModel) :
    NoShortFastCompleteGenerator V := by
  intro L G
  exact (not_shortFastGeneratorComplete_iff_fails V L G).mp
    (by
      intro hcomplete
      exact hdeep (shallowSearch_of_shortFastGeneratorComplete V L G hcomplete))

/-- If a shallow machine exists, it is short-fast for its own concrete code
length. -/
def shortFastGenerator_of_searchMachine
    (V : DescriptionMachineModel)
    (M : SearchMachine V.toMachineModel) :
    ShortFastCandidateGenerator V (V.programLength M.code) where
  machine := M
  short_code := Nat.le_refl _

/-- Ruling out short-fast complete generators for every length budget gives deep
SAT search. -/
theorem deepSATSearch_of_noShortFastCompleteGenerator
    (V : DescriptionMachineModel)
    (hno : NoShortFastCompleteGenerator V) :
    DeepSATSearch V.toMachineModel := by
  intro hshallow
  rcases hshallow with ⟨M, hM⟩
  let G := shortFastGenerator_of_searchMachine V M
  have hfail : ShortFastGeneratorFails V (V.programLength M.code) G :=
    hno (V.programLength M.code) G
  have hcomplete : ShortFastGeneratorComplete V (V.programLength M.code) G := hM
  exact ((not_shortFastGeneratorComplete_iff_fails
    V (V.programLength M.code) G).mpr hfail) hcomplete

/-- The precise lower-bound target: SAT-search depth is equivalent to the
failure of every short fast candidate generator at every code-length budget. -/
theorem deepSATSearch_iff_noShortFastCompleteGenerator
    (V : DescriptionMachineModel) :
    DeepSATSearch V.toMachineModel ↔ NoShortFastCompleteGenerator V := by
  constructor
  · exact noShortFastCompleteGenerator_of_deepSATSearch V
  · exact deepSATSearch_of_noShortFastCompleteGenerator V

/-! ## Canonical-surface form of the hard socket -/

/-- Add a description-length function to an existing canonical surface. -/
structure DescribedCanonicalSurface where
  surface : CanonicalMachineSurface
  programLength : Nat -> Nat

/-- The description model induced by a described canonical surface. -/
def DescribedCanonicalSurface.toDescriptionMachineModel
    (D : DescribedCanonicalSurface) : DescriptionMachineModel where
  toMachineModel := D.surface.toMachineModel
  programLength := D.programLength

/-- Canonical version of the exact short-fast lower-bound socket. -/
def CanonicalNoShortFastCompleteGenerator
    (D : DescribedCanonicalSurface) : Prop :=
  NoShortFastCompleteGenerator D.toDescriptionMachineModel

/-- Canonical deep search is exactly the no-short-fast-generator target once a
program-length function is fixed. -/
theorem canonicalDeepSATSearch_iff_noShortFastCompleteGenerator
    (D : DescribedCanonicalSurface) :
    CanonicalDeepSATSearch D.surface ↔
      CanonicalNoShortFastCompleteGenerator D := by
  exact deepSATSearch_iff_noShortFastCompleteGenerator
    D.toDescriptionMachineModel

/-- This is the real P-vs-NP-strength socket in the new language.  Proving this
for the intended universal canonical surface would close the lower-bound route;
there is no proof of it in this file. -/
def HardMetacomplexitySocket
    (D : DescribedCanonicalSurface) : Prop :=
  CanonicalNoShortFastCompleteGenerator D

/-- The hard socket is not a new hidden assumption: it is definitionally the
canonical deep SAT-search lower bound. -/
theorem hardMetacomplexitySocket_iff_canonicalDeepSATSearch
    (D : DescribedCanonicalSurface) :
    HardMetacomplexitySocket D ↔ CanonicalDeepSATSearch D.surface := by
  rw [HardMetacomplexitySocket, CanonicalNoShortFastCompleteGenerator]
  exact (canonicalDeepSATSearch_iff_noShortFastCompleteGenerator D).symm

/-! ## Axiom trace -/

#print axioms shallowSearch_of_shortFastGeneratorComplete
#print axioms not_shortFastGeneratorComplete_iff_fails
#print axioms noShortFastCompleteGenerator_of_deepSATSearch
#print axioms deepSATSearch_of_noShortFastCompleteGenerator
#print axioms deepSATSearch_iff_noShortFastCompleteGenerator
#print axioms canonicalDeepSATSearch_iff_noShortFastCompleteGenerator
#print axioms hardMetacomplexitySocket_iff_canonicalDeepSATSearch

end SATDepthMachine
