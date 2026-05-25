import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResourceBoundedDescriptions

/-
# K^t route theorem surface

This file packages the remaining computational-depth route as a final theorem
surface.

It does **not** prove P ≠ NP.  Instead it records the exact object that would
have to be proved:

  `HardMetacomplexitySocket D`

for an intended described canonical surface `D`.

The new pieces here are paper-facing refinements:

* a polynomial description-length-bound predicate;
* a Levin/K^t-style cost predicate `KtCostAtMost`;
* short-fast generators with a length bound as a function of input size;
* the final implication chain from the hard socket to no canonical SAT decider;
* equivalences showing that the hard socket is exactly the canonical deep-search
  / no-decider lower bound, not a hidden stronger assumption.
-/

namespace SATDepthMachine

/-! ## Polynomial description-length and KT-style cost surfaces -/

/-- Polynomially bounded description-length schedule. -/
def IsPolynomialLengthBound (ell : Nat -> Nat) : Prop :=
  ∃ k c : Nat, ∀ n : Nat, ell n ≤ c * (n + 1) ^ k

/-- Levin/K^t-style combined cost bound for a code on formula `φ`.

We use addition rather than `programLength + log time` to avoid importing a
logarithm library and because the theorem surface only needs a monotone resource
cap.  Later files can refine this to a literal logarithmic KT definition. -/
def KtCostAtMost
    (V : DescriptionMachineModel)
    (B : Nat -> Nat)
    (code : Nat) (φ : CNF) : Prop :=
  V.programLength code + V.toMachineModel.searchSteps code φ ≤ B φ.size

/-- A local witness has bounded KT-style cost if some code within the combined
resource cap outputs a satisfying assignment. -/
def KtCostWitnessDescription
    (V : DescriptionMachineModel)
    (B : Nat -> Nat)
    (φ : CNF) : Prop :=
  ∃ code a,
    KtCostAtMost V B code φ ∧
    V.toMachineModel.searchRun code φ = some a ∧
    Satisfies φ a

/-- Local KT-cost depth at budget `B`.  This is still a per-instance predicate;
the uniform lower-bound object remains the generator failure predicate below. -/
def KtCostWitnessDeepAt
    (V : DescriptionMachineModel)
    (B : Nat -> Nat)
    (φ : CNF) : Prop :=
  Satisfiable φ ∧ ¬ KtCostWitnessDescription V B φ

/-! ## Size-dependent short-fast generator bounds -/

/-- A search machine whose code length is bounded by a length schedule at every
input size.  Since code length is constant for a fixed machine, this is mostly a
paper-facing bridge to standard `ell(n)` metacomplexity notation. -/
structure LengthScheduledCandidateGenerator
    (V : DescriptionMachineModel) (ell : Nat -> Nat) where
  machine : SearchMachine V.toMachineModel
  short_at_size : ∀ φ : CNF, V.programLength machine.code ≤ ell φ.size

/-- Completeness for a length-scheduled generator. -/
def LengthScheduledGeneratorComplete
    (V : DescriptionMachineModel) (ell : Nat -> Nat)
    (G : LengthScheduledCandidateGenerator V ell) : Prop :=
  SearchCorrect V.toMachineModel G.machine

/-- Failure for a length-scheduled generator. -/
def LengthScheduledGeneratorFails
    (V : DescriptionMachineModel) (ell : Nat -> Nat)
    (G : LengthScheduledCandidateGenerator V ell) : Prop :=
  ∃ φ : CNF,
    Satisfiable φ ∧
      ¬ ∃ a : RawAssignment,
        V.toMachineModel.searchRun G.machine.code φ = some a ∧ Satisfies φ a

/-- If a scheduled generator is complete, it yields shallow SAT search. -/
theorem shallowSearch_of_lengthScheduledGeneratorComplete
    (V : DescriptionMachineModel) (ell : Nat -> Nat)
    (G : LengthScheduledCandidateGenerator V ell)
    (hG : LengthScheduledGeneratorComplete V ell G) :
    ShallowSATSearch V.toMachineModel :=
  ⟨G.machine, hG⟩

/-- Negating scheduled completeness is exactly scheduled failure. -/
theorem not_lengthScheduledGeneratorComplete_iff_fails
    (V : DescriptionMachineModel) (ell : Nat -> Nat)
    (G : LengthScheduledCandidateGenerator V ell) :
    ¬ LengthScheduledGeneratorComplete V ell G ↔
      LengthScheduledGeneratorFails V ell G := by
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

/-- Deep search rules out all complete length-scheduled candidate generators. -/
theorem lengthScheduledGeneratorFails_of_deepSATSearch
    (V : DescriptionMachineModel)
    (hdeep : DeepSATSearch V.toMachineModel)
    (ell : Nat -> Nat)
    (G : LengthScheduledCandidateGenerator V ell) :
    LengthScheduledGeneratorFails V ell G :=
  (not_lengthScheduledGeneratorComplete_iff_fails V ell G).mp
    (by
      intro hcomplete
      exact hdeep
        (shallowSearch_of_lengthScheduledGeneratorComplete V ell G hcomplete))

/-- A short-fast generator at a fixed length budget becomes a scheduled
generator for any schedule that dominates that fixed budget on all formula sizes.
-/ 
def lengthScheduledGenerator_of_shortFast
    (V : DescriptionMachineModel) (L : Nat) (ell : Nat -> Nat)
    (hdom : ∀ n : Nat, L ≤ ell n)
    (G : ShortFastCandidateGenerator V L) :
    LengthScheduledCandidateGenerator V ell where
  machine := G.machine
  short_at_size := by
    intro φ
    exact Nat.le_trans G.short_code (hdom φ.size)

/-! ## Final route closure -/

/-- The hard metacomplexity socket implies canonical deep SAT search. -/
theorem canonicalDeepSATSearch_of_hardMetacomplexitySocket
    (D : DescribedCanonicalSurface)
    (h : HardMetacomplexitySocket D) :
    CanonicalDeepSATSearch D.surface :=
  (hardMetacomplexitySocket_iff_canonicalDeepSATSearch D).mp h

/-- The hard metacomplexity socket rules out canonical polynomial-time SAT
decision.  This is the paper-facing closure theorem for the route. -/
theorem noCanonicalSATDecisionInP_of_hardMetacomplexitySocket
    (D : DescribedCanonicalSurface)
    (h : HardMetacomplexitySocket D) :
    ¬ CanonicalSATDecisionInP D.surface :=
  canonicalNoDecider_of_deepSATSearch D.surface
    (canonicalDeepSATSearch_of_hardMetacomplexitySocket D h)

/-- Conversely, no canonical SAT decider implies the hard metacomplexity socket,
because the canonical surface already includes the prefix-unit decision-to-search
compiler.  Thus the socket is exactly the P-vs-NP-strength remaining theorem for
this canonical model. -/
theorem hardMetacomplexitySocket_of_noCanonicalSATDecisionInP
    (D : DescribedCanonicalSurface)
    (h : ¬ CanonicalSATDecisionInP D.surface) :
    HardMetacomplexitySocket D :=
  (hardMetacomplexitySocket_iff_canonicalDeepSATSearch D).mpr
    ((canonicalDeepSATSearch_iff_no_decider D.surface).mpr h)

/-- Final equivalence: the metacomplexity socket and no canonical SAT decider are
identical targets after the canonical compiler wiring. -/
theorem hardMetacomplexitySocket_iff_noCanonicalSATDecisionInP
    (D : DescribedCanonicalSurface) :
    HardMetacomplexitySocket D ↔ ¬ CanonicalSATDecisionInP D.surface := by
  constructor
  · exact noCanonicalSATDecisionInP_of_hardMetacomplexitySocket D
  · exact hardMetacomplexitySocket_of_noCanonicalSATDecisionInP D

/-- The lower-bound target also rules out every polynomial length-scheduled
complete generator. -/
theorem lengthScheduledGeneratorFails_of_hardMetacomplexitySocket
    (D : DescribedCanonicalSurface)
    (h : HardMetacomplexitySocket D)
    (ell : Nat -> Nat)
    (G : LengthScheduledCandidateGenerator
      D.toDescriptionMachineModel ell) :
    LengthScheduledGeneratorFails D.toDescriptionMachineModel ell G :=
  lengthScheduledGeneratorFails_of_deepSATSearch
    D.toDescriptionMachineModel
    (canonicalDeepSATSearch_of_hardMetacomplexitySocket D h)
    ell G

/-- Fully expanded final target: for every polynomial length schedule, every
scheduled candidate generator fails on some satisfiable CNF.  This follows from
the hard socket; proving it directly would also imply the same no-decider result
once converted back to `DeepSATSearch`. -/
def NoPolynomialLengthScheduledCompleteGenerators
    (D : DescribedCanonicalSurface) : Prop :=
  ∀ ell : Nat -> Nat,
    IsPolynomialLengthBound ell ->
      ∀ G : LengthScheduledCandidateGenerator D.toDescriptionMachineModel ell,
        LengthScheduledGeneratorFails D.toDescriptionMachineModel ell G

/-- Hard socket implies the fully expanded polynomial-schedule failure target. -/
theorem noPolynomialLengthScheduledCompleteGenerators_of_hardSocket
    (D : DescribedCanonicalSurface)
    (h : HardMetacomplexitySocket D) :
    NoPolynomialLengthScheduledCompleteGenerators D := by
  intro ell _hell G
  exact lengthScheduledGeneratorFails_of_hardMetacomplexitySocket D h ell G

/-- Named final route statement: if the intended described canonical surface
satisfies the hard metacomplexity socket, then canonical SAT decision is not in
P for that surface and every polynomial length-scheduled generator fails. -/
theorem ktRoute_finalClosure
    (D : DescribedCanonicalSurface)
    (h : HardMetacomplexitySocket D) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ⟨noCanonicalSATDecisionInP_of_hardMetacomplexitySocket D h,
    noPolynomialLengthScheduledCompleteGenerators_of_hardSocket D h⟩

/-! ## Axiom trace -/

#print axioms shallowSearch_of_lengthScheduledGeneratorComplete
#print axioms not_lengthScheduledGeneratorComplete_iff_fails
#print axioms lengthScheduledGeneratorFails_of_deepSATSearch
#print axioms canonicalDeepSATSearch_of_hardMetacomplexitySocket
#print axioms noCanonicalSATDecisionInP_of_hardMetacomplexitySocket
#print axioms hardMetacomplexitySocket_of_noCanonicalSATDecisionInP
#print axioms hardMetacomplexitySocket_iff_noCanonicalSATDecisionInP
#print axioms noPolynomialLengthScheduledCompleteGenerators_of_hardSocket
#print axioms ktRoute_finalClosure

end SATDepthMachine
