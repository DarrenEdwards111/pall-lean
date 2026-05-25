import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKtRouteTheorem

/-
# Reductions to the hard metacomplexity socket

This file does not prove any of the standard open lower bounds.  It gives a
clean reduction ledger: several familiar lower-bound targets are represented as
abstract sockets, and each is connected to the route's single hard endpoint,
`HardMetacomplexitySocket`.

The pattern is intentionally simple and auditable:

* each external target is expressed as a predicate saying it rules out complete
  short-fast SAT candidate generators;
* each target therefore implies `CanonicalNoShortFastCompleteGenerator` and
  hence `HardMetacomplexitySocket`;
* the final route closure then gives `¬ CanonicalSATDecisionInP`.

This turns "maybe use MCSP / MINKT / circuits / Cook-Levin / diagonalization /
proof complexity" into concrete Lean obligations without pretending those
obligations are solved.
-/

namespace SATDepthMachine

/-! ## Shared bridge predicates -/

/-- A lower-bound oracle/socket that directly rules out every short-fast
candidate generator at every code-length bound.  This is the common conclusion
that standard lower-bound approaches must establish. -/
def RulesOutShortFastSATGenerators
    (D : DescribedCanonicalSurface) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      ShortFastGeneratorFails D.toDescriptionMachineModel L G

/-- The shared bridge from any approach that rules out complete short-fast SAT
generators to the route's hard socket. -/
theorem hardSocket_of_rulesOutShortFastSATGenerators
    (D : DescribedCanonicalSurface)
    (h : RulesOutShortFastSATGenerators D) :
    HardMetacomplexitySocket D := by
  intro L G
  exact h L G

/-- Any approach that rules out short-fast SAT generators closes the route to no
canonical SAT decider. -/
theorem noCanonicalSATDecisionInP_of_rulesOutShortFastSATGenerators
    (D : DescribedCanonicalSurface)
    (h : RulesOutShortFastSATGenerators D) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_hardMetacomplexitySocket D
    (hardSocket_of_rulesOutShortFastSATGenerators D h)

/-! ## MCSP / MINKT socket -/

/-- Abstract MCSP/MINKT hardness principle for the described canonical surface.

Intended reading: a sufficiently strong MCSP/MINKT lower bound prevents any
short fast decompressor/searcher from covering SAT witnesses uniformly. -/
def MCSPMINKTHardnessSocket
    (D : DescribedCanonicalSurface) : Prop :=
  RulesOutShortFastSATGenerators D

/-- MCSP/MINKT hardness implies the route's hard socket. -/
theorem hardSocket_of_MCSPMINKTHardness
    (D : DescribedCanonicalSurface)
    (h : MCSPMINKTHardnessSocket D) :
    HardMetacomplexitySocket D :=
  hardSocket_of_rulesOutShortFastSATGenerators D h

/-- MCSP/MINKT hardness closes the no-canonical-decider route. -/
theorem noCanonicalSATDecisionInP_of_MCSPMINKTHardness
    (D : DescribedCanonicalSurface)
    (h : MCSPMINKTHardnessSocket D) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_hardMetacomplexitySocket D
    (hardSocket_of_MCSPMINKTHardness D h)

/-! ## Circuit lower-bound socket -/

/-- Abstract circuit-lower-bound principle.

Intended reading: every polynomial-size circuit family attempting to implement
SAT witness generation fails on some satisfiable CNF.  The compiler from coded
machines to circuits is the missing concrete theorem behind this socket. -/
def CircuitLowerBoundSocket
    (D : DescribedCanonicalSurface) : Prop :=
  RulesOutShortFastSATGenerators D

/-- Circuit lower bounds imply the hard metacomplexity socket. -/
theorem hardSocket_of_circuitLowerBound
    (D : DescribedCanonicalSurface)
    (h : CircuitLowerBoundSocket D) :
    HardMetacomplexitySocket D :=
  hardSocket_of_rulesOutShortFastSATGenerators D h

/-- Circuit lower bounds close the no-canonical-decider route. -/
theorem noCanonicalSATDecisionInP_of_circuitLowerBound
    (D : DescribedCanonicalSurface)
    (h : CircuitLowerBoundSocket D) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_hardMetacomplexitySocket D
    (hardSocket_of_circuitLowerBound D h)

/-! ## Cook-Levin hard-family socket -/

/-- A named family of satisfiable CNFs, indexed by `n`. -/
structure SatisfiableCNFFamily where
  formula : Nat -> CNF
  satisfiable : ∀ n : Nat, Satisfiable (formula n)

/-- A short-fast generator fails on a named family if it misses at least one
satisfiable formula in that family. -/
def GeneratorFailsOnFamily
    (D : DescribedCanonicalSurface)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    (F : SatisfiableCNFFamily) : Prop :=
  ∃ n : Nat,
    ¬ ∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a

/-- Failure on a satisfiable family gives ordinary generator failure. -/
theorem shortFastGeneratorFails_of_failsOnFamily
    (D : DescribedCanonicalSurface)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    (F : SatisfiableCNFFamily)
    (h : GeneratorFailsOnFamily D L G F) :
    ShortFastGeneratorFails D.toDescriptionMachineModel L G := by
  rcases h with ⟨n, hfail⟩
  exact ⟨F.formula n, F.satisfiable n, hfail⟩

/-- Abstract Cook-Levin hard-family socket.

Intended reading: there is an explicit Cook-Levin family such that every
short-fast SAT generator fails on some member of that family. -/
def CookLevinHardFamilySocket
    (D : DescribedCanonicalSurface) : Prop :=
  ∃ F : SatisfiableCNFFamily,
    ∀ L : Nat,
      ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
        GeneratorFailsOnFamily D L G F

/-- A Cook-Levin hard family rules out every short-fast SAT generator. -/
theorem rulesOutShortFastSATGenerators_of_CookLevinHardFamily
    (D : DescribedCanonicalSurface)
    (h : CookLevinHardFamilySocket D) :
    RulesOutShortFastSATGenerators D := by
  rcases h with ⟨F, hF⟩
  intro L G
  exact shortFastGeneratorFails_of_failsOnFamily D L G F (hF L G)

/-- Cook-Levin hard-family lower bounds imply the hard socket. -/
theorem hardSocket_of_CookLevinHardFamily
    (D : DescribedCanonicalSurface)
    (h : CookLevinHardFamilySocket D) :
    HardMetacomplexitySocket D :=
  hardSocket_of_rulesOutShortFastSATGenerators D
    (rulesOutShortFastSATGenerators_of_CookLevinHardFamily D h)

/-! ## Explicit diagonalization socket -/

/-- Abstract diagonalization principle.

Intended reading: enumerate every short-fast generator and construct, for each
one, a satisfiable CNF on which it fails. -/
def ExplicitDiagonalizationSocket
    (D : DescribedCanonicalSurface) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      ∃ φ : CNF,
        Satisfiable φ ∧
          ¬ ∃ a : RawAssignment,
            D.surface.toMachineModel.searchRun G.machine.code φ = some a ∧
              Satisfies φ a

/-- Diagonalization is just the fully expanded short-fast-generator failure
predicate. -/
theorem rulesOutShortFastSATGenerators_of_diagonalization
    (D : DescribedCanonicalSurface)
    (h : ExplicitDiagonalizationSocket D) :
    RulesOutShortFastSATGenerators D := by
  intro L G
  exact h L G

/-- Explicit diagonalization implies the hard socket. -/
theorem hardSocket_of_diagonalization
    (D : DescribedCanonicalSurface)
    (h : ExplicitDiagonalizationSocket D) :
    HardMetacomplexitySocket D :=
  hardSocket_of_rulesOutShortFastSATGenerators D
    (rulesOutShortFastSATGenerators_of_diagonalization D h)

/-! ## Proof-complexity / communication socket -/

/-- Abstract proof-complexity or communication-complexity lower-bound socket.

Intended reading: the communication/proof measure lower bound prevents any
short-fast generator from producing valid SAT witnesses uniformly. -/
def ProofCommunicationLowerBoundSocket
    (D : DescribedCanonicalSurface) : Prop :=
  RulesOutShortFastSATGenerators D

/-- Proof/communication lower bounds imply the hard socket. -/
theorem hardSocket_of_proofCommunicationLowerBound
    (D : DescribedCanonicalSurface)
    (h : ProofCommunicationLowerBoundSocket D) :
    HardMetacomplexitySocket D :=
  hardSocket_of_rulesOutShortFastSATGenerators D h

/-- Proof/communication lower bounds close the no-canonical-decider route. -/
theorem noCanonicalSATDecisionInP_of_proofCommunicationLowerBound
    (D : DescribedCanonicalSurface)
    (h : ProofCommunicationLowerBoundSocket D) :
    ¬ CanonicalSATDecisionInP D.surface :=
  noCanonicalSATDecisionInP_of_hardMetacomplexitySocket D
    (hardSocket_of_proofCommunicationLowerBound D h)

/-! ## Combined ledger -/

/-- Any one of the named standard lower-bound approaches is sufficient to prove
the route's hard socket. -/
def AnyKnownLowerBoundSocket
    (D : DescribedCanonicalSurface) : Prop :=
  MCSPMINKTHardnessSocket D ∨
  CircuitLowerBoundSocket D ∨
  CookLevinHardFamilySocket D ∨
  ExplicitDiagonalizationSocket D ∨
  ProofCommunicationLowerBoundSocket D

/-- The combined reduction ledger: any named known-style socket implies the hard
metacomplexity socket. -/
theorem hardSocket_of_anyKnownLowerBoundSocket
    (D : DescribedCanonicalSurface)
    (h : AnyKnownLowerBoundSocket D) :
    HardMetacomplexitySocket D := by
  rcases h with hMCSP | hCircuit | hCook | hDiag | hProof
  · exact hardSocket_of_MCSPMINKTHardness D hMCSP
  · exact hardSocket_of_circuitLowerBound D hCircuit
  · exact hardSocket_of_CookLevinHardFamily D hCook
  · exact hardSocket_of_diagonalization D hDiag
  · exact hardSocket_of_proofCommunicationLowerBound D hProof

/-- Any named lower-bound socket closes the final route to no canonical SAT
decider and polynomial-schedule generator failure. -/
theorem ktRoute_finalClosure_of_anyKnownLowerBoundSocket
    (D : DescribedCanonicalSurface)
    (h : AnyKnownLowerBoundSocket D) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D (hardSocket_of_anyKnownLowerBoundSocket D h)

/-! ## Axiom trace -/

#print axioms hardSocket_of_rulesOutShortFastSATGenerators
#print axioms noCanonicalSATDecisionInP_of_rulesOutShortFastSATGenerators
#print axioms hardSocket_of_MCSPMINKTHardness
#print axioms noCanonicalSATDecisionInP_of_MCSPMINKTHardness
#print axioms hardSocket_of_circuitLowerBound
#print axioms noCanonicalSATDecisionInP_of_circuitLowerBound
#print axioms shortFastGeneratorFails_of_failsOnFamily
#print axioms rulesOutShortFastSATGenerators_of_CookLevinHardFamily
#print axioms hardSocket_of_CookLevinHardFamily
#print axioms rulesOutShortFastSATGenerators_of_diagonalization
#print axioms hardSocket_of_diagonalization
#print axioms hardSocket_of_proofCommunicationLowerBound
#print axioms noCanonicalSATDecisionInP_of_proofCommunicationLowerBound
#print axioms hardSocket_of_anyKnownLowerBoundSocket
#print axioms ktRoute_finalClosure_of_anyKnownLowerBoundSocket

end SATDepthMachine
