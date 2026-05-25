import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetacomplexityReductions

/-
# Cook-Levin family obstruction layer

This file takes the next hard step after the reduction ledger: it introduces an
explicit Cook-Levin-family interface and the proof/communication/circuit
obstruction predicates that would imply the existing `CookLevinHardFamilySocket`.

No open lower bound is proved.  The point is to make the remaining mathematical
obligations concrete:

* provide a satisfiable Cook-Levin CNF family;
* attach an obstruction measure to each family member;
* prove that every short-fast generator is blocked by the measure on some
  family member;
* bridge that blockedness to actual witness-generation failure.

Once those are supplied, the already-pushed route closes automatically to
`HardMetacomplexitySocket` and `¬ CanonicalSATDecisionInP`.
-/

namespace SATDepthMachine

/-! ## Explicit Cook-Levin family interface -/

/-- Abstract source machine/run family encoded by Cook-Levin CNFs.

The fields are intentionally semantic rather than committing to a particular
Turing-machine encoding.  A concrete instantiation should fill `source`,
`timeBound`, `formula`, and prove that each formula is satisfiable because the
encoded accepting computation exists. -/
structure CookLevinTraceFamily where
  Source : Type
  source : Nat -> Source
  timeBound : Nat -> Nat
  formula : Nat -> CNF
  satisfiable : ∀ n : Nat, Satisfiable (formula n)

/-- Forget the Cook-Levin metadata and keep the satisfiable CNF family needed by
`CookLevinHardFamilySocket`. -/
def CookLevinTraceFamily.toSatisfiableCNFFamily
    (F : CookLevinTraceFamily) : SatisfiableCNFFamily where
  formula := F.formula
  satisfiable := F.satisfiable

/-! ## Obstruction measures -/

/-- A proof/communication/circuit obstruction measure attached to one family
member and one generator code.

`blocked` is the semantic condition saying the measure certifies that the
generator does not output a satisfying witness for this formula.  Concrete
instantiations can interpret `measure` as resolution width, communication
complexity, rectangle rank, circuit lower-bound witness, transcript complexity,
etc. -/
structure FamilyGeneratorObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    (n : Nat) where
  measure : Nat
  lowerBound : Nat
  violatesBound : measure < lowerBound
  blocked :
    ¬ ∃ a : RawAssignment,
      D.surface.toMachineModel.searchRun G.machine.code (F.formula n) = some a ∧
        Satisfies (F.formula n) a

/-- A generator is obstructed on a Cook-Levin family if some family member has a
valid obstruction certificate. -/
def GeneratorObstructedOnCookLevinFamily
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L) : Prop :=
  ∃ n : Nat, Nonempty (FamilyGeneratorObstruction D F L G n)

/-- An obstruction certificate gives failure on the underlying satisfiable CNF
family. -/
theorem generatorFailsOnFamily_of_obstructed
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (L : Nat)
    (G : ShortFastCandidateGenerator D.toDescriptionMachineModel L)
    (h : GeneratorObstructedOnCookLevinFamily D F L G) :
    GeneratorFailsOnFamily D L G F.toSatisfiableCNFFamily := by
  rcases h with ⟨n, hob⟩
  exact ⟨n, (Classical.choice hob).blocked⟩

/-- If every short-fast generator is obstructed on one Cook-Levin family, then
that family is a Cook-Levin hard family. -/
theorem cookLevinHardFamilySocket_of_generatorObstructions
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (hF : ∀ L : Nat,
      ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
        GeneratorObstructedOnCookLevinFamily D F L G) :
    CookLevinHardFamilySocket D := by
  refine ⟨F.toSatisfiableCNFFamily, ?_⟩
  intro L G
  exact generatorFailsOnFamily_of_obstructed D F L G (hF L G)

/-! ## Proof/communication/circuit obstruction sockets -/

/-- Proof-complexity obstruction for a Cook-Levin family.

Intended reading: for every generator, some member of the family has a proof
measure lower bound that the generator-induced proof/trace cannot meet. -/
def CookLevinProofComplexityObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      GeneratorObstructedOnCookLevinFamily D F L G

/-- Communication-complexity obstruction for a Cook-Levin family.

This is separate from proof complexity so later files can instantiate it via
rectangle/cut/rank arguments while reusing the same bridge theorem. -/
def CookLevinCommunicationObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      GeneratorObstructedOnCookLevinFamily D F L G

/-- Circuit obstruction for a Cook-Levin family.

Intended reading: the generator-to-circuit simulation plus a circuit lower bound
produces an obstruction certificate for some family member. -/
def CookLevinCircuitObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily) : Prop :=
  ∀ L : Nat,
    ∀ G : ShortFastCandidateGenerator D.toDescriptionMachineModel L,
      GeneratorObstructedOnCookLevinFamily D F L G

/-- Proof-complexity obstruction implies the Cook-Levin hard-family socket. -/
theorem cookLevinHardFamilySocket_of_proofComplexityObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinProofComplexityObstruction D F) :
    CookLevinHardFamilySocket D :=
  cookLevinHardFamilySocket_of_generatorObstructions D F h

/-- Communication-complexity obstruction implies the Cook-Levin hard-family
socket. -/
theorem cookLevinHardFamilySocket_of_communicationObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinCommunicationObstruction D F) :
    CookLevinHardFamilySocket D :=
  cookLevinHardFamilySocket_of_generatorObstructions D F h

/-- Circuit obstruction implies the Cook-Levin hard-family socket. -/
theorem cookLevinHardFamilySocket_of_circuitObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinCircuitObstruction D F) :
    CookLevinHardFamilySocket D :=
  cookLevinHardFamilySocket_of_generatorObstructions D F h

/-! ## Final route closures from Cook-Levin obstructions -/

/-- A proof-complexity obstruction on an explicit Cook-Levin family implies the
hard metacomplexity socket. -/
theorem hardSocket_of_CookLevinProofComplexityObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinProofComplexityObstruction D F) :
    HardMetacomplexitySocket D :=
  hardSocket_of_CookLevinHardFamily D
    (cookLevinHardFamilySocket_of_proofComplexityObstruction D F h)

/-- A communication-complexity obstruction on an explicit Cook-Levin family
implies the hard metacomplexity socket. -/
theorem hardSocket_of_CookLevinCommunicationObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinCommunicationObstruction D F) :
    HardMetacomplexitySocket D :=
  hardSocket_of_CookLevinHardFamily D
    (cookLevinHardFamilySocket_of_communicationObstruction D F h)

/-- A circuit obstruction on an explicit Cook-Levin family implies the hard
metacomplexity socket. -/
theorem hardSocket_of_CookLevinCircuitObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinCircuitObstruction D F) :
    HardMetacomplexitySocket D :=
  hardSocket_of_CookLevinHardFamily D
    (cookLevinHardFamilySocket_of_circuitObstruction D F h)

/-- Paper-facing closure from a proof-complexity obstruction. -/
theorem ktRoute_finalClosure_of_CookLevinProofComplexityObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinProofComplexityObstruction D F) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardSocket_of_CookLevinProofComplexityObstruction D F h)

/-- Paper-facing closure from a communication-complexity obstruction. -/
theorem ktRoute_finalClosure_of_CookLevinCommunicationObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinCommunicationObstruction D F) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardSocket_of_CookLevinCommunicationObstruction D F h)

/-- Paper-facing closure from a circuit obstruction. -/
theorem ktRoute_finalClosure_of_CookLevinCircuitObstruction
    (D : DescribedCanonicalSurface)
    (F : CookLevinTraceFamily)
    (h : CookLevinCircuitObstruction D F) :
    (¬ CanonicalSATDecisionInP D.surface) ∧
      NoPolynomialLengthScheduledCompleteGenerators D :=
  ktRoute_finalClosure D
    (hardSocket_of_CookLevinCircuitObstruction D F h)

/-! ## Axiom trace -/

#print axioms CookLevinTraceFamily.toSatisfiableCNFFamily
#print axioms generatorFailsOnFamily_of_obstructed
#print axioms cookLevinHardFamilySocket_of_generatorObstructions
#print axioms cookLevinHardFamilySocket_of_proofComplexityObstruction
#print axioms cookLevinHardFamilySocket_of_communicationObstruction
#print axioms cookLevinHardFamilySocket_of_circuitObstruction
#print axioms hardSocket_of_CookLevinProofComplexityObstruction
#print axioms hardSocket_of_CookLevinCommunicationObstruction
#print axioms hardSocket_of_CookLevinCircuitObstruction
#print axioms ktRoute_finalClosure_of_CookLevinProofComplexityObstruction
#print axioms ktRoute_finalClosure_of_CookLevinCommunicationObstruction
#print axioms ktRoute_finalClosure_of_CookLevinCircuitObstruction

end SATDepthMachine
