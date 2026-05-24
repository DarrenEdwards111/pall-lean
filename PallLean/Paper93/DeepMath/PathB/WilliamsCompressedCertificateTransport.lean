import PallLean.Paper93.DeepMath.PathB.CompressedCertificateGeometry

/-!
# Williams-style transport for compressed certificates

The rank/width versions of the dynamic N-frame route fail by counting.  The
remaining positive idea is to use the compressed-certificate layer as an input
to the Williams algorithmic method instead of trying to lower-bound SAT
directly.

This file formalizes that shift as a socket:

* a circuit class `C`;
* a faster-than-brute-force SAT algorithm for `C`;
* an easy-witness/compressed-certificate transport;
* a nondeterministic hierarchy contradiction.

That is the known successful pattern behind Williams-style lower bounds.  The
N-frame compressed geometry can participate only by supplying the algorithmic
transport data, not by reintroducing a monotone rank-to-width bridge.

The file does not claim P vs NP.  It proves the correct theorem for the
Williams template: once the fast-SAT/easy-witness/hierarchy transport is
supplied, `NEXP` is not contained in the chosen circuit class.  A separate
polynomial-scale bridge would still be needed to turn this into a P-vs-NP
statement.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## Abstract Williams lower-bound template -/

/-- Abstract surface for a circuit class in the Williams algorithmic method.

`NEXPLanguage` is intentionally abstract: this repository has not formalized
NEXP.  The point of the file is the transport shape, not a full complexity
theory library. -/
structure WilliamsCircuitClass where
  NEXPLanguage : Type
  HasSmallCircuits : NEXPLanguage -> Prop
  FastCircuitSAT : Prop
  EasyWitnessCompression : Prop
  HierarchyCollapse : Prop

/-- NEXP is contained in the circuit class. -/
def NEXPSubsetCircuitClass (C : WilliamsCircuitClass) : Prop :=
  forall L : C.NEXPLanguage, C.HasSmallCircuits L

/-- NEXP is not contained in the circuit class. -/
def NEXPNotSubsetCircuitClass (C : WilliamsCircuitClass) : Prop :=
  Not (NEXPSubsetCircuitClass C)

/-- Williams-style algorithmic transport.

The two load-bearing steps are exactly the known pattern:

1. fast SAT plus a small-circuit assumption gives easy witnesses;
2. easy witnesses plus the same small-circuit assumption gives a hierarchy
   collapse, contradicting the nondeterministic time hierarchy.
-/
structure WilliamsAlgorithmicTransport (C : WilliamsCircuitClass) where
  easyWitness_of_fastSAT_and_smallCircuits :
    C.FastCircuitSAT ->
      NEXPSubsetCircuitClass C ->
        C.EasyWitnessCompression
  hierarchyCollapse_of_easyWitness_and_smallCircuits :
    C.EasyWitnessCompression ->
      NEXPSubsetCircuitClass C ->
        C.HierarchyCollapse
  hierarchyContradiction : Not C.HierarchyCollapse

/-- The core Williams lower-bound theorem. -/
theorem nexp_not_subset_of_williams_transport
    (C : WilliamsCircuitClass)
    (hfast : C.FastCircuitSAT)
    (transport : WilliamsAlgorithmicTransport C) :
    NEXPNotSubsetCircuitClass C := by
  intro hsubset
  have heasy : C.EasyWitnessCompression :=
    transport.easyWitness_of_fastSAT_and_smallCircuits hfast hsubset
  have hcollapse : C.HierarchyCollapse :=
    transport.hierarchyCollapse_of_easyWitness_and_smallCircuits
      heasy hsubset
  exact transport.hierarchyContradiction hcollapse

/-! ## Connecting compressed N-frame certificates to Williams transport -/

/-- A compressed N-frame geometry contributes to Williams's method only if it
produces an algorithmic speedup for a circuit class.

This replaces the failed direct bridge
`obstructionRank <= observerWidth`.  The bridge target is now
`FastCircuitSAT`, which Williams transport can use non-circularly. -/
def CompressedGeometryYieldsFastCircuitSAT
    {enc : ThreeCNFEncoding}
    (G : CompressedCanonicalNFrameGeometry enc)
    (C : WilliamsCircuitClass) : Prop :=
  exists k : Nat,
    DescriptionPolynomialBound G k /\
      SATObstructionLowerBound G /\
      C.FastCircuitSAT

/-- Full Williams-powered compressed-certificate program.

This is the honest positive research target.  The N-frame geometry must produce
a fast circuit-SAT algorithm for the target class; Williams transport then turns
that algorithm into a circuit lower bound. -/
structure WilliamsCompressedCertificateProgram
    (enc : ThreeCNFEncoding) where
  geometry : CompressedCanonicalNFrameGeometry enc
  circuitClass : WilliamsCircuitClass
  compressed_geometry_yields_fast_sat :
    CompressedGeometryYieldsFastCircuitSAT geometry circuitClass
  williams_transport :
    WilliamsAlgorithmicTransport circuitClass

/-- A completed Williams-powered compressed-certificate program yields a
Williams-style NEXP circuit lower bound. -/
theorem nexp_not_subset_of_williamsCompressedCertificateProgram
    (enc : ThreeCNFEncoding)
    (program : WilliamsCompressedCertificateProgram enc) :
    NEXPNotSubsetCircuitClass program.circuitClass := by
  rcases program.compressed_geometry_yields_fast_sat with
    ⟨k, hdesc, hsat, hfast⟩
  exact nexp_not_subset_of_williams_transport
    program.circuitClass hfast program.williams_transport

/-! ## What would still be needed for P vs NP -/

/-- A separate bridge from a Williams-style circuit lower bound to the
repository's SAT-decider lower bound.

This is intentionally a distinct socket.  Williams transport supplies known
lower bounds at NEXP/circuit-class scale; pushing the consequence down to
`DTMDecidesSATWithEncoding` is another hard theorem, not a bookkeeping step. -/
def PolynomialScaleWilliamsBridge
    (enc : ThreeCNFEncoding)
    (C : WilliamsCircuitClass) : Prop :=
  NEXPNotSubsetCircuitClass C ->
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M)

/-- If one additionally supplies a polynomial-scale bridge, the Williams
compressed-certificate program would prove the SAT-decider lower bound.

The theorem is deliberately conditional on `PolynomialScaleWilliamsBridge`:
that bridge is the open breakthrough needed to turn Williams-style progress
into P-vs-NP progress. -/
theorem no_DTMDecidesSATWithEncoding_of_williamsCompressedCertificateProgram
    (enc : ThreeCNFEncoding)
    (program : WilliamsCompressedCertificateProgram enc)
    (hpolyScale :
      PolynomialScaleWilliamsBridge enc program.circuitClass) :
    Not (exists M : TuringMachine.DTM, DTMDecidesSATWithEncoding enc M) :=
  hpolyScale
    (nexp_not_subset_of_williamsCompressedCertificateProgram enc program)

/-! ## Kernel-only axiom trace -/

#print axioms nexp_not_subset_of_williams_transport
#print axioms nexp_not_subset_of_williamsCompressedCertificateProgram
#print axioms no_DTMDecidesSATWithEncoding_of_williamsCompressedCertificateProgram

end PallLean.Paper93.DeepMath.PathB
