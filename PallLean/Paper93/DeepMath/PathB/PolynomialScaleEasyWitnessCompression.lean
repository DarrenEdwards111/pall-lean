import PallLean.Paper93.DeepMath.PathB.WilliamsCompressedCertificateTransport

/-!
# Polynomial-scale easy-witness compression frontier

The Williams transport file gives the known successful shape:

  fast circuit-SAT -> easy witnesses -> hierarchy contradiction
  -> NEXP circuit lower bound.

This file names the extra theorem needed to make that transport bite at the
repository's SAT-decider scale.  It is not another CEW/rank variant.  It is the
precise missing bridge:

  fast circuit-SAT at the compressed N-frame geometry layer
  -> polynomial-scale easy witnesses
  -> polynomial-scale Williams bridge
  -> no polynomial-time SAT decider.

No such bridge is proved here.  The point is to isolate it without circularly
restating the direct SAT lower bound as a live-rank extraction theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-! ## Polynomial-scale easy witnesses -/

/-- Polynomial-scale easy-witness transport for a Williams circuit class.

This is the requested use of Williams as the missing transport.  The first
field says a fast circuit-SAT algorithm yields easy witnesses at the smaller
scale.  The second field says those easy witnesses are strong enough to turn a
Williams NEXP-level lower bound into the repository's SAT-decider lower bound.
-/
structure PolynomialScaleEasyWitnessCompression
    (enc : ThreeCNFEncoding)
    (C : WilliamsCircuitClass) : Prop where
  easyWitness_of_fastCircuitSAT :
    C.FastCircuitSAT -> C.EasyWitnessCompression
  polynomialScaleBridge_of_easyWitness :
    C.EasyWitnessCompression -> PolynomialScaleWilliamsBridge enc C

/-- Extract the fast circuit-SAT consequence from compressed N-frame geometry. -/
theorem fastCircuitSAT_of_compressedGeometry
    {enc : ThreeCNFEncoding}
    {G : CompressedCanonicalNFrameGeometry enc}
    {C : WilliamsCircuitClass}
    (hgeom : CompressedGeometryYieldsFastCircuitSAT G C) :
    C.FastCircuitSAT := by
  rcases hgeom with ⟨k, hdesc, hsat, hfast⟩
  exact hfast

/-- Polynomial-scale easy-witness compression supplies the missing
polynomial-scale Williams bridge once the compressed geometry gives fast SAT. -/
theorem polynomialScaleBridge_of_easyWitnessCompression
    {enc : ThreeCNFEncoding}
    {G : CompressedCanonicalNFrameGeometry enc}
    {C : WilliamsCircuitClass}
    (hgeom : CompressedGeometryYieldsFastCircuitSAT G C)
    (hcompress : PolynomialScaleEasyWitnessCompression enc C) :
    PolynomialScaleWilliamsBridge enc C := by
  have hfast : C.FastCircuitSAT :=
    fastCircuitSAT_of_compressedGeometry hgeom
  have heasy : C.EasyWitnessCompression :=
    hcompress.easyWitness_of_fastCircuitSAT hfast
  exact hcompress.polynomialScaleBridge_of_easyWitness heasy

/-! ## N-frame/Williams program at polynomial scale -/

/-- The combined positive program.

This is the clean target if we use Williams as the transport for the compressed
N-frame certificate idea.  The load-bearing field is
`polynomial_easy_witness`; it is the open breakthrough, not Lean wiring. -/
structure PolynomialScaleNFrameWilliamsProgram
    (enc : ThreeCNFEncoding) where
  geometry : CompressedCanonicalNFrameGeometry enc
  circuitClass : WilliamsCircuitClass
  compressed_geometry_yields_fast_sat :
    CompressedGeometryYieldsFastCircuitSAT geometry circuitClass
  williams_transport :
    WilliamsAlgorithmicTransport circuitClass
  polynomial_easy_witness :
    PolynomialScaleEasyWitnessCompression enc circuitClass

/-- Forget the polynomial-scale program to the ordinary Williams compressed
certificate program. -/
def PolynomialScaleNFrameWilliamsProgram.toWilliamsProgram
    {enc : ThreeCNFEncoding}
    (program : PolynomialScaleNFrameWilliamsProgram enc) :
    WilliamsCompressedCertificateProgram enc where
  geometry := program.geometry
  circuitClass := program.circuitClass
  compressed_geometry_yields_fast_sat :=
    program.compressed_geometry_yields_fast_sat
  williams_transport := program.williams_transport

/-- The polynomial-scale program still gives the Williams-level NEXP circuit
lower bound. -/
theorem nexp_not_subset_of_polynomialScaleNFrameWilliamsProgram
    (enc : ThreeCNFEncoding)
    (program : PolynomialScaleNFrameWilliamsProgram enc) :
    NEXPNotSubsetCircuitClass program.circuitClass :=
  nexp_not_subset_of_williamsCompressedCertificateProgram
    enc program.toWilliamsProgram

/-- The polynomial-scale program gives the SAT-decider lower bound exactly when
the new easy-witness transport supplies the polynomial-scale Williams bridge. -/
theorem no_DTMDecidesSATWithEncoding_of_polynomialScaleNFrameWilliamsProgram
    (enc : ThreeCNFEncoding)
    (program : PolynomialScaleNFrameWilliamsProgram enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  have hbridge : PolynomialScaleWilliamsBridge enc program.circuitClass :=
    polynomialScaleBridge_of_easyWitnessCompression
      program.compressed_geometry_yields_fast_sat
      program.polynomial_easy_witness
  exact
    no_DTMDecidesSATWithEncoding_of_williamsCompressedCertificateProgram
      enc program.toWilliamsProgram hbridge

/-! ## Universal theorem form -/

/-- A universal polynomial-scale easy-witness theorem for all compressed
N-frame/Williams targets.

This is the mathematical theorem one would actually have to prove to push the
Williams transport down to the SAT-decider scale. -/
def UniversalPolynomialScaleEasyWitnessCompression
    (enc : ThreeCNFEncoding) : Prop :=
  forall C : WilliamsCircuitClass,
    PolynomialScaleEasyWitnessCompression enc C

/-- If the universal polynomial-scale easy-witness theorem is available, any
compressed N-frame geometry that yields fast circuit-SAT and has Williams
transport closes the SAT-decider lower bound. -/
theorem no_DTMDecidesSATWithEncoding_of_universalPolynomialScaleEasyWitness
    (enc : ThreeCNFEncoding)
    (huniv : UniversalPolynomialScaleEasyWitnessCompression enc)
    (G : CompressedCanonicalNFrameGeometry enc)
    (C : WilliamsCircuitClass)
    (hgeom : CompressedGeometryYieldsFastCircuitSAT G C)
    (htransport : WilliamsAlgorithmicTransport C) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) := by
  let program : PolynomialScaleNFrameWilliamsProgram enc := {
    geometry := G
    circuitClass := C
    compressed_geometry_yields_fast_sat := hgeom
    williams_transport := htransport
    polynomial_easy_witness := huniv C
  }
  exact no_DTMDecidesSATWithEncoding_of_polynomialScaleNFrameWilliamsProgram
    enc program

/-! ## Kernel-only axiom trace -/

#print axioms fastCircuitSAT_of_compressedGeometry
#print axioms polynomialScaleBridge_of_easyWitnessCompression
#print axioms nexp_not_subset_of_polynomialScaleNFrameWilliamsProgram
#print axioms no_DTMDecidesSATWithEncoding_of_polynomialScaleNFrameWilliamsProgram
#print axioms no_DTMDecidesSATWithEncoding_of_universalPolynomialScaleEasyWitness

end PallLean.Paper93.DeepMath.PathB
