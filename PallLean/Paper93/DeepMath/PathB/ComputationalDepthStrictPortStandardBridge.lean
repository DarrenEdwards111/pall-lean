import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207StrictPort

/-!
# Strict-port bridge to a standard P-vs-NP statement

The strict Book-1 route has reached an exact no-decider endpoint:

```lean
Theorem207StrictLiveBoundaryPort enc
  ↔ ¬ ∃ M, DTMDecidesSATWithEncoding enc M
```

This file packages the final model-equivalence layer needed to read that
endpoint as a standard `P ≠ NP` statement.  It does not assert that the standard
statement has been proved.  Instead it requires an explicit bridge saying that
the repository's encoded-DTM SAT-decider notion is equivalent to the intended
standard polynomial-time SAT-decider notion.

Thus the final remaining work is exactly visible:

1. instantiate `StandardPvsNPBridge enc` for the intended standard model; and
2. prove either side of `theorem207StrictPort_iff_no_DTMDecidesSATWithEncoding`
   unconditionally.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- A local, explicit bridge from the repository's encoded-DTM SAT lower-bound
endpoint to whatever standard `P ≠ NP` proposition the final paper chooses.

The field `standardPvsNP` is intentionally abstract here.  The point is to
avoid silently identifying `DTMDecidesSATWithEncoding enc` with a separate
standard model.  That identification must be supplied as a theorem by the
chosen formalization of standard polynomial-time SAT decision. -/
structure StandardPvsNPBridge
    (enc : ThreeCNFEncoding) where
  standardPvsNP : Prop
  standardPvsNP_iff_no_encodedSATDecider :
    standardPvsNP ↔
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M)

/-- The strict live-boundary port is equivalent to the bridged standard
`P ≠ NP` proposition, once the model-equivalence bridge is supplied. -/
theorem theorem207StrictPort_iff_standardPvsNP
    {enc : ThreeCNFEncoding}
    (B : StandardPvsNPBridge enc) :
    Theorem207StrictLiveBoundaryPort enc ↔ B.standardPvsNP := by
  constructor
  · intro hport
    exact B.standardPvsNP_iff_no_encodedSATDecider.mpr
      ((theorem207StrictPort_iff_no_DTMDecidesSATWithEncoding enc).mp hport)
  · intro hstd
    exact (theorem207StrictPort_iff_no_DTMDecidesSATWithEncoding enc).mpr
      (B.standardPvsNP_iff_no_encodedSATDecider.mp hstd)

/-- If the strict port is proved unconditionally, the bridged standard
`P ≠ NP` proposition follows. -/
theorem standardPvsNP_of_theorem207StrictPort
    {enc : ThreeCNFEncoding}
    (B : StandardPvsNPBridge enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    B.standardPvsNP :=
  (theorem207StrictPort_iff_standardPvsNP B).mp Hport

/-- Package-level standard readout from the final strict-port package. -/
theorem standardPvsNP_of_strictPortSeparationPackage
    {enc : ThreeCNFEncoding}
    (B : StandardPvsNPBridge enc)
    (pkg : Theorem207StrictPortSeparationPackage enc) :
    B.standardPvsNP :=
  standardPvsNP_of_theorem207StrictPort B pkg.hport

/-- The low-action Book-1 final endpoint, read through the standard-model
bridge.  This theorem records that once a strict-port package exists, its
no-decider consequence is exactly the bridged standard `P ≠ NP` statement.

It is not an unconditional proof: the strict-port package remains the
P-vs-NP-strength frontier. -/
theorem standardPvsNP_of_strictBook1_lowActionPackage
    {enc : ThreeCNFEncoding}
    (B : StandardPvsNPBridge enc)
    (pkg : Theorem207StrictPortSeparationPackage enc) :
    B.standardPvsNP := by
  have hno :
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M) :=
    strictBook1_lowActionFinalNoDeciderEndpoint enc pkg
  exact B.standardPvsNP_iff_no_encodedSATDecider.mpr hno

/-! ## Kernel-only axiom trace -/

#print axioms theorem207StrictPort_iff_standardPvsNP
#print axioms standardPvsNP_of_theorem207StrictPort
#print axioms standardPvsNP_of_strictPortSeparationPackage
#print axioms standardPvsNP_of_strictBook1_lowActionPackage

end PallLean.Paper93.DeepMath.PathB
