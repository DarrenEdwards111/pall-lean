import PallLean.Tseitin
import PallLean.Paper93.DeepMath.PathB.ProjectedIdentityMinorPaperFaithful

/-!
# Independent Route B source lower bound

This module isolates the source-side identity-minor lower-bound route for a
coupled sheet `Q : CoupledSheetPoly σ` without using the older concrete
compiler witness.

The generic identity-minor infrastructure proves the lower bound for Tseitin's
`coupledVerifier`.  What is still missing for a new Route B source polynomial
is the bridge from that generic Tseitin verifier/rank statement to the selected
coupled sheet.  We record that bridge as explicit data and prove the source
lower-bound theorem from it.
-/

namespace PallLean.Paper93.Paper283

open MultilinearSPDP
open PaperFaithfulCompilation
open PallLean.Paper93.DeepMath.PathB

/-- The precise missing bridge from generic Tseitin identity minors to an
arbitrary coupled-sheet source polynomial.

For a source sheet `Q`, this packages:
* the Tseitin formula and disjoint packing to which the generic theorem applies;
* the arithmetic comparison from the generic minor size to the paper's
  `choose (n / 3) (log₂ n)` target;
* the rank transport from `blockedSpdpRank` of the generic Tseitin verifier to
  the `mlBlockedSpdpRank` of the coupled sheet against the pulled-back source
  partition.

Supplying this bridge is exactly the remaining generic-to-`CoupledSheetPoly`
obligation for an independent, non-compiled Route B source. -/
structure GenericTseitinIdentityMinorToCoupledSheetBridge
    (n : Nat) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : Nat) (Q : CoupledSheetPoly σ) : Type where
  Phi : Tseitin.TseitinFormula
  pack : Tseitin.DisjointPacking Phi
  kappa_le_pack : κ ≤ pack.selected.length
  target_choose_le_pack_choose :
    Nat.choose (n / 3) (Nat.log 2 n) ≤ Nat.choose pack.selected.length κ
  generic_rank_transports_to_source :
    SPDP.blockedSpdpRank (IdentityMinor.tseitinPartition Phi) κ ℓ
        (Tseitin.coupledVerifier Rat Phi) ≤
      mlBlockedSpdpRank (pullbackPartition B σ.inlU) κ ℓ Q

/-- Generic identity-minor lower bound transported to an arbitrary coupled
sheet, assuming the explicit generic-to-coupled-sheet bridge above. -/
theorem sourceIdentityMinorLowerBound_of_genericTseitinBridge
    (n : Nat) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : Nat) (Q : CoupledSheetPoly σ)
    (bridge :
      GenericTseitinIdentityMinorToCoupledSheetBridge n σ B κ ℓ Q) :
    SourceIdentityMinorLowerBound n σ B κ ℓ Q := by
  unfold SourceIdentityMinorLowerBound
  have hgeneric :
      Nat.choose bridge.pack.selected.length κ ≤
        SPDP.blockedSpdpRank (IdentityMinor.tseitinPartition bridge.Phi) κ ℓ
          (Tseitin.coupledVerifier Rat bridge.Phi) :=
    Tseitin.identity_minor_lower_bound Rat bridge.Phi bridge.pack κ ℓ
      bridge.kappa_le_pack
  exact bridge.target_choose_le_pack_choose.trans
    (hgeneric.trans bridge.generic_rank_transports_to_source)

/-- Certificate form for an independently supplied Route B source lower bound.

The `not_compiled_route` field is deliberately abstract: callers may instantiate
it with their own predicate proving that the chosen `Q` was produced by the
intended independent source construction. -/
structure IndependentCoupledSheetSourceLowerBoundCertificate
    (n : Nat) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : Nat) (Q : CoupledSheetPoly σ) : Type where
  not_compiled_route : Prop
  not_compiled_route_proof : not_compiled_route
  bridge : GenericTseitinIdentityMinorToCoupledSheetBridge n σ B κ ℓ Q

/-- A certified independent source sheet carries the paper-faithful source
identity-minor lower bound. -/
theorem sourceIdentityMinorLowerBound_of_independentCertificate
    (n : Nat) (σ : UVSplit) (B : SPDP.BlockPartition σ.total)
    (κ ℓ : Nat) (Q : CoupledSheetPoly σ)
    (cert :
      IndependentCoupledSheetSourceLowerBoundCertificate n σ B κ ℓ Q) :
    SourceIdentityMinorLowerBound n σ B κ ℓ Q :=
  sourceIdentityMinorLowerBound_of_genericTseitinBridge
    n σ B κ ℓ Q cert.bridge

/-! ## Axiom audit anchors -/

#print axioms sourceIdentityMinorLowerBound_of_genericTseitinBridge
#print axioms sourceIdentityMinorLowerBound_of_independentCertificate

end PallLean.Paper93.Paper283
