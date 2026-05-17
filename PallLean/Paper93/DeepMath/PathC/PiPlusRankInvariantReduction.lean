import PallLean.Paper93.DeepMath.PathC.PiPlusConcreteAdmissibilityFrontier

/-!
# Pi+ rank-invariance reduction

This file isolates the exact kernel-clean theorem needed for Route-C rank
invariance.

For an invertible `Pi+` transform, SPDP rank invariance follows once the
multilinear SPDP generator subspace is transported by the transform.  This is
the mathematically honest core: the remaining work is not linear-algebraic
finrank bookkeeping, but proving that the block-Hadamard polynomial equivalence
commutes with the specific `mlProj`/derivative/block-admissibility generator
space.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Exact subspace-transport condition for `Pi+`.

This states that applying the `Pi+` gauge map to the SPDP generator subspace of
`p` gives exactly the SPDP generator subspace of the transformed polynomial.
Once this is proved, rank invariance is pure finite-dimensional linear algebra. -/
def PiPlusSPDPSubspaceTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : PathB.SATDeciderGaugeSpace M n hn2 htb hns),
    Submodule.map piP.gauge
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p) =
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ (piP.gauge p)

/-- Subspace transport implies SPDP rank invariance for any invertible `Pi+`
transform. -/
theorem piPlusRankInvariant_of_spdpSubspaceTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (htransport : PiPlusSPDPSubspaceTransport M n hn2 htb hns piP) :
    PiPlusRankInvariant M n hn2 htb hns piP := by
  intro κ ℓ p
  unfold mlBlockedSpdpRank
  rw [← htransport κ ℓ p]
  exact LinearEquiv.finrank_map_eq piP.equiv
    (mlBlockedSpdpSubspace
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p)

/-- Concrete paired Cook--Levin SPDP-transport condition. -/
abbrev CookLevinPairedPiPlusSPDPSubspaceTransport
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2) : Prop :=
  PiPlusSPDPSubspaceTransport M n hn2 htb hns
    (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)

/-- Concrete paired Cook--Levin subspace transport gives the rank-invariance
field. -/
theorem cookLevinPiPlusRankInvariantOfPair_of_spdpSubspaceTransport
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2)
    (htransport : CookLevinPairedPiPlusSPDPSubspaceTransport
      M n m hn2 htb hns hnpair) :
    PiPlusRankInvariant M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair) :=
  piPlusRankInvariant_of_spdpSubspaceTransport M n hn2 htb hns
    (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)
    htransport

/-- If SPDP subspace transport is known, the paired admissibility frontier only
needs the P-side upper bound and NP-side identity-minor preservation. -/
theorem paired_frontier_of_spdpSubspaceTransport
    (M : DTM) (n m : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hnpair : n = m * 2)
    (htransport : CookLevinPairedPiPlusSPDPSubspaceTransport
      M n m hn2 htb hns hnpair)
    (hp : PiPlusWidthRankPSide M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair))
    (hnp : PiPlusIdentityMinorPreservation M n hn2 htb hns
      (cookLevinPiPlusSATTransformOfPair M n m hn2 htb hns hnpair)) :
    CookLevinPairedPiPlusAdmissibilityFrontier M n m hn2 htb hns hnpair where
  rank_invariant :=
    cookLevinPiPlusRankInvariantOfPair_of_spdpSubspaceTransport
      M n m hn2 htb hns hnpair htransport
  width_rank_p_side := hp
  identity_minor_preservation := hnp

/-- Paper-scale SPDP-transport condition for the concrete `Pi+`. -/
abbrev PaperScalePiPlusSPDPSubspaceTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  CookLevinPairedPiPlusSPDPSubspaceTransport M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804

/-- Paper-scale SPDP subspace transport gives rank invariance for the concrete
paper-scale `Pi+` transform. -/
theorem cookLevinPiPlusRankInvariant_paperScale_of_spdpSubspaceTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (htransport : PaperScalePiPlusSPDPSubspaceTransport M htb hns) :
    PiPlusRankInvariant M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns) :=
  cookLevinPiPlusRankInvariantOfPair_of_spdpSubspaceTransport
    M (2 ^ 804) (2 ^ 803) paperScale_ge_two htb hns
    paperScale_pairing_2_804 htransport

/-- Paper-scale SPDP transport reduces the full admissibility frontier to the
remaining P-side and NP-side bounds. -/
theorem paperScale_frontier_of_spdpSubspaceTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (htransport : PaperScalePiPlusSPDPSubspaceTransport M htb hns)
    (hp : PiPlusWidthRankPSide M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns))
    (hnp : PiPlusIdentityMinorPreservation M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)) :
    PaperScalePiPlusAdmissibilityFrontier M htb hns :=
  paired_frontier_of_spdpSubspaceTransport M (2 ^ 804) (2 ^ 803)
    paperScale_ge_two htb hns paperScale_pairing_2_804 htransport hp hnp

/-! ## Axiom audit anchors -/

#print axioms piPlusRankInvariant_of_spdpSubspaceTransport
#print axioms cookLevinPiPlusRankInvariantOfPair_of_spdpSubspaceTransport
#print axioms paired_frontier_of_spdpSubspaceTransport
#print axioms cookLevinPiPlusRankInvariant_paperScale_of_spdpSubspaceTransport
#print axioms paperScale_frontier_of_spdpSubspaceTransport

end PallLean.Paper93.DeepMath.PathC
