import PallLean.Paper93.DeepMath.PathC.PiPlusHolographicFaithfulLiftSemantics

/-!
# Boundary-lattice no-go for the holographic pivot

This file tests the proposed rescue:

* put an SPDP/God-Move-style lattice on the boundary;
* require faithful join/meet-preserving reconstruction of the bulk;
* hope the lattice structure escapes the boundary/bulk capacity obstruction.

The conclusion is negative in the precise finite setting used by Path C.
Any faithful join/meet-preserving reconstruction contains, in particular, an
injective coding of independent bulk witnesses into boundary-lift codes.
Therefore it implies the same cardinal lift bound

```lean
bulk.rank <= liftCost boundary.rank
```

and the already-proved boundary/bulk gap rules it out.

So a boundary lattice equivalent to SPDP/God-Move can strengthen the
presentation of the obstruction, but it cannot rescue the proof route unless
it adds genuinely new non-rank, non-local, instance-sensitive content.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- A finite boundary/bulk lattice reconstruction surface.

The operations are intentionally explicit.  The bulk side has `bulk.rank`
independent witnesses.  The boundary side has only
`liftCost boundary.rank` code slots.  A faithful lattice reconstruction must
encode bulk witnesses injectively and preserve the two lattice operations.

The no-go below does not need any lattice laws: associativity, absorption, and
distributivity can only add constraints.  The cardinal obstruction already
fires from injective faithfulness plus finite boundary capacity. -/
structure BoundaryBulkLatticeReconstruction
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (boundary : HolographicBoundaryLayer M n hn2 htb hns)
    (bulk : HolographicBulkLayer M n hn2 htb hns)
    (liftCost : Nat -> Nat) where
  bulkJoin :
    Fin bulk.rank -> Fin bulk.rank -> Fin bulk.rank
  bulkMeet :
    Fin bulk.rank -> Fin bulk.rank -> Fin bulk.rank
  boundaryJoin :
    Fin (liftCost boundary.rank) ->
      Fin (liftCost boundary.rank) ->
        Fin (liftCost boundary.rank)
  boundaryMeet :
    Fin (liftCost boundary.rank) ->
      Fin (liftCost boundary.rank) ->
        Fin (liftCost boundary.rank)
  encodeBulkWitness :
    Fin bulk.rank -> Fin (liftCost boundary.rank)
  encodeBulkWitness_injective :
    Function.Injective encodeBulkWitness
  map_join :
    forall a b,
      encodeBulkWitness (bulkJoin a b) =
        boundaryJoin (encodeBulkWitness a) (encodeBulkWitness b)
  map_meet :
    forall a b,
      encodeBulkWitness (bulkMeet a b) =
        boundaryMeet (encodeBulkWitness a) (encodeBulkWitness b)

/-- A faithful lattice reconstruction forgets to a faithful decoder. -/
def BoundaryBulkLatticeReconstruction.toDecoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    (L : BoundaryBulkLatticeReconstruction boundary bulk liftCost) :
    BoundaryBulkFaithfulDecoder boundary bulk liftCost where
  encodeBulkWitness := L.encodeBulkWitness
  encodeBulkWitness_injective := L.encodeBulkWitness_injective

/-- Therefore faithful lattice reconstruction implies the same raw lift bound. -/
theorem faithful_boundary_to_bulk_of_latticeReconstruction
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    (L : BoundaryBulkLatticeReconstruction boundary bulk liftCost) :
    bulk.rank <= liftCost boundary.rank :=
  faithful_boundary_to_bulk_of_decoder L.toDecoder

/-- Conversely, any faithful decoder can be made into a degenerate
join/meet-preserving reconstruction by taking both operations to be left
projection.  This shows that, absent fixed external lattice operations, the
lattice socket is exactly the decoder socket. -/
def latticeReconstruction_of_decoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    (D : BoundaryBulkFaithfulDecoder boundary bulk liftCost) :
    BoundaryBulkLatticeReconstruction boundary bulk liftCost where
  bulkJoin := fun a _ => a
  bulkMeet := fun a _ => a
  boundaryJoin := fun a _ => a
  boundaryMeet := fun a _ => a
  encodeBulkWitness := D.encodeBulkWitness
  encodeBulkWitness_injective := D.encodeBulkWitness_injective
  map_join := by intro a b; rfl
  map_meet := by intro a b; rfl

/-- Lattice reconstruction existence is equivalent to decoder existence, unless
some additional, externally fixed lattice semantics is imposed. -/
theorem exists_latticeReconstruction_iff_exists_decoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat} :
    Nonempty (BoundaryBulkLatticeReconstruction boundary bulk liftCost) ↔
      Nonempty (BoundaryBulkFaithfulDecoder boundary bulk liftCost) := by
  constructor
  · intro h
    rcases h with ⟨L⟩
    exact ⟨L.toDecoder⟩
  · intro h
    rcases h with ⟨D⟩
    exact ⟨latticeReconstruction_of_decoder D⟩

/-- Lattice reconstruction exists exactly when the raw cardinal lift bound
holds.  A boundary lattice equivalent to SPDP/God-Move therefore cannot avoid
the faithful-lift frontier. -/
theorem exists_latticeReconstruction_iff_faithful_boundary_to_bulk
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat} :
    Nonempty (BoundaryBulkLatticeReconstruction boundary bulk liftCost) ↔
      bulk.rank <= liftCost boundary.rank := by
  exact exists_latticeReconstruction_iff_exists_decoder.trans
    exists_decoder_iff_faithful_boundary_to_bulk

/-- No faithful boundary lattice compression can exist under the same
boundary/bulk gap used by the holographic pivot. -/
theorem no_faithfulBoundaryLatticeCompression_of_boundary_bulk_gap
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    (liftCost_mono : Monotone liftCost)
    (boundary_P_bound : boundary.rank <= n ^ 200)
    (bulk_NP_lower :
      DecidesSAT M -> Nat.choose (n / 3) (Nat.log 2 n) <= bulk.rank)
    (holographic_gap :
      liftCost (n ^ 200) < Nat.choose (n / 3) (Nat.log 2 n))
    (hdec : DecidesSAT M) :
    Not (Nonempty (BoundaryBulkLatticeReconstruction boundary bulk liftCost)) := by
  intro hlat
  have hdecoder : Nonempty (BoundaryBulkFaithfulDecoder boundary bulk liftCost) :=
    exists_latticeReconstruction_iff_exists_decoder.mp hlat
  exact no_decoder_of_boundary_bulk_gap
    liftCost_mono boundary_P_bound bulk_NP_lower holographic_gap hdec hdecoder

/-! ## Axiom audit anchors -/

#print axioms BoundaryBulkLatticeReconstruction.toDecoder
#print axioms faithful_boundary_to_bulk_of_latticeReconstruction
#print axioms latticeReconstruction_of_decoder
#print axioms exists_latticeReconstruction_iff_exists_decoder
#print axioms exists_latticeReconstruction_iff_faithful_boundary_to_bulk
#print axioms no_faithfulBoundaryLatticeCompression_of_boundary_bulk_gap

end PallLean.Paper93.DeepMath.PathC
