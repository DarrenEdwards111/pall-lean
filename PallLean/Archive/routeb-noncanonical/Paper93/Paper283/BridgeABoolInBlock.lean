import PallLean.CookLevinDefs
import PallLean.Paper93.Paper283.BridgeACookLevinLocalQvCandidate
import PallLean.Paper93.Paper283.RouteBBridgeARealCompilerQvFrontier

/-!
# Bridge A provenance: booleanity at vertex `v` lies in `v`'s locality block

For the actual `cook_levin_compilation` and the locality partition with block
size `3`, the booleanity constraint `boolLC n v` has support `{v}`, so its
unique support variable is assigned by the compiler partition to the block
`T.partition.assign v`.  Hence `boolLC n v` is a member of the filtered list
`cookLevinConstraintsTouchingBlock T (T.partition.assign v)` that defines the
real local block product `cookLevinLocalBlockQ M n hn htb hns _`.

This is the "kappa = 1" provenance lemma for Bridge A:  the booleanity factor
at `v` is one of the factors entering the local-block polynomial used to
witness the rank-one part of the per-vertex bound.

The companion file `RouteBBridgeARealCompilerQvFrontier.lean` already proves
the analogous statement for its sibling predicate `constraintTouchesBlock`
(see `boolLC_mem_compilerBlockConstraints_self`).  This file establishes the
same provenance for the predicate `cookLevinConstraintTouchesBlock` actually
used by `cookLevinLocalBlockQ`.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial PaperFaithfulSeparation MultilinearSPDP

attribute [local instance] Classical.dec

/-- The booleanity constraint `boolLC n v` touches the locality block to which
the compiler partition assigns `v`. -/
theorem cookLevin_boolLC_cookLevinConstraintTouchesBlock_self
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    cookLevinConstraintTouchesBlock
        (cook_levin_compilation M n hn htb hns)
        ((cook_levin_compilation M n hn htb hns).partition.assign v)
        (boolLC n v) := by
  -- The unique support variable of `boolLC n v` is `v` itself, and it is
  -- assigned to the very block we are filtering for.
  refine ⟨v, ?_, rfl⟩
  -- `(boolLC n v).support = {v}`.
  show v ∈ (boolLC n v).support
  unfold boolLC
  simp

/-- Booleanity provenance for Bridge A `kappa = 1`:  `boolLC n v` is a member
of the filtered constraint list whose product defines `cookLevinLocalBlockQ`
at the locality block containing `v`. -/
theorem boolLC_mem_cookLevinConstraintsTouchingBlock_self
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (v : Fin (cook_levin_compilation M n hn htb hns).numVars) :
    boolLC n v ∈
      cookLevinConstraintsTouchingBlock
        (cook_levin_compilation M n hn htb hns)
        ((cook_levin_compilation M n hn htb hns).partition.assign v) := by
  classical
  unfold cookLevinConstraintsTouchingBlock
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · exact boolLC_mem_cookLevin_constraints M n hn htb hns v
  · apply decide_eq_true
    exact cookLevin_boolLC_cookLevinConstraintTouchesBlock_self
      M n hn htb hns v

/-- Convenience reformulation:  for any vertex-to-block map that sends `v` to
the actual locality block of `v`, the booleanity constraint at `v` lies in the
filtered list at `blockOfVertex v`. -/
theorem boolLC_mem_cookLevinConstraintsTouchingBlock_blockOfVertex
    {N : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (blockOfVertex :
      Fin N -> Fin (cook_levin_compilation M n hn htb hns).partition.numBlocks)
    (vertexVar :
      Fin N -> Fin (cook_levin_compilation M n hn htb hns).numVars)
    (hcompat :
      ∀ v : Fin N,
        (cook_levin_compilation M n hn htb hns).partition.assign
            (vertexVar v) =
          blockOfVertex v)
    (v : Fin N) :
    boolLC n (vertexVar v) ∈
      cookLevinConstraintsTouchingBlock
        (cook_levin_compilation M n hn htb hns)
        (blockOfVertex v) := by
  have hbase :=
    boolLC_mem_cookLevinConstraintsTouchingBlock_self
      M n hn htb hns (vertexVar v)
  -- Rewrite the assigned block to the user-supplied `blockOfVertex v`.
  rw [hcompat v] at hbase
  exact hbase

/-! ## Axiom audit anchors -/

#print axioms cookLevin_boolLC_cookLevinConstraintTouchesBlock_self
#print axioms boolLC_mem_cookLevinConstraintsTouchingBlock_self
#print axioms boolLC_mem_cookLevinConstraintsTouchingBlock_blockOfVertex

end PallLean.Paper93.Paper283
