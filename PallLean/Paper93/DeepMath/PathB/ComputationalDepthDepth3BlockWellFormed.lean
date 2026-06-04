import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ClauseGrouping
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafClauses

/-!
# Well-formedness of the block-decoder target `clauseGrouping (deepestSatSeq …)`

Toward the run-matching: the target `clauseGrouping (deepestSatSeq cs F σ)` is a list of **nonempty**
blocks, each block's entries drawn from the **end-state-readable** clauses `leafClauses`.  So the
decoder produces nonempty position-runs over a known clause family.

* `clauseGrouping_ne_nil` — every block of `clauseGrouping` is nonempty (`List.nil_notMem_splitBy`).
* `clauseGrouping_block_entry_mem_leafClauses` — every entry's clause in a block lies in
  `leafClauses cs (deepestEnd …)` (via the round-trip `clauseGrouping_flatten` +
  `deepestSatSeq_clause_mem_leafClauses`).

These fix the shape of the decoder's output; the remaining work is the assignment of the label's
position-runs to the clauses in order.  Not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Every block of `clauseGrouping` is nonempty. -/
theorem clauseGrouping_ne_nil (l : List (Clause n × ℕ)) {blk : List (Clause n × ℕ)}
    (h : blk ∈ clauseGrouping l) : blk ≠ [] := by
  intro hnil
  rw [hnil] at h
  exact (List.nil_notMem_splitBy _ l) h

/-- Every entry's clause in a block of `clauseGrouping (deepestSatSeq …)` is end-state-readable. -/
theorem clauseGrouping_block_entry_mem_leafClauses (cs : List (Clause n)) (F : ℕ)
    (σ : Fin n → Option Bool) {blk : List (Clause n × ℕ)} {C : Clause n} {p : ℕ}
    (hblk : blk ∈ clauseGrouping (deepestSatSeq cs F σ)) (hentry : (C, p) ∈ blk)
    (hsat : SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false) :
    C ∈ leafClauses cs (deepestEnd cs F σ) := by
  have hmem : (C, p) ∈ deepestSatSeq cs F σ := by
    rw [← clauseGrouping_flatten (deepestSatSeq cs F σ)]
    exact List.mem_flatten_of_mem hblk hentry
  exact deepestSatSeq_clause_mem_leafClauses cs F σ hmem hsat

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.clauseGrouping_ne_nil
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.clauseGrouping_block_entry_mem_leafClauses
