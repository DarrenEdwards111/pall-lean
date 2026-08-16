import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossBranchQuotientRank

/-!
# Saturation obstruction for cross-branch quotient rank

The quotient-rank bound gives a saving only when projected queried columns are dependent.  This file proves the exact
opposite regime: if the projected columns are linearly independent and projection does not identify queried columns,
then their quotient rank equals the raw query count `q`.

Hence no universal `d < q` collision theorem can follow from parity-layer syntax alone.  A successful restriction
lemma must derive projected dependence from additional structure of the upper layer / separator, or switch to a
nonlinear simplification measure.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRankSaturation

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRank

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

/-- Independent projected queried columns have rank equal to their distinct projected count. -/
theorem quotientQueryRank_eq_projected_card_of_independent (kept queried : Finset V)
    (hind : LinearIndepOn (ZMod 2) id
      (↑(projectedQueriedSet kept queried) :
        Set (V ⧸ Submodule.span (ZMod 2) (↑kept : Set V)))) :
    quotientQueryRank kept queried = (projectedQueriedSet kept queried).card := by
  exact finrank_span_finset_eq_card hind

/-- **Quotient-rank saturation (proved).**  If projection is injective on queried columns and their images are
linearly independent, then `d=q`: cross-branch quotient rank has no deficit to exploit. -/
theorem quotientQueryRank_eq_query_card_of_independent (kept queried : Finset V)
    (hinj : Set.InjOn (Submodule.mkQ (Submodule.span (ZMod 2) (↑kept : Set V)))
      (queried : Set V))
    (hind : LinearIndepOn (ZMod 2) id
      (↑(projectedQueriedSet kept queried) :
        Set (V ⧸ Submodule.span (ZMod 2) (↑kept : Set V)))) :
    quotientQueryRank kept queried = queried.card := by
  rw [quotientQueryRank_eq_projected_card_of_independent kept queried hind]
  exact Finset.card_image_of_injOn hinj

/-- In the independent projected-column regime, the desired strict rank deficit is impossible. -/
theorem not_quotientRank_lt_query_card_of_independent (kept queried : Finset V)
    (hinj : Set.InjOn (Submodule.mkQ (Submodule.span (ZMod 2) (↑kept : Set V)))
      (queried : Set V))
    (hind : LinearIndepOn (ZMod 2) id
      (↑(projectedQueriedSet kept queried) :
        Set (V ⧸ Submodule.span (ZMod 2) (↑kept : Set V)))) :
    ¬ quotientQueryRank kept queried < queried.card := by
  rw [quotientQueryRank_eq_query_card_of_independent kept queried hinj hind]
  exact Nat.lt_irrefl _

end PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRankSaturation

#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRankSaturation.quotientQueryRank_eq_query_card_of_independent
#print axioms PallLean.Paper93.DeepMath.PathB.CrossBranchQuotientRankSaturation.not_quotientRank_lt_query_card_of_independent
