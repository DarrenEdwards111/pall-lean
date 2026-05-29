import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayeredThresholdInvariant
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSignRankFactorization

/-!
# First concrete handhold below the layered threshold frontier

`ComputationalDepthLayeredThresholdInvariant` gives the finite-prefix climb
interface, but its transfer fields are intentionally not filled.  This file
installs the first **concrete** threshold-adjacent handhold that is already known
in this development: the depth-2 / UPP / sign-rank boundary, in the precise
split-rank form already proved by `ComputationalDepthSignRankFactorization`.

Honest scope:

* This is a real handhold: a split-rank threshold representation with `s` terms
  has sign-rank at most `s`, hence a Forster/sign-rank lower bound rules it out
  below budget.
* This is **not** a depth-`2 → 3` transfer theorem and does not instantiate the
  full `LayerTransferStableUpTo` field for arbitrary threshold layers.
* It marks the first installed rung: depth-2/split-UPP is controlled by
  sign-rank.  The higher threshold-composition rungs remain the frontier.
-/

namespace PallLean.Paper93.DeepMath.PathB

open scoped BigOperators

/-! ## Installed handhold: split-rank depth-2 threshold ⇒ sign-rank bound -/

/-- **First concrete handhold.**  A threshold sign of `s` split rank-one terms
has sign-rank at most `s`.  This is the formal depth-2/UPP boundary in the
rank-factorized model: the realizer matrix is explicitly `B * C`, with `s`
intermediate coordinates.

This is a real preservation theorem, not a carried stability field. -/
theorem first_handhold_splitSparse_hasSignRankLE {m n s : Nat}
    (u : Fin s -> Fin m -> ℝ) (v : Fin s -> Fin n -> ℝ)
    (hne : ∀ i j, (∑ k, u k i * v k j) ≠ 0) :
    HasSignRankLE (SplitSparseThreshold s u v) s :=
  splitSparseThreshold_hasSignRankLE u v hne

/-- **First-handhold lower-bound consequence.**  If a matrix/function has
sign-rank lower bound `B` (for example by Forster), then no split-rank depth-2
threshold representation with fewer than `B` terms computes it. -/
theorem first_handhold_no_small_splitSparse {m n B s : Nat}
    {M : Fin m -> Fin n -> Bool}
    (hF : ForsterLowerBound M B)
    (u : Fin s -> Fin m -> ℝ) (v : Fin s -> Fin n -> ℝ)
    (hne : ∀ i j, (∑ k, u k i * v k j) ≠ 0)
    (hcomp : SplitSparseThreshold s u v = M) (hsmall : s < B) : False :=
  no_small_splitThreshold hF u v hne hcomp hsmall

/-- Single split bipartite halfspaces are the base gate of the handhold: the
matrix `sign(αᵢ + βⱼ)` has sign-rank at most `2`. -/
theorem first_handhold_bipartiteHalfspace_hasSignRankLE_two {m n : Nat}
    (α : Fin m -> ℝ) (β : Fin n -> ℝ)
    (hne : ∀ i j, α i + β j ≠ 0) :
    HasSignRankLE (bipartiteHalfspace α β) 2 :=
  bipartiteHalfspace_hasSignRankLE_two α β hne

#print axioms first_handhold_splitSparse_hasSignRankLE
#print axioms first_handhold_no_small_splitSparse
#print axioms first_handhold_bipartiteHalfspace_hasSignRankLE_two

end PallLean.Paper93.DeepMath.PathB
