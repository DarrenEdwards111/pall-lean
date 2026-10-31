import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelTowerSuperpolyScale

/-!
# Semantic Hankel product capture

This file formalizes the exact boundary found by the finite Mikoshi audit.
For a stage with semantic prefix/continuation rank `rank i`, use the
representation-invariant load `rank i - 1`.  If successive stages contain a
genuine independent semantic product, their ranks square.  Starting at rank
at least two, this implies the solver-capture recurrence.

The product law is an explicit field, not an axiom and not a consequence of
one-bit solver correctness.  Copying or sharing a rank does not satisfy the
recurrence.  The remaining unrestricted theorem must construct this product
law from solver-relative reflection while preserving polynomial encoding.
-/

namespace PallLean.Paper93.DeepMath.PathB.HankelProductCapture

open PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale

/-- Rank-minus-one semantic load. -/
def hankelLoad (rank : Nat → Nat) (i : Nat) : Nat := rank i - 1

/-- The precise independent-product payload.  It deliberately records the
semantic rank-square law rather than postulating solver capture directly. -/
structure SemanticProductEmbedding (rank : Nat → Nat) : Prop where
  baseRank : 2 ≤ rank 0
  squareRank : ∀ i, rank (i + 1) = rank i * rank i

theorem rank_ge_two {rank : Nat → Nat}
    (product : SemanticProductEmbedding rank) :
    ∀ i, 2 ≤ rank i := by
  intro i
  induction i with
  | zero => exact product.baseRank
  | succ i ih =>
      rw [product.squareRank i]
      nlinarith

/-- A genuine semantic product embedding supplies the exact tower doubling
needed by the already-certified superpolynomial scale theorem. -/
theorem productEmbedding_to_solverCapture {rank : Nat → Nat}
    (product : SemanticProductEmbedding rank) :
    SolverCaptureDoubling (hankelLoad rank) := by
  constructor
  · have hbase := product.baseRank
    simp only [hankelLoad]
    omega
  · intro i
    have htwo : 2 ≤ rank i := rank_ge_two product i
    rw [hankelLoad, hankelLoad, product.squareRank i]
    have hone : 1 ≤ rank i := by omega
    have hreconstruct : rank i - 1 + 1 = rank i := Nat.sub_add_cancel hone
    apply Nat.le_sub_of_add_le
    nlinarith [sq_nonneg (rank i - 1 : Int)]

/-- Reusing the same nonzero rank at the next level cannot meet even one
rank-minus-one doubling step.  Fanout and syntactic duplication therefore do
not constitute semantic product capture. -/
theorem copiedRank_fails_doubling {r : Nat} (_hr : 2 ≤ r) :
    ¬ 2 * (r - 1) + 1 ≤ r - 1 := by
  omega

/-- The concrete rank-two boundary observed by exhaustive finite testing:
copying keeps load one, whereas a product rank of four gives load three. -/
theorem rankTwo_copy_fails : ¬ 2 * (2 - 1) + 1 ≤ 2 - 1 := by
  omega

theorem rankTwo_product_succeeds :
    2 * (2 - 1) + 1 ≤ (2 * 2) - 1 := by
  omega

/-- Once the semantic product law and a scale witness are available, the
rank-minus-one load breaks the stated polynomial budget. -/
theorem productEmbedding_breaks_polynomial_at_witness
    {rank : Nat → Nat} (product : SemanticProductEmbedding rank)
    {n k C : Nat} (scale : SuperpolyScaleWitness n k C) :
    n ^ C < hankelLoad rank k :=
  polynomial_budget_broken (productEmbedding_to_solverCapture product) scale

end PallLean.Paper93.DeepMath.PathB.HankelProductCapture

#print axioms PallLean.Paper93.DeepMath.PathB.HankelProductCapture.rank_ge_two
#print axioms PallLean.Paper93.DeepMath.PathB.HankelProductCapture.productEmbedding_to_solverCapture
#print axioms PallLean.Paper93.DeepMath.PathB.HankelProductCapture.copiedRank_fails_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.HankelProductCapture.productEmbedding_breaks_polynomial_at_witness
