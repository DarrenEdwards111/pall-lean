import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFClauseExtraction

/-!
# Verified 2-CNF observer/restriction pipeline capstone

This file packages the width-two base-case components behind one theorem interface: constructed structural dispatch,
semantic correctness of every small-cover branch, signed extraction for proper binary clauses, exact canonical
large-matching branch counts, and strict combined work accounting.

It deliberately makes no claim about width-three CNF.  The extension from this capstone to an NP-complete class is the
new switching/restriction theorem required by the observer programme.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFPipelineCapstone

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding
open PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction
open PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher
open PallLean.Paper93.DeepMath.PathB.TwoCNFLargeMatchingSemantics
open PallLean.Paper93.DeepMath.PathB.TwoCNFClauseExtraction

variable {n : ℕ}

/-- All externally consumed guarantees of the verified width-two pipeline. -/
structure PipelineGuarantees (φ : CNF n) (k : ℕ) : Prop where
  dispatch :
    3 * k ≤ (constructedMatching φ).card ∨
      ((constructedCover φ).card < 6 * k ∧
        ∀ ρ : PartialAssignment n, AssignsCover ρ (constructedCover φ) →
          (CoverLeafAccepts ρ φ ↔ ∃ x, Completes ρ x ∧ evalCNF x φ))
  work :
    PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout.combined2CNFWork n k < 2 ^ n
  properClauseExtraction :
    ∀ (C : ProperBinaryClause n) (x : Fin n → Bool),
      evalClause x C.clause ↔
        x (endpoint C 0) = sign C 0 ∨ x (endpoint C 1) = sign C 1
  matchingBranchCount :
    ∀ {m : ℕ} (signs : Fin m → Bool × Bool) (r : ℕ),
      Fintype.card (MatchingBranch signs r) = 3 ^ m * 2 ^ r

/-- **Width-two pipeline capstone (proved).** -/
theorem verified_two_cnf_pipeline
    (φ : CNF n)
    (hnonempty : ∀ clause ∈ φ, clause.Nonempty)
    (hwidth : ∀ clause ∈ φ, clause.card ≤ 2)
    (k : ℕ) (hk : 1 ≤ k) (hkn : 6 * k ≤ n) :
    PipelineGuarantees φ k where
  dispatch := constructed_matching_or_solved_cover φ hnonempty hwidth k
  work := constructed_dispatcher_work_lt_cube n k hk hkn
  properClauseExtraction := fun C x => evalClause_iff_extracted C x
  matchingBranchCount := fun signs r => card_matchingBranch signs r

end PallLean.Paper93.DeepMath.PathB.TwoCNFPipelineCapstone

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFPipelineCapstone.verified_two_cnf_pipeline
