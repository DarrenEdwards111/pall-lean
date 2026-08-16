import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFGreedyMatching

/-!
# 2-CNF final structural dispatcher

This file reconnects the support-level greedy matching to actual CNF syntax.  Clause supports are the variables
appearing in their literals.  A support cover is proved to be exactly the literal-cover hypothesis consumed by the
end-to-end residual solver.  Applying the greedy saturated matching and the threshold `3*k` dichotomy therefore
constructs either a large disjoint clause-support family or a semantic cover of fewer than `6*k` variables.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding
open PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCover
open PallLean.Paper93.DeepMath.PathB.TwoCNFGreedyMatching
open PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction

variable {n : ℕ}

/-- Variables occurring in a clause. -/
def clauseSupport (clause : Finset (Literal n)) : Finset (Fin n) := clause.image Prod.fst

/-- The support hypergraph of a CNF. -/
def supportFamily (φ : CNF n) : Finset (Finset (Fin n)) := φ.image clauseSupport

theorem clauseSupport_card_le (clause : Finset (Literal n)) :
    (clauseSupport clause).card ≤ clause.card := Finset.card_image_le

theorem clauseSupport_nonempty {clause : Finset (Literal n)} (h : clause.Nonempty) :
    (clauseSupport clause).Nonempty := by
  obtain ⟨l, hl⟩ := h
  exact ⟨l.1, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩

/-- A cover of all clause supports is a literal cover of the original CNF. -/
theorem literalCover_of_hitsAll_supportFamily
    (φ : CNF n) (cover : Finset (Fin n))
    (hhit : HitsAll (supportFamily φ) cover) : LiteralCover φ cover := by
  intro clause hc
  have hsMem : clauseSupport clause ∈ supportFamily φ :=
    Finset.mem_image.mpr ⟨clause, hc, rfl⟩
  obtain ⟨v, hvSupport, hvCover⟩ := Finset.not_disjoint_iff.mp (hhit _ hsMem)
  obtain ⟨l, hl, hlv⟩ := Finset.mem_image.mp hvSupport
  exact ⟨l, hl, by simpa [hlv] using hvCover⟩

/-- The greedy support matching used by the final dispatcher. -/
noncomputable def constructedMatching (φ : CNF n) : Finset (Finset (Fin n)) :=
  (greedyMatching (supportFamily φ).toList).toFinset

/-- The variables owned by the constructed matching. -/
noncomputable def constructedCover (φ : CNF n) : Finset (Fin n) := matchingSupport (constructedMatching φ)

theorem constructedMatching_saturated
    (φ : CNF n) (hnonempty : ∀ clause ∈ φ, clause.Nonempty) :
    SaturatedMatching (supportFamily φ) (constructedMatching φ) := by
  apply greedyMatching_saturated
  intro support hs
  obtain ⟨clause, hc, rfl⟩ := Finset.mem_image.mp hs
  exact clauseSupport_nonempty (hnonempty clause hc)

/-- Every support in a width-two CNF has cardinality at most two. -/
theorem supportFamily_width_two
    (φ : CNF n) (hwidth : ∀ clause ∈ φ, clause.card ≤ 2) :
    ∀ support ∈ supportFamily φ, support.card ≤ 2 := by
  intro support hs
  obtain ⟨clause, hc, rfl⟩ := Finset.mem_image.mp hs
  exact (clauseSupport_card_le clause).trans (hwidth clause hc)

/-- **Constructive semantic matching-or-cover dispatcher (proved).** -/
theorem constructed_matching_or_cover
    (φ : CNF n)
    (hnonempty : ∀ clause ∈ φ, clause.Nonempty)
    (hwidth : ∀ clause ∈ φ, clause.card ≤ 2) (k : ℕ) :
    3 * k ≤ (constructedMatching φ).card ∨
      (LiteralCover φ (constructedCover φ) ∧ (constructedCover φ).card < 6 * k) := by
  have hsat := constructedMatching_saturated φ hnonempty
  have hdich := saturatedMatching_dichotomy (supportFamily_width_two φ hwidth) hsat (3 * k)
  rcases hdich with hlarge | ⟨hhit, hsmall⟩
  · exact Or.inl hlarge
  · right
    refine ⟨literalCover_of_hitsAll_supportFamily φ (constructedCover φ) hhit, ?_⟩
    unfold constructedCover
    omega

/-- The small-cover outcome is immediately consumable by the verified branch solver. -/
theorem constructed_matching_or_solved_cover
    (φ : CNF n)
    (hnonempty : ∀ clause ∈ φ, clause.Nonempty)
    (hwidth : ∀ clause ∈ φ, clause.card ≤ 2) (k : ℕ) :
    3 * k ≤ (constructedMatching φ).card ∨
      ((constructedCover φ).card < 6 * k ∧
        ∀ ρ : PartialAssignment n, AssignsCover ρ (constructedCover φ) →
          (CoverLeafAccepts ρ φ ↔ ∃ x, Completes ρ x ∧ evalCNF x φ)) := by
  rcases constructed_matching_or_cover φ hnonempty hwidth k with hlarge | ⟨hcover, hsmall⟩
  · exact Or.inl hlarge
  · right
    exact ⟨hsmall, fun ρ hassign => coverLeafAccepts_iff φ (constructedCover φ) ρ hwidth hcover hassign⟩

/-- The already-integrated matching/cover work budget is strictly sub-cube. -/
theorem constructed_dispatcher_work_lt_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 6 * k ≤ n) :
    PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout.combined2CNFWork n k < 2 ^ n :=
  PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCoverCashout.combined2CNFWork_lt_cube n k hk hkn

end PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher.literalCover_of_hitsAll_supportFamily
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher.constructed_matching_or_cover
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher.constructed_matching_or_solved_cover
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFFinalDispatcher.constructed_dispatcher_work_lt_cube
