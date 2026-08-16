import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFGreedyMatching

/-!
# Width-three CNF: matching/cover accounting stress test

This is the first width-three stress test of the verified observer/restriction pipeline.  A proper signed ternary
clause has seven satisfying local states.  Six disjoint clauses therefore cost `7^6 = 117649 < 2^17`, saving one bit
per six-clause block relative to their eighteen owned variables.

A saturated matching of width-three supports gives the complementary arm: below threshold `6*k`, its union is a
cover of fewer than `18*k` variables.  Restricting that cover leaves width at most two.  The present file proves the
structural and exponent accounting only; the semantic restriction-to-2-CNF bridge is the next integration theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.ThreeCNFMatchingCoverAccounting

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCover
open PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding
open PallLean.Paper93.DeepMath.PathB.TwoCNFCoverRestriction

variable {V : Type*} [DecidableEq V]

/-- Satisfying local states of a signed ternary clause. -/
abbrev SignedTripleState (first second third : Bool) :=
  {p : Bool × (Bool × Bool) // p.1 = first ∨ p.2.1 = second ∨ p.2.2 = third}

/-- Every signed ternary clause has exactly seven satisfying local states. -/
theorem card_signedTripleState (first second third : Bool) :
    Fintype.card (SignedTripleState first second third) = 7 := by
  cases first <;> cases second <;> cases third <;> decide

/-- A width-three selected family owns at most three variables per selected clause. -/
theorem matchingSupport_card_le_three_mul
    {E M : Finset (Finset V)}
    (hwidth : ∀ e ∈ E, e.card ≤ 3) (hM : M ⊆ E) :
    (matchingSupport M).card ≤ 3 * M.card := by
  calc
    (matchingSupport M).card ≤ ∑ e ∈ M, e.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ M, 3 := Finset.sum_le_sum fun e he => hwidth e (hM he)
    _ = 3 * M.card := by simp [Nat.mul_comm]

/-- Width-three matching/cover dichotomy for any saturated matching. -/
theorem saturatedMatching_dichotomy_three
    {E M : Finset (Finset V)}
    (hwidth : ∀ e ∈ E, e.card ≤ 3)
    (hmatch : SaturatedMatching E M) (t : ℕ) :
    t ≤ M.card ∨ (HitsAll E (matchingSupport M) ∧ (matchingSupport M).card < 3 * t) := by
  by_cases hlarge : t ≤ M.card
  · exact Or.inl hlarge
  · right
    refine ⟨hmatch.saturated, ?_⟩
    have hcard := matchingSupport_card_le_three_mul hwidth hmatch.subfamily
    omega

/-- Assigning a variable cover removes at least one literal from every surviving width-three clause. -/
theorem residualClause_card_le_two
    {n : ℕ} (φ : CNF n) (cover : Finset (Fin n)) (ρ : PartialAssignment n)
    (hwidth : ∀ clause ∈ φ, clause.card ≤ 3)
    (hcover : LiteralCover φ cover) (hassign : AssignsCover ρ cover)
    {clause : Finset (Literal n)} (hclause : clause ∈ φ) :
    (residualClause ρ clause).card ≤ 2 := by
  have hsubset : residualClause ρ clause ⊆ clause := by
    intro l hl
    exact (Finset.mem_filter.mp hl).1
  obtain ⟨l, hl, hlcover⟩ := hcover clause hclause
  obtain ⟨value, hvalue⟩ := hassign l.1 hlcover
  have hnotmem : l ∉ residualClause ρ clause := by
    intro hres
    have hfree := (Finset.mem_filter.mp hres).2
    rw [hfree] at hvalue
    contradiction
  have hproper : residualClause ρ clause ⊂ clause :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, fun heq => hnotmem (heq.symm ▸ hl)⟩
  have hlt : (residualClause ρ clause).card < clause.card := Finset.card_lt_card hproper
  have hthree := hwidth clause hclause
  omega

/-- Conservative work of six-clause matching blocks. -/
def matchingArmWork (n k : ℕ) : ℕ := 117649 ^ k * 2 ^ (n - 18 * k)

/-- Conservative work of the strict-small-cover arm. -/
def coverArmWork (k : ℕ) : ℕ := 2 ^ (18 * k - 1)

/-- Worst-case work of the width-three matching/cover stress test. -/
def combined3CNFWork (n k : ℕ) : ℕ := max (matchingArmWork n k) (coverArmWork k)

/-- Six independent ternary clauses save one bit across their eighteen variables. -/
theorem seven_six_blocks_le_seventeen_bits (k : ℕ) :
    117649 ^ k ≤ 2 ^ (17 * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by norm_num) k

theorem matchingArmWork_le_half_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 18 * k ≤ n) :
    matchingArmWork n k ≤ 2 ^ (n - 1) := by
  unfold matchingArmWork
  calc
    117649 ^ k * 2 ^ (n - 18 * k) ≤ 2 ^ (17 * k) * 2 ^ (n - 18 * k) :=
      Nat.mul_le_mul_right _ (seven_six_blocks_le_seventeen_bits k)
    _ = 2 ^ (17 * k + (n - 18 * k)) := by rw [Nat.pow_add]
    _ = 2 ^ (n - k) := by congr 1 <;> omega
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem coverArmWork_le_half_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 18 * k ≤ n) :
    coverArmWork k ≤ 2 ^ (n - 1) := by
  unfold coverArmWork
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Width-three accounting survives:** both structural arms are strictly below exhaustive search. -/
theorem combined3CNFWork_lt_cube (n k : ℕ) (hk : 1 ≤ k) (hkn : 18 * k ≤ n) :
    combined3CNFWork n k < 2 ^ n := by
  calc
    combined3CNFWork n k ≤ 2 ^ (n - 1) := by
      rw [combined3CNFWork, max_le_iff]
      exact ⟨matchingArmWork_le_half_cube n k hk hkn, coverArmWork_le_half_cube n k hk hkn⟩
    _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)

end PallLean.Paper93.DeepMath.PathB.ThreeCNFMatchingCoverAccounting

#print axioms PallLean.Paper93.DeepMath.PathB.ThreeCNFMatchingCoverAccounting.card_signedTripleState
#print axioms PallLean.Paper93.DeepMath.PathB.ThreeCNFMatchingCoverAccounting.saturatedMatching_dichotomy_three
#print axioms PallLean.Paper93.DeepMath.PathB.ThreeCNFMatchingCoverAccounting.residualClause_card_le_two
#print axioms PallLean.Paper93.DeepMath.PathB.ThreeCNFMatchingCoverAccounting.combined3CNFWork_lt_cube
