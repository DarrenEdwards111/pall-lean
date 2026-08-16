import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDisjoint2CNFSwitching

/-!
# Width-two overlap: the matching-or-cover bridge

Represent every 2-CNF clause only by its variable support, of cardinality at most two.  A saturated matching is a
pairwise-disjoint subfamily whose union intersects every clause support.  Its union is therefore a variable cover.
Because each selected support has size at most two, the cover has size at most twice the matching.

Consequently, for every threshold `t`, either the matching contains at least `t` independent clauses (feeding the
disjoint-clause switching engine), or all clauses are hit by fewer than `2*t` variables (a separator/backdoor).
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCover

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- Variables owned by a selected family of clause supports. -/
def matchingSupport (M : Finset (Finset V)) : Finset V := M.biUnion id

/-- `cover` intersects every clause support in `E`. -/
def HitsAll (E : Finset (Finset V)) (cover : Finset V) : Prop :=
  ∀ e ∈ E, ¬Disjoint e cover

/-- The operational property of a maximal disjoint clause family: its endpoints hit every clause. -/
structure SaturatedMatching (E M : Finset (Finset V)) : Prop where
  subfamily : M ⊆ E
  pairwiseDisjoint : ∀ ⦃a⦄, a ∈ M → ∀ ⦃b⦄, b ∈ M → a ≠ b → Disjoint a b
  saturated : HitsAll E (matchingSupport M)

/-- Any width-two selected family owns at most two variables per selected clause. -/
theorem matchingSupport_card_le_two_mul
    {E M : Finset (Finset V)}
    (hwidth : ∀ e ∈ E, e.card ≤ 2) (hM : M ⊆ E) :
    (matchingSupport M).card ≤ 2 * M.card := by
  calc
    (matchingSupport M).card ≤ ∑ e ∈ M, e.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ M, 2 := Finset.sum_le_sum fun e he => hwidth e (hM he)
    _ = 2 * M.card := by simp [Nat.mul_comm]

/-- **Matching-or-cover dichotomy (proved).** -/
theorem saturatedMatching_dichotomy
    {E M : Finset (Finset V)}
    (hwidth : ∀ e ∈ E, e.card ≤ 2)
    (hmatch : SaturatedMatching E M) (t : ℕ) :
    t ≤ M.card ∨ (HitsAll E (matchingSupport M) ∧ (matchingSupport M).card < 2 * t) := by
  by_cases hlarge : t ≤ M.card
  · exact Or.inl hlarge
  · right
    refine ⟨hmatch.saturated, ?_⟩
    have hcard := matchingSupport_card_le_two_mul hwidth hmatch.subfamily
    omega

end PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCover

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCover.matchingSupport_card_le_two_mul
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFMatchingCover.saturatedMatching_dichotomy
