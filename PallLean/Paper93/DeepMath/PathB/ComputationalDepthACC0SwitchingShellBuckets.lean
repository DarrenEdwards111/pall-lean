import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BlockSwitchingDyadicIntegration

/-!
# Concrete fixed-star shell buckets

The block-switching SAT integration previously accepted an abstract list of bucket counts together
with the hypothesis that their sum is the total bad-set cardinality.  Here the buckets are built:
one bucket for each `K`-element set of free coordinates, containing exactly the bad restrictions with
that free set.  They are pairwise disjoint, their union is `Bad`, and hence their cardinalities sum
to `Bad.card`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting
open PallLean.Paper93.DeepMath.PathB.ACC0BlockSwitchingDyadicIntegration
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- The set of coordinates left free by a restriction. -/
def freeSet {n : ℕ} (ρ : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ρ i = none)

theorem freeSet_card {n : ℕ} (ρ : Restriction n) : (freeSet ρ).card = stars ρ := rfl

/-- Indices for the concrete buckets in the fixed-`K` shell. -/
abbrev FreeSetBucket (n K : ℕ) := {S : Finset (Fin n) // S.card = K}

theorem card_freeSetBucket (n K : ℕ) :
    Fintype.card (FreeSetBucket n K) = n.choose K := by
  simpa [FreeSetBucket] using (Fintype.card_finset_len (α := Fin n) K)

/-- Bad restrictions whose free-coordinate set is exactly `S`. -/
def badBucket {n K : ℕ} (Bad : Finset (Restriction n)) (S : FreeSetBucket n K) :
    Finset (Restriction n) :=
  Bad.filter (fun ρ => freeSet ρ = S.1)

theorem badBucket_pairwiseDisjoint {n K : ℕ} (Bad : Finset (Restriction n)) :
    (↑(Finset.univ : Finset (FreeSetBucket n K)) : Set (FreeSetBucket n K)).PairwiseDisjoint
      (badBucket Bad) := by
  classical
  intro S _ T _ hST
  rw [Function.onFun, Finset.disjoint_left]
  intro ρ hS hT
  rw [badBucket, Finset.mem_filter] at hS hT
  exact hST (Subtype.ext (hS.2.symm.trans hT.2))

theorem biUnion_badBucket_eq {n K : ℕ} {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, stars ρ = K) :
    (Finset.univ : Finset (FreeSetBucket n K)).biUnion (badBucket Bad) = Bad := by
  classical
  ext ρ
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, badBucket, Finset.mem_filter]
  constructor
  · rintro ⟨S, hρ, -⟩
    exact hρ
  · intro hρ
    let S : FreeSetBucket n K := ⟨freeSet ρ, by rw [freeSet_card, hstars ρ hρ]⟩
    exact ⟨S, hρ, rfl⟩

/-- The formerly supplied partition identity, now derived from the concrete shell buckets. -/
theorem sum_badBucket_card {n K : ℕ} {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, stars ρ = K) :
    (∑ S : FreeSetBucket n K, (badBucket Bad S).card) = Bad.card := by
  classical
  rw [← Finset.card_biUnion (badBucket_pairwiseDisjoint Bad), biUnion_badBucket_eq hstars]

/-- Canonically enumerate the concrete free-set buckets by `Fin (n.choose K)`. -/
noncomputable def freeSetBucketEquivFin (n K : ℕ) :
    FreeSetBucket n K ≃ Fin (n.choose K) :=
  Fintype.equivFinOfCardEq (card_freeSetBucket n K)

/-- The actual bucket-count array expected by the arithmetic averaging theorem. -/
noncomputable def concreteBadCount {n K : ℕ} (Bad : Finset (Restriction n)) :
    Fin (n.choose K) → ℕ :=
  fun i => (badBucket Bad ((freeSetBucketEquivFin n K).symm i)).card

theorem sum_concreteBadCount {n K : ℕ} {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, stars ρ = K) :
    (∑ i : Fin (n.choose K), concreteBadCount (K := K) Bad i) = Bad.card := by
  classical
  rw [Fintype.sum_equiv (freeSetBucketEquivFin n K).symm
    (fun i => concreteBadCount Bad i) (fun S => (badBucket Bad S).card) (by intro i; rfl)]
  exact sum_badBucket_card hstars

/-- **End-to-end integration with the shell partition constructed internally.** -/
theorem block_switching_to_concreteBucket_activeGap
    {n : ℕ} (cs : List (Clause n)) (w F K depth saving : ℕ)
    (hcons : ∀ T ∈ cs, Consistent T) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    {Bad : Finset (Restriction n)}
    (hstars : ∀ ρ ∈ Bad, stars ρ = K)
    (hbadDepth : ∀ ρ ∈ Bad, (blockStream cs F ρ).length = depth)
    (hdepthK : depth ≤ K) (hKn : K ≤ n) (hr : 2 * K < n - K + 1)
    (hrhs :
      ((2 : ℚ) ^ w * (((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))) ^ depth
          / (1 - ((2 * K : ℕ) : ℚ) / ((n - K + 1 : ℕ) : ℚ))
        ≤ 1 / (2 ^ (saving + 1) : ℚ))
    (hsq : saving + 1 ≤ n - K) (hsN : saving + 1 ≤ n)
    (hbudget : (n - K) + (depth - 1) ≤ n - saving - 1) :
    ∃ i : Fin (n.choose K), goodBadWork n (n - K) (2 ^ (n - K))
      (concreteBadCount (K := K) Bad i) (depth - 1)
      ≤ 2 ^ (n - saving) := by
  apply block_switching_to_selectedBucket_activeGap cs w F K depth saving hcons hw
    hstars hbadDepth hdepthK hKn hr hrhs (concreteBadCount (K := K) Bad)
  · exact sum_concreteBadCount hstars
  · exact hsq
  · exact hsN
  · exact hbudget

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets.sum_badBucket_card
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets.block_switching_to_concreteBucket_activeGap
