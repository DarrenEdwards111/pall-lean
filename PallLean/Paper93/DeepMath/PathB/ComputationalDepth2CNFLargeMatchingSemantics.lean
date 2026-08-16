import PallLean.Paper93.DeepMath.PathB.ComputationalDepth2CNFCoverRestriction

/-!
# Large-matching branch semantics for signed 2-CNF clauses

Matched clauses own disjoint pairs of variables.  The two literals may have arbitrary signs.  Each clause still has
exactly three satisfying local states.  This file constructs the branch space, maps every branch to a total assignment,
and proves conversely that every assignment satisfying all matched clauses is recovered by one branch.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoCNFLargeMatchingSemantics

open scoped Classical

/-- Satisfying local states for a signed binary clause requiring `left` or `right`. -/
abbrev SignedPairState (left right : Bool) :=
  {p : Bool × Bool // p.1 = left ∨ p.2 = right}

/-- Every nondegenerate signed binary clause has exactly three satisfying local states. -/
theorem card_signedPairState (left right : Bool) :
    Fintype.card (SignedPairState left right) = 3 := by
  cases left <;> cases right <;> decide

/-- Variables owned by `m` matched clauses, plus `r` unrestricted remainder variables. -/
abbrev MatchVar (m r : ℕ) := Sum (Fin m × Fin 2) (Fin r)

/-- A branch chooses one satisfying state for each matched clause and all remaining Boolean variables. -/
abbrev MatchingBranch {m : ℕ} (signs : Fin m → Bool × Bool) (r : ℕ) :=
  (∀ i, SignedPairState (signs i).1 (signs i).2) × (Fin r → Bool)

/-- Decode a matching branch into a total assignment. -/
def assignmentOfBranch {m r : ℕ} {signs : Fin m → Bool × Bool}
    (branch : MatchingBranch signs r) : MatchVar m r → Bool
  | Sum.inl (i, side) => if side = 0 then (branch.1 i).1.1 else (branch.1 i).1.2
  | Sum.inr j => branch.2 j

/-- Evaluation of the signed clause owned by matching position `i`. -/
def evalMatchedClause {m r : ℕ} (signs : Fin m → Bool × Bool)
    (x : MatchVar m r → Bool) (i : Fin m) : Prop :=
  x (Sum.inl (i, 0)) = (signs i).1 ∨ x (Sum.inl (i, 1)) = (signs i).2

/-- Every decoded branch satisfies all selected matching clauses. -/
theorem assignmentOfBranch_satisfies {m r : ℕ} {signs : Fin m → Bool × Bool}
    (branch : MatchingBranch signs r) (i : Fin m) :
    evalMatchedClause signs (assignmentOfBranch branch) i := by
  simpa [evalMatchedClause, assignmentOfBranch] using (branch.1 i).2

/-- Encode any total assignment satisfying the matching into the branch space. -/
def branchOfAssignment {m r : ℕ} (signs : Fin m → Bool × Bool)
    (x : MatchVar m r → Bool) (hx : ∀ i, evalMatchedClause signs x i) : MatchingBranch signs r :=
  ⟨fun i => ⟨(x (Sum.inl (i, 0)), x (Sum.inl (i, 1))), hx i⟩, fun j => x (Sum.inr j)⟩

/-- Decoding the encoded satisfying assignment is the identity. -/
theorem assignmentOfBranch_branchOfAssignment {m r : ℕ} (signs : Fin m → Bool × Bool)
    (x : MatchVar m r → Bool) (hx : ∀ i, evalMatchedClause signs x i) :
    assignmentOfBranch (branchOfAssignment signs x hx) = x := by
  funext v
  rcases v with ⟨⟨i, side⟩⟩ | j
  · fin_cases side <;> simp [assignmentOfBranch, branchOfAssignment]
  · rfl

/-- The exact branch count is `3^m * 2^r`. -/
theorem card_matchingBranch {m : ℕ} (signs : Fin m → Bool × Bool) (r : ℕ) :
    Fintype.card (MatchingBranch signs r) = 3 ^ m * 2 ^ r := by
  simp [MatchingBranch, card_signedPairState]

/-- Grouping `m = 3k` clauses recovers the `27^k * 2^r` large-matching work term. -/
theorem card_matchingBranch_three_blocks {k : ℕ} (signs : Fin (3 * k) → Bool × Bool) (r : ℕ) :
    Fintype.card (MatchingBranch signs r) = 27 ^ k * 2 ^ r := by
  rw [card_matchingBranch, pow_mul]
  norm_num

end PallLean.Paper93.DeepMath.PathB.TwoCNFLargeMatchingSemantics

#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFLargeMatchingSemantics.card_signedPairState
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFLargeMatchingSemantics.assignmentOfBranch_branchOfAssignment
#print axioms PallLean.Paper93.DeepMath.PathB.TwoCNFLargeMatchingSemantics.card_matchingBranch_three_blocks
