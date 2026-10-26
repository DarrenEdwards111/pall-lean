import Mathlib

/-!
# Decision-invariant repair audit

A new audit of two proposed repairs to the trace-rank argument:
1. Ask a finite invariant of the projected decision predicate to dominate all
   verifier trace ranks. This is impossible: diagonal padding has arbitrary rank.
2. Minimize rank over all semantically equivalent verifier presentations.
   Without an efficiency constraint this collapses to rank at most one, because
   an arbitrary decision predicate can be placed in the verifier itself.

These are obstructions, NOT a P versus NP separation. In particular the
rank-one presentation below is NOT asserted to be polynomial-time decidable.
-/

namespace DecisionInvariantTraceRankAudit

/-- A verifier with witness and trace erased by existential projection. -/
structure Presentation (Input Witness Trace : Type) where
  accepts : Input → Witness → Trace → Prop

def projected {I W T : Type} (V : Presentation I W T) (x : I) : Prop :=
  ∃ w t, V.accepts x w t

/-- The rational acceptance matrix at one fixed input. -/
noncomputable def acceptanceMatrix {I W T : Type}
    (V : Presentation I W T) (x : I) : Matrix W T ℚ := by
  classical
  exact fun w t => if V.accepts x w t then 1 else 0

/-- Add matching existential indices without changing the decision predicate. -/
def diagonalPresentation {I : Type} (P : I → Prop) (k : Nat) :
    Presentation I (Fin (k + 1)) (Fin (k + 1)) where
  accepts x w t := P x ∧ w = t

theorem diagonal_projected_iff {I : Type} (P : I → Prop) (k : Nat) (x : I) :
    projected (diagonalPresentation P k) x ↔ P x := by
  constructor
  · rintro ⟨w, t, h, _⟩
    exact h
  · intro h
    exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, h, rfl⟩

theorem diagonal_projected_eq {I : Type} (P : I → Prop) (k : Nat) :
    projected (diagonalPresentation P k) = P := by
  funext x
  exact propext (diagonal_projected_iff P k x)

theorem diagonal_matrix_eq_one {I : Type} (P : I → Prop) (k : Nat)
    (x : I) (hx : P x) :
    acceptanceMatrix (diagonalPresentation P k) x = 1 := by
  classical
  ext w t
  simp [acceptanceMatrix, diagonalPresentation, hx, Matrix.one_apply]

theorem diagonal_rank {I : Type} (P : I → Prop) (k : Nat)
    (x : I) (hx : P x) :
    (acceptanceMatrix (diagonalPresentation P k) x).rank = k + 1 := by
  rw [diagonal_matrix_eq_one P k x hx, Matrix.rank_one]
  simp

/-- Even a fixed nonempty predicate has presentations exceeding every proposed
finite, decision-only bound. The input and predicate do not vary with k. -/
theorem no_decision_only_rank_upper_bound {I : Type}
    (P : I → Prop) (x : I) (hx : P x) (bound : (I → Prop) → Nat) :
    ¬ ∀ k : Nat,
      (acceptanceMatrix (diagonalPresentation P k) x).rank ≤
        bound (projected (diagonalPresentation P k)) := by
  intro h
  have hk := h (bound P)
  rw [diagonal_projected_eq, diagonal_rank P (bound P) x hx] at hk
  omega

/-- Degenerate semantic normalization: all decision work is hidden in accepts.
No runtime bound or algorithm for P is supplied by this definition. -/
def directPresentation {I : Type} (P : I → Prop) : Presentation I Unit Unit where
  accepts x _ _ := P x

theorem direct_projected_eq {I : Type} (P : I → Prop) :
    projected (directPresentation P) = P := by
  funext x
  apply propext
  constructor
  · rintro ⟨w, t, h⟩
    exact h
  · intro h
    exact ⟨(), (), h⟩

theorem direct_rank_le_one {I : Type} (P : I → Prop) (x : I) :
    (acceptanceMatrix (directPresentation P) x).rank ≤ 1 := by
  have h := Matrix.rank_le_card_width (acceptanceMatrix (directPresentation P) x)
  simpa using h

/-- Semantic equivalence alone always admits a one-by-one presentation. -/
theorem semantic_normalization_rank_le_one {I : Type} (P : I → Prop) :
    ∃ V : Presentation I Unit Unit,
      projected V = P ∧ ∀ x, (acceptanceMatrix V x).rank ≤ 1 :=
  ⟨directPresentation P, direct_projected_eq P, direct_rank_le_one P⟩

/-- On an accepted input the two equivalent presentations have arbitrarily
separated ranks. This is not a lower bound for algorithms deciding P. -/
theorem equivalent_presentations_rank_gap {I : Type} (P : I → Prop)
    (x : I) (hx : P x) (k : Nat) (hk : 1 ≤ k) :
    projected (directPresentation P) = projected (diagonalPresentation P k) ∧
    (acceptanceMatrix (directPresentation P) x).rank <
      (acceptanceMatrix (diagonalPresentation P k) x).rank := by
  constructor
  · rw [direct_projected_eq, diagonal_projected_eq]
  · rw [diagonal_rank P k x hx]
    have h := direct_rank_le_one P x
    omega

end DecisionInvariantTraceRankAudit

#print axioms DecisionInvariantTraceRankAudit.diagonal_rank
#print axioms DecisionInvariantTraceRankAudit.no_decision_only_rank_upper_bound
#print axioms DecisionInvariantTraceRankAudit.semantic_normalization_rank_le_one
#print axioms DecisionInvariantTraceRankAudit.equivalent_presentations_rank_gap
