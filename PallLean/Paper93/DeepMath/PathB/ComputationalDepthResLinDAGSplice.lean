import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinRestrictedBooleanCleanup

/-!
# Reindexing and splicing checked `Res(⊕)` dags

Inserting a cleanup macro before an existing dag shifts every later line and every parent pointer by
the prefix length.  This file proves that bookkeeping once and for all.  Lines and inference data
are unchanged apart from parent indices; exact dependency levels are joined piecewise.

The main result, `DAGDerivation.append`, concatenates two checked dags over the same premises and
proves exact additive size.  The lower-level `validAt_shift_append` is the primitive needed by the
restricted-Boolean-source substitution compiler, where later lines may refer back into an inserted
cleanup prefix.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical

/-- Add a fixed offset to every parent pointer in an inference tag. -/
def shiftJustification {n : ℕ} (offset : ℕ) : Justification n → Justification n
  | .premise => .premise
  | .boolean i => .boolean i
  | .weaken p e => .weaken (offset + p) e
  | .simplify p b => .simplify (offset + p) b
  | .linearResolve p q e f => .linearResolve (offset + p) (offset + q) e f

/-- Shift one stored step without changing its line. -/
def shiftStep {n : ℕ} (offset : ℕ) (s : DAGStep n) : DAGStep n where
  line := s.line
  why := shiftJustification offset s.why

/-- Piecewise level function for a prefix followed by a shifted suffix. -/
def appendLevel (cut : ℕ) (prefixLevel suffixLevel : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < cut then prefixLevel i else suffixLevel (i - cut)

theorem appendLevel_left {cut i : ℕ} {prefixLevel suffixLevel : ℕ → ℕ} (hi : i < cut) :
    appendLevel cut prefixLevel suffixLevel i = prefixLevel i := by
  simp [appendLevel, hi]

theorem appendLevel_right (cut i : ℕ) {prefixLevel suffixLevel : ℕ → ℕ} :
    appendLevel cut prefixLevel suffixLevel (cut + i) = suffixLevel i := by
  simp [appendLevel]

/-- Lookup in a shifted suffix returns the original line. -/
theorem lineAt_append_shift {n : ℕ} (pre steps : List (DAGStep n))
    (i : ℕ) :
    lineAt (pre ++ steps.map (shiftStep pre.length)) (pre.length + i) =
      lineAt steps i := by
  unfold lineAt
  rw [List.getElem?_append_right]
  · simp only [Nat.add_sub_cancel_left, List.getElem?_map]
    cases steps[i]? <;> rfl
  · omega

/-- Lookup in the untouched prefix is unchanged. -/
theorem lineAt_append_left {n : ℕ} (pre suffix : List (DAGStep n))
    {i : ℕ} (hi : i < pre.length) :
    lineAt (pre ++ suffix) i = lineAt pre i := by
  unfold lineAt
  rw [List.getElem?_append_left hi]

/-- A locally valid suffix step remains valid after an arbitrary prefix is inserted and all of its
parent pointers are shifted. -/
theorem validAt_shift_append {n : ℕ} {Γ : Finset (Clause n)}
    (pre : List (DAGStep n)) (prefixLevel : ℕ → ℕ)
    {steps : List (DAGStep n)} {level : ℕ → ℕ} {i : ℕ}
    (hv : ValidAt Γ steps level i) :
    ValidAt Γ (pre ++ steps.map (shiftStep pre.length))
      (appendLevel pre.length prefixLevel level) (pre.length + i) := by
  unfold ValidAt at hv ⊢
  cases hs : steps[i]? with
  | none => simp [hs] at hv
  | some s =>
      simp only [hs] at hv
      have hcur :
          (pre ++ steps.map (shiftStep pre.length))[pre.length + i]? =
            some (shiftStep pre.length s) := by
        rw [List.getElem?_append_right]
        · simp [hs]
        · omega
      rw [hcur]
      simp only
      cases hwhy : s.why with
      | premise =>
          simp only [hwhy] at hv
          rw [show (shiftStep pre.length s).why = Justification.premise by
            simp [shiftStep, shiftJustification, hwhy]]
          exact ⟨hv.1, by simpa [appendLevel_right] using hv.2⟩
      | boolean v =>
          simp only [hwhy] at hv
          rw [show (shiftStep pre.length s).why = Justification.boolean v by
            simp [shiftStep, shiftJustification, hwhy]]
          exact ⟨by simpa [shiftStep] using hv.1,
            by simpa [appendLevel_right] using hv.2⟩
      | weaken p e =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, C, hC, hline, hlevel⟩
          rw [show (shiftStep pre.length s).why =
              Justification.weaken (pre.length + p) e by
            simp [shiftStep, shiftJustification, hwhy]]
          refine ⟨by omega, C, lineAt_append_shift pre steps p ▸ hC, ?_, ?_⟩
          · simpa [shiftStep] using hline
          · simpa [appendLevel_right] using hlevel
      | simplify p b =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, hb, C, hC, hline, hlevel⟩
          rw [show (shiftStep pre.length s).why =
              Justification.simplify (pre.length + p) b by
            simp [shiftStep, shiftJustification, hwhy]]
          refine ⟨by omega, hb, C, lineAt_append_shift pre steps p ▸ hC, ?_, ?_⟩
          · simpa [shiftStep] using hline
          · simpa [appendLevel_right] using hlevel
      | linearResolve p q e f =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, hq, C, D, hC, hD, hline, hlevel⟩
          rw [show (shiftStep pre.length s).why =
              Justification.linearResolve (pre.length + p) (pre.length + q) e f by
            simp [shiftStep, shiftJustification, hwhy]]
          refine ⟨by omega, by omega, C, D,
            lineAt_append_shift pre steps p ▸ hC,
            lineAt_append_shift pre steps q ▸ hD, ?_, ?_⟩
          · simpa [shiftStep] using hline
          · simpa [appendLevel_right] using hlevel

/-- Prefix validity is unaffected by appending any suffix. -/
theorem validAt_append_left {n : ℕ} {Γ : Finset (Clause n)}
    {pre suffix : List (DAGStep n)} {level suffixLevel : ℕ → ℕ} {i : ℕ}
    (hi : i < pre.length) (hv : ValidAt Γ pre level i) :
    ValidAt Γ (pre ++ suffix) (appendLevel pre.length level suffixLevel) i := by
  unfold ValidAt at hv ⊢
  rw [List.getElem?_append_left hi]
  cases hs : pre[i]? with
  | none => simp [hs] at hv
  | some s =>
      simp only [hs] at hv ⊢
      cases hwhy : s.why with
      | premise =>
          simp only [hwhy] at hv ⊢
          exact ⟨hv.1, by simpa [appendLevel_left hi] using hv.2⟩
      | boolean v =>
          simp only [hwhy] at hv ⊢
          exact ⟨hv.1, by simpa [appendLevel_left hi] using hv.2⟩
      | weaken p e =>
          simp only [hwhy] at hv ⊢
          rcases hv with ⟨hp, C, hC, hline, hlevel⟩
          refine ⟨hp, C, ?_, hline, ?_⟩
          · simpa [lineAt_append_left pre suffix (lt_trans hp hi)] using hC
          · rw [appendLevel_left hi, appendLevel_left (lt_trans hp hi)]
            exact hlevel
      | simplify p b =>
          simp only [hwhy] at hv ⊢
          rcases hv with ⟨hp, hb, C, hC, hline, hlevel⟩
          refine ⟨hp, hb, C, ?_, hline, ?_⟩
          · simpa [lineAt_append_left pre suffix (lt_trans hp hi)] using hC
          · rw [appendLevel_left hi, appendLevel_left (lt_trans hp hi)]
            exact hlevel
      | linearResolve p q e f =>
          simp only [hwhy] at hv ⊢
          rcases hv with ⟨hp, hq, C, D, hC, hD, hline, hlevel⟩
          refine ⟨hp, hq, C, D, ?_, ?_, hline, ?_⟩
          · simpa [lineAt_append_left pre suffix (lt_trans hp hi)] using hC
          · simpa [lineAt_append_left pre suffix (lt_trans hq hi)] using hD
          · rw [appendLevel_left hi, appendLevel_left (lt_trans hp hi),
              appendLevel_left (lt_trans hq hi)]
            exact hlevel

/-- Concatenate two checked dag derivations over the same premises.  The second dag is reindexed
past the first; its final line remains the combined final line. -/
def DAGDerivation.append {n : ℕ} {Γ : Finset (Clause n)} {A B : Clause n}
    (P : DAGDerivation n Γ A) (Q : DAGDerivation n Γ B) : DAGDerivation n Γ B where
  steps := P.steps ++ Q.steps.map (shiftStep P.steps.length)
  level := appendLevel P.steps.length P.level Q.level
  nonempty := by simp [P.nonempty]
  valid := by
    intro i hi
    by_cases hleft : i < P.steps.length
    · apply validAt_append_left hleft
      exact P.valid i hleft
    · obtain ⟨j, rfl⟩ : ∃ j, i = P.steps.length + j := by
        refine ⟨i - P.steps.length, by omega⟩
      apply validAt_shift_append P.steps P.level
      apply Q.valid
      simp at hi
      omega
  final_line := by
    simp [Q.nonempty, shiftStep, Q.final_line]

theorem DAGDerivation.append_size {n : ℕ} {Γ : Finset (Clause n)} {A B : Clause n}
    (P : DAGDerivation n Γ A) (Q : DAGDerivation n Γ B) :
    (P.append Q).size = P.size + Q.size := by
  simp [DAGDerivation.append, DAGDerivation.size]

theorem DAGDerivation.append_depth {n : ℕ} {Γ : Finset (Clause n)} {A B : Clause n}
    (P : DAGDerivation n Γ A) (Q : DAGDerivation n Γ B) :
    (P.append Q).depth = Q.depth := by
  have hq : 0 < Q.steps.length := List.length_pos_of_ne_nil Q.nonempty
  unfold DAGDerivation.depth
  change appendLevel P.steps.length P.level Q.level
      ((P.steps ++ Q.steps.map (shiftStep P.steps.length)).length - 1) + 1 =
    Q.level (Q.steps.length - 1) + 1
  simp only [List.length_append, List.length_map]
  have hidx : P.steps.length + Q.steps.length - 1 =
      P.steps.length + (Q.steps.length - 1) := by omega
  rw [hidx, appendLevel_right]

/-- Regard a checked refutation as a checked derivation of the empty line. -/
def DAGRefutation.toDAGDerivation {n : ℕ} {Γ : Finset (Clause n)}
    (P : DAGRefutation n Γ) : DAGDerivation n Γ ∅ where
  steps := P.steps
  level := P.level
  nonempty := P.nonempty
  valid := P.valid
  final_line := P.final_empty

/-- A checked dag derivation of the empty line is a checked refutation. -/
def DAGDerivation.toRefutation {n : ℕ} {Γ : Finset (Clause n)}
    (P : DAGDerivation n Γ ∅) : DAGRefutation n Γ where
  steps := P.steps
  level := P.level
  nonempty := P.nonempty
  valid := P.valid
  final_empty := P.final_line

/-- Insert any checked derivation as a prefix of a refutation and reindex the entire refutation
past it.  This is the checked list-splicing operation used for cleanup macros. -/
def DAGRefutation.prepend {n : ℕ} {Γ : Finset (Clause n)} {C : Clause n}
    (Q : DAGRefutation n Γ) (P : DAGDerivation n Γ C) : DAGRefutation n Γ :=
  (P.append Q.toDAGDerivation).toRefutation

theorem DAGRefutation.prepend_size {n : ℕ} {Γ : Finset (Clause n)} {C : Clause n}
    (Q : DAGRefutation n Γ) (P : DAGDerivation n Γ C) :
    (Q.prepend P).size = P.size + Q.size := by
  simpa [DAGRefutation.prepend, DAGRefutation.toDAGDerivation,
    DAGDerivation.toRefutation, DAGRefutation.size, DAGDerivation.size] using
    DAGDerivation.append_size P Q.toDAGDerivation

theorem DAGRefutation.prepend_depth {n : ℕ} {Γ : Finset (Clause n)} {C : Clause n}
    (Q : DAGRefutation n Γ) (P : DAGDerivation n Γ C) :
    (Q.prepend P).depth = Q.depth := by
  simpa [DAGRefutation.prepend, DAGRefutation.toDAGDerivation,
    DAGDerivation.toRefutation, DAGRefutation.depth, DAGDerivation.depth] using
    DAGDerivation.append_depth P Q.toDAGDerivation

/-- Concrete specialization: a six-line Boolean cleanup macro can be inserted before any checked
refutation, with exact additive size and no increase in final dependency depth. -/
theorem DAGRefutation.prepend_fixedBooleanCleanup_cost
    {n : ℕ} {Γ : Finset (Clause n)} (Q : DAGRefutation n Γ) (i : Fin n) :
    (Q.prepend (fixedBooleanCleanupDAG Γ i)).size = 6 + Q.size ∧
      (Q.prepend (fixedBooleanCleanupDAG Γ i)).depth = Q.depth := by
  exact ⟨by rw [Q.prepend_size, fixedBooleanCleanupDAG_size],
    Q.prepend_depth (fixedBooleanCleanupDAG Γ i)⟩

#print axioms validAt_shift_append
#print axioms DAGDerivation.append_size
#print axioms DAGDerivation.append_depth
#print axioms DAGRefutation.prepend_fixedBooleanCleanup_cost

end PallLean.Paper93.DeepMath.PathB.ResLinParity
