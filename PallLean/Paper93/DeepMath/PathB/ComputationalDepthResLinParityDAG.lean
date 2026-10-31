import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinParityKernel

/-!
# Size-aware dag proofs for resolution over parities

The semantic kernel deliberately did not identify tree terms with dag proofs.  This file adds the
actual indexed object: every non-initial line names earlier parent indices, every line has an exact
dependency level, and proof size is the number of stored lines.  The final theorem proves global
soundness by strong induction over line indices, so sharing is genuine rather than implicit prose.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical

/-- A compact justification tag.  Parent indices are natural numbers and are checked against the
current line by `ValidAt`. -/
inductive Justification (n : ℕ)
  | premise
  | boolean (i : Fin n)
  | weaken (parent : ℕ) (e : Equation n)
  | simplify (parent : ℕ) (b : ZMod 2)
  | linearResolve (left right : ℕ) (e f : Equation n)
  deriving DecidableEq

/-- One stored line in a dag proof. -/
structure DAGStep (n : ℕ) where
  line : Clause n
  why : Justification n
  deriving DecidableEq

/-- Safe lookup of a stored proof line. -/
def lineAt {n : ℕ} (steps : List (DAGStep n)) (i : ℕ) : Option (Clause n) :=
  (steps[i]?).map DAGStep.line

/-- Local proof checker.  Besides checking the rule, it enforces backward parent pointers and an
exact dependency level: sources have level zero, unary rules add one, and binary resolution takes
one plus the maximum parent level. -/
def ValidAt {n : ℕ} (Γ : Finset (Clause n)) (steps : List (DAGStep n))
    (level : ℕ → ℕ) (i : ℕ) : Prop :=
  match steps[i]? with
  | none => False
  | some s =>
      match s.why with
      | .premise => s.line ∈ Γ ∧ level i = 0
      | .boolean v => s.line = booleanAxiom n v ∧ level i = 0
      | .weaken p e =>
          p < i ∧ ∃ C, lineAt steps p = some C ∧ s.line = insert e C ∧
            level i = level p + 1
      | .simplify p b =>
          p < i ∧ b ≠ 0 ∧ ∃ C, lineAt steps p = some (insert (falseConstant n b) C) ∧
            s.line = C ∧ level i = level p + 1
      | .linearResolve p q e f =>
          p < i ∧ q < i ∧ ∃ C D,
            lineAt steps p = some (insert e C) ∧
            lineAt steps q = some (insert f D) ∧
            s.line = insert (e.add f) (C ∪ D) ∧
            level i = max (level p) (level q) + 1

/-- A checked dag refutation.  The last stored line is the empty clause. -/
structure DAGRefutation (n : ℕ) (Γ : Finset (Clause n)) where
  steps : List (DAGStep n)
  level : ℕ → ℕ
  nonempty : steps ≠ []
  valid : ∀ i, i < steps.length → ValidAt Γ steps level i
  final_empty : (steps.getLast nonempty).line = ∅

namespace DAGRefutation

/-- Dag size is the number of stored lines; a shared parent is counted once. -/
def size {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) : ℕ :=
  P.steps.length

/-- Dependency depth is one plus the exact level of the final line. -/
def depth {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) : ℕ :=
  P.level (P.steps.length - 1) + 1

theorem size_pos {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) :
    0 < P.size := by
  exact List.length_pos_of_ne_nil P.nonempty

/-- Soundness of one checked line assuming soundness of all earlier referenced lines. -/
theorem validAt_sound {n : ℕ} {Γ : Finset (Clause n)}
    {steps : List (DAGStep n)} {level : ℕ → ℕ} {i : ℕ} {s : DAGStep n}
    (hs : steps[i]? = some s) (hv : ValidAt Γ steps level i)
    (x : Fin n → ZMod 2) (hΓ : Models x Γ)
    (hprev : ∀ j, j < i → ∀ C, lineAt steps j = some C → SatisfiesClause x C) :
    SatisfiesClause x s.line := by
  unfold ValidAt at hv
  rw [hs] at hv
  cases hwhy : s.why with
  | premise =>
      simp only [hwhy] at hv
      exact hΓ _ hv.1
  | boolean v =>
      simp only [hwhy] at hv
      rw [hv.1]
      exact booleanAxiom_valid x v
  | weaken p e =>
      simp only [hwhy] at hv
      rcases hv with ⟨hp, C, hC, hline, _⟩
      rcases hprev p hp C hC with ⟨f, hf, hsat⟩
      rw [hline]
      exact ⟨f, Finset.mem_insert_of_mem hf, hsat⟩
  | simplify p b =>
      simp only [hwhy] at hv
      rcases hv with ⟨hp, hb, C, hC, hline, _⟩
      rcases hprev p hp _ hC with ⟨e, he, hsat⟩
      rw [hline]
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact False.elim ((not_satisfies_falseConstant x hb) hsat)
      · exact ⟨e, he, hsat⟩
  | linearResolve p q e f =>
      simp only [hwhy] at hv
      rcases hv with ⟨hp, hq, C, D, hC, hD, hline, _⟩
      rcases hprev p hp _ hC with ⟨g, hg, hgsat⟩
      rcases hprev q hq _ hD with ⟨h, hh, hhsat⟩
      rw [hline]
      rw [Finset.mem_insert] at hg hh
      rcases hg with rfl | hg
      · rcases hh with rfl | hh
        · exact ⟨_, Finset.mem_insert_self _ _, Equation.satisfies_add x _ _ hgsat hhsat⟩
        · exact ⟨h, Finset.mem_insert_of_mem (Finset.mem_union_right _ hh), hhsat⟩
      · exact ⟨g, Finset.mem_insert_of_mem (Finset.mem_union_left _ hg), hgsat⟩

/-- Every stored line in a checked dag refutation is semantically valid. -/
theorem line_sound {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ)
    (x : Fin n → ZMod 2) (hΓ : Models x Γ) :
    ∀ i C, lineAt P.steps i = some C → SatisfiesClause x C := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro C hC
      unfold lineAt at hC
      cases hs : P.steps[i]? with
      | none => simp [hs] at hC
      | some s =>
          simp only [hs, Option.map_some, Option.some.injEq] at hC
          subst C
          have hi : i < P.steps.length := by
            rw [List.getElem?_eq_some_iff] at hs
            exact hs.1
          exact validAt_sound (steps := P.steps) (level := P.level) hs (P.valid i hi) x hΓ
            (fun j hj D hD => ih j hj D hD)

/-- **Global dag soundness.**  No checked `Res(⊕)` dag refutes satisfiable premises. -/
theorem unsat {n : ℕ} {Γ : Finset (Clause n)} (P : DAGRefutation n Γ) :
    ¬ ∃ x : Fin n → ZMod 2, Models x Γ := by
  rintro ⟨x, hx⟩
  let i := P.steps.length - 1
  have hi : i < P.steps.length := by
    have hpos : 0 < P.steps.length := by simpa [size] using P.size_pos
    simp only [i]
    omega
  have hlast : P.steps[i]? = some (P.steps.getLast P.nonempty) := by
    rw [List.getElem?_eq_getElem hi]
    congr 1
    simpa [i] using List.get_length_sub_one hi
  have hline : lineAt P.steps i = some (∅ : Clause n) := by
    unfold lineAt
    simp only [hlast, Option.map_some, P.final_empty]
  rcases P.line_sound x hx i ∅ hline with ⟨e, he, _⟩
  simp at he

#print axioms validAt_sound
#print axioms line_sound
#print axioms unsat

end DAGRefutation

end PallLean.Paper93.DeepMath.PathB.ResLinParity
