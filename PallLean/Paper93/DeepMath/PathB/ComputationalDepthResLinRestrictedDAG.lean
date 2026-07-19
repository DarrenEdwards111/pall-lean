import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinRestrictedInstance

/-!
# Restricting an entire checked `Res(⊕)` dag

This file lifts restriction from local inference rules to the size-aware dag checker.  A restricted
Boolean axiom is a tautology but is not necessarily syntactically the canonical Boolean axiom.
We therefore place all restricted Boolean axioms among the residual sources and turn `.boolean`
steps into `.premise` steps.  Every other justification is transported exactly.

The resulting checked dag has exactly the same number of lines and exactly the same dependency
depth.  The only remaining cleanup problem is proof-complexity, not soundness: remove the added
tautological sources while controlling size and depth.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical

/-- Residual premises together with the restricted forms of the free Boolean axioms. -/
def restrictedSources {n : ℕ} (ρ : Restriction n) (Γ : Finset (Clause n)) :
    Finset (Clause n) :=
  restrictPremises ρ Γ ∪ Finset.univ.image (fun i => restrictClause ρ (booleanAxiom n i))

/-- Transport an inference tag through a restriction.  Boolean sources become ordinary residual
premises because their restricted syntax need not be a canonical Boolean axiom. -/
def restrictJustification {n : ℕ} (ρ : Restriction n) : Justification n → Justification n
  | .premise => .premise
  | .boolean _ => .premise
  | .weaken p e => .weaken p (restrictEq ρ e)
  | .simplify p b => .simplify p b
  | .linearResolve p q e f => .linearResolve p q (restrictEq ρ e) (restrictEq ρ f)

/-- Restrict one stored proof line and its justification. -/
def restrictStep {n : ℕ} (ρ : Restriction n) (s : DAGStep n) : DAGStep n where
  line := restrictClause ρ s.line
  why := restrictJustification ρ s.why

/-- Line lookup commutes with mapping restriction over the stored dag. -/
theorem lineAt_map_restrictStep {n : ℕ} (ρ : Restriction n)
    (steps : List (DAGStep n)) (i : ℕ) :
    lineAt (steps.map (restrictStep ρ)) i = (lineAt steps i).map (restrictClause ρ) := by
  unfold lineAt
  simp only [List.getElem?_map]
  cases steps[i]? <;> rfl

/-- Every locally checked inference remains locally checked after restriction, with restricted
Boolean axioms treated as residual premises. -/
theorem validAt_restrict {n : ℕ} {Γ : Finset (Clause n)} (ρ : Restriction n)
    {steps : List (DAGStep n)} {level : ℕ → ℕ} {i : ℕ}
    (hv : ValidAt Γ steps level i) :
    ValidAt (restrictedSources ρ Γ) (steps.map (restrictStep ρ)) level i := by
  unfold ValidAt at hv ⊢
  cases hs : steps[i]? with
  | none => simp [hs] at hv
  | some s =>
      simp only [hs] at hv
      have hrs : (steps.map (restrictStep ρ))[i]? = some (restrictStep ρ s) := by
        simp [hs]
      rw [hrs]
      simp only
      cases hwhy : s.why with
      | premise =>
          simp only [hwhy] at hv
          rw [show (restrictStep ρ s).why = Justification.premise by
            simp [restrictStep, restrictJustification, hwhy]]
          exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s.line, hv.1, rfl⟩), hv.2⟩
      | boolean v =>
          simp only [hwhy] at hv
          rw [show (restrictStep ρ s).why = Justification.premise by
            simp [restrictStep, restrictJustification, hwhy]]
          refine ⟨Finset.mem_union_right _ ?_, hv.2⟩
          exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, by simp [restrictStep, hv.1]⟩
      | weaken p e =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, C, hC, hline, hlevel⟩
          rw [show (restrictStep ρ s).why = Justification.weaken p (restrictEq ρ e) by
            simp [restrictStep, restrictJustification, hwhy]]
          refine ⟨hp, restrictClause ρ C, ?_, ?_, hlevel⟩
          · rw [lineAt_map_restrictStep, hC]
            rfl
          · simpa [restrictStep, hline] using restrictClause_insert ρ e C
      | simplify p b =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, hb, C, hC, hline, hlevel⟩
          rw [show (restrictStep ρ s).why = Justification.simplify p b by
            simp [restrictStep, restrictJustification, hwhy]]
          refine ⟨hp, hb, restrictClause ρ C, ?_, ?_, hlevel⟩
          · rw [lineAt_map_restrictStep, hC]
            simpa using restrict_simplification_source ρ C b
          · simp [restrictStep, hline]
      | linearResolve p q e f =>
          simp only [hwhy] at hv
          rcases hv with ⟨hp, hq, C, D, hC, hD, hline, hlevel⟩
          rw [show (restrictStep ρ s).why =
              Justification.linearResolve p q (restrictEq ρ e) (restrictEq ρ f) by
            simp [restrictStep, restrictJustification, hwhy]]
          refine ⟨hp, hq, restrictClause ρ C, restrictClause ρ D, ?_, ?_, ?_, hlevel⟩
          · rw [lineAt_map_restrictStep, hC]
            simpa using restrictClause_insert ρ e C
          · rw [lineAt_map_restrictStep, hD]
            simpa using restrictClause_insert ρ f D
          · simpa [restrictStep, hline] using restrict_linearResolvent ρ C D e f

/-- Restrict every line of a checked refutation.  The transformed dag refutes the residual sources
without adding or duplicating any stored line. -/
def DAGRefutation.restrict {n : ℕ} {Γ : Finset (Clause n)}
    (P : DAGRefutation n Γ) (ρ : Restriction n) :
    DAGRefutation n (restrictedSources ρ Γ) where
  steps := P.steps.map (restrictStep ρ)
  level := P.level
  nonempty := by simpa using P.nonempty
  valid := by
    intro i hi
    apply validAt_restrict ρ (P.valid i ?_)
    simpa using hi
  final_empty := by
    rw [List.getLast_map]
    simp [restrictStep, P.final_empty, restrictClause]

/-- Dag restriction preserves size exactly. -/
theorem DAGRefutation.restrict_size {n : ℕ} {Γ : Finset (Clause n)}
    (P : DAGRefutation n Γ) (ρ : Restriction n) :
    (P.restrict ρ).size = P.size := by
  simp [DAGRefutation.restrict, DAGRefutation.size]

/-- Dag restriction preserves dependency depth exactly. -/
theorem DAGRefutation.restrict_depth {n : ℕ} {Γ : Finset (Clause n)}
    (P : DAGRefutation n Γ) (ρ : Restriction n) :
    (P.restrict ρ).depth = P.depth := by
  simp [DAGRefutation.restrict, DAGRefutation.depth]

#print axioms validAt_restrict
#print axioms DAGRefutation.restrict_size
#print axioms DAGRefutation.restrict_depth

end PallLean.Paper93.DeepMath.PathB.ResLinParity
