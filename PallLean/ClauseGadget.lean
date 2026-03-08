import PallLean.SPDPDefs
import PallLean.TuringMachine
import PallLean.NPWitness
import PallLean.TseitinDefs
import PallLean.ExtractionPipeline
import Mathlib.Tactic
/-!
# Clause Gadget — Single Clause Sheet Coupling Correctness

## Design (Theorem 181, single clause)

For a single 3-SAT clause C = (ℓ₁ ∨ ℓ₂ ∨ ℓ₃), the clause gadget introduces:
- **3 clause variables** u₁, u₂, u₃ (the literal values)
- **1 selector variable** z_C

The gadget polynomial is:

  g_C(u, z) = z_C · V_C(u)²

where V_C(u) = (1 - ℓ₁)(1 - ℓ₂)(1 - ℓ₃) is the clause violation polynomial.
V_C(u) = 0 iff the clause is satisfied.

The coupled verifier for this clause is:

  q_C(u, z) = 1 - z_C · V_C(u)²

Properties:
1. When z_C = 1 (selector activated): q_C = 1 - V_C² = 0 iff clause satisfied
2. When z_C = 0 (selector off): q_C = 1 (trivially nonzero)

## Key Lemma

After restricting z_C ← 1 and projecting out non-clause variables:

  project(restrict(g_C)) = V_C(u)²

This is the atomic unit of the PAC extraction.
-/

namespace ClauseGadget

open MvPolynomial SPDP

/-! ## Variable Layout for a Single Clause Gadget

For a clause with 3 literals, we use 4 variables:
- Index 0: u₁ (first literal value)
- Index 1: u₂ (second literal value)
- Index 2: u₃ (third literal value)
- Index 3: z_C (selector)
-/

/-- Number of variables in a single clause gadget -/
abbrev clauseVars : ℕ := 4

/-- Variable indices -/
def u₁ : Fin clauseVars := 0
def u₂ : Fin clauseVars := 1
def u₃ : Fin clauseVars := 2
def zC : Fin clauseVars := 3

/-- Clause violation polynomial: V_C = (1 - u₁)(1 - u₂)(1 - u₃)
    V_C = 0 iff at least one uᵢ = 1 (clause satisfied) -/
noncomputable def clauseViolation (F : Type*) [Field F] :
    MvPolynomial (Fin clauseVars) F :=
  (1 - X u₁) * (1 - X u₂) * (1 - X u₃)

/-- Clause gadget constraint: z_C · V_C² -/
noncomputable def clauseGadgetPoly (F : Type*) [Field F] :
    MvPolynomial (Fin clauseVars) F :=
  X zC * clauseViolation F * clauseViolation F

/-- Coupled verifier factor: 1 - z_C · V_C² -/
noncomputable def coupledFactor (F : Type*) [Field F] :
    MvPolynomial (Fin clauseVars) F :=
  1 - clauseGadgetPoly F

/-! ## Restriction and Projection -/

/-- Selector restriction: set z_C ← 1 -/
noncomputable def restrictSelector (F : Type*) [Field F] :
    MvPolynomial (Fin clauseVars) F →ₐ[F] MvPolynomial (Fin clauseVars) F :=
  ExtractionPipeline.restrictPoly
    (fun v => decide (v = zC))  -- isTrace: only z_C is trace
    (fun _ => 1)                 -- assign all trace vars to 1

/-- Projection to clause variables: keep u₁, u₂, u₃; drop z_C -/
noncomputable def projectClause (F : Type*) [Field F] :
    MvPolynomial (Fin clauseVars) F →ₐ[F] MvPolynomial (Fin clauseVars) F :=
  ExtractionPipeline.projectPoly
    (fun v => decide (v ≠ zC))  -- keep: everything except z_C

/-- V_C² in clause variables only (no selector) -/
noncomputable def violationSquared (F : Type*) [Field F] :
    MvPolynomial (Fin clauseVars) F :=
  clauseViolation F * clauseViolation F

/-! ## Single Clause Correctness Lemma -/

/-- Restricting z_C to 1 in the gadget polynomial gives V_C² -/
private theorem aeval_selector (F : Type*) [Field F] :
    aeval (fun v : Fin clauseVars => if decide (v = zC) then (C 1 : MvPolynomial (Fin clauseVars) F) else X v)
      (X zC : MvPolynomial (Fin clauseVars) F) = C 1 := by
  simp [aeval_X, zC]

private theorem u_ne_zC (v : Fin clauseVars) (hv : v = u₁ ∨ v = u₂ ∨ v = u₃) :
    ¬(v = zC) := by
  rcases hv with rfl | rfl | rfl <;> decide

private theorem aeval_clause_var (F : Type*) [Field F] (v : Fin clauseVars)
    (hv : v = u₁ ∨ v = u₂ ∨ v = u₃) :
    aeval (fun w : Fin clauseVars => if decide (w = zC) then (C 1 : MvPolynomial (Fin clauseVars) F) else X w)
      (X v : MvPolynomial (Fin clauseVars) F) = X v := by
  simp [aeval_X, show ¬(v = zC) from u_ne_zC v hv]

private theorem aeval_violation (F : Type*) [Field F] :
    aeval (fun v : Fin clauseVars => if decide (v = zC) then (C 1 : MvPolynomial (Fin clauseVars) F) else X v)
      (clauseViolation F) = clauseViolation F := by
  unfold clauseViolation
  simp only [map_mul, map_sub, map_one]
  congr 1; congr 1
  · congr 1; exact aeval_clause_var F u₁ (Or.inl rfl)
  · congr 1; exact aeval_clause_var F u₂ (Or.inr (Or.inl rfl))
  · congr 1; exact aeval_clause_var F u₃ (Or.inr (Or.inr rfl))

/-- aeval that fixes non-zC variables is identity on polynomials not involving zC -/
private theorem aeval_clause_violation (F : Type*) [Field F] :
    aeval (fun v : Fin clauseVars =>
      if decide (v = zC) then (C 1 : MvPolynomial (Fin clauseVars) F) else X v)
      (clauseViolation F) = clauseViolation F := by
  unfold clauseViolation
  simp only [map_mul, map_sub, map_one, MvPolynomial.aeval_X]
  -- Each X uᵢ: decide (uᵢ = zC) = false, so if branch gives X uᵢ
  have h1 : decide (u₁ = zC) = false := by decide
  have h2 : decide (u₂ = zC) = false := by decide
  have h3 : decide (u₃ = zC) = false := by decide
  simp [h1, h2, h3]

theorem restrict_selector_gadget (F : Type*) [Field F] :
    restrictSelector F (clauseGadgetPoly F) = violationSquared F := by
  unfold restrictSelector clauseGadgetPoly violationSquared
  unfold ExtractionPipeline.restrictPoly
  simp only [map_mul]
  -- aeval(X zC) = if zC = zC then C 1 else X zC = C 1
  have h1 : aeval (fun v : Fin clauseVars =>
      if decide (v = zC) then (C 1 : MvPolynomial _ F) else X v)
      (X zC : MvPolynomial _ F) = C 1 := by
    simp [MvPolynomial.aeval_X]
  -- aeval(V) = V since V doesn't involve zC
  have h2 : aeval (fun v : Fin clauseVars =>
      if decide (v = zC) then (C 1 : MvPolynomial _ F) else X v)
      (clauseViolation F) = clauseViolation F :=
    aeval_clause_violation F
  rw [h1, h2]
  simp [MvPolynomial.C_1]

/-- Projecting after restriction leaves the clause variables unchanged
    (z_C is already a constant, projecting it to 0 doesn't change the poly) -/
private theorem aeval_project_violation (F : Type*) [Field F] :
    aeval (fun v : Fin clauseVars =>
      if decide (v ≠ zC) then (X v : MvPolynomial (Fin clauseVars) F) else 0)
      (clauseViolation F) = clauseViolation F := by
  unfold clauseViolation
  simp only [map_mul, map_sub, map_one, MvPolynomial.aeval_X]
  have h1 : decide (u₁ ≠ zC) = true := by decide
  have h2 : decide (u₂ ≠ zC) = true := by decide
  have h3 : decide (u₃ ≠ zC) = true := by decide
  simp [h1, h2, h3]

theorem project_after_restrict (F : Type*) [Field F] :
    projectClause F (restrictSelector F (clauseGadgetPoly F)) =
    violationSquared F := by
  rw [restrict_selector_gadget]
  unfold projectClause violationSquared
  unfold ExtractionPipeline.projectPoly
  simp only [map_mul, aeval_project_violation]

/-- The coupled factor after restriction: 1 - V_C² -/
theorem restrict_coupled_factor (F : Type*) [Field F] :
    restrictSelector F (coupledFactor F) = 1 - violationSquared F := by
  unfold coupledFactor
  simp only [map_sub, map_one]
  rw [restrict_selector_gadget]

/-! ## Block Partition for Clause Gadget -/

/-- Block partition: each clause variable in its own block, selector in overflow -/
noncomputable def clauseBlock : SPDP.BlockPartition clauseVars where
  numBlocks := 4
  assign := fun v => v  -- each variable is its own block

/-- The selector is in its own block -/
theorem selector_own_block :
    clauseBlock.assign zC ≠ clauseBlock.assign u₁ ∧
    clauseBlock.assign zC ≠ clauseBlock.assign u₂ ∧
    clauseBlock.assign zC ≠ clauseBlock.assign u₃ := by
  unfold clauseBlock zC u₁ u₂ u₃
  refine ⟨by decide, by decide, by decide⟩

/-! ## Multi-Clause Composition (sketch)

For m clauses, the full coupled verifier is:

  Q×(u, z) = ∏_{C=1}^{m} (1 - z_C · V_C(u_C)²)

Each clause uses disjoint clause variables u_C = (u_{C,1}, u_{C,2}, u_{C,3})
and its own selector z_C.

The extraction for the full system:
1. Restrict all selectors z_C ← 1 for packed clauses
2. Project out all non-clause variables
3. Result = ∏(1 - V_C²) = tseitinPoly (in coupled verifier form)

This is a uniform repetition of the single-clause gadget.
-/

/-- A multi-clause system with m clauses -/
structure MultiClauseSystem (m : ℕ) where
  /-- Total number of variables: 3m clause vars + m selectors + k compute vars -/
  totalVars : ℕ
  /-- Number of compute (non-clause, non-selector) variables -/
  computeVars : ℕ
  /-- totalVars = 3m + m + computeVars -/
  vars_eq : totalVars = 3 * m + m + computeVars
  /-- Embedding of clause variables for clause c -/
  clauseEmbed : Fin m → Fin 3 → Fin totalVars
  /-- Embedding of selector for clause c -/
  selectorEmbed : Fin m → Fin totalVars
  /-- All embeddings injective and disjoint -/
  clause_injective : ∀ c₁ c₂ : Fin m, ∀ i₁ i₂ : Fin 3,
    clauseEmbed c₁ i₁ = clauseEmbed c₂ i₂ → c₁ = c₂ ∧ i₁ = i₂
  selector_injective : ∀ c₁ c₂ : Fin m,
    selectorEmbed c₁ = selectorEmbed c₂ → c₁ = c₂
  clause_selector_disjoint : ∀ c₁ : Fin m, ∀ i : Fin 3, ∀ c₂ : Fin m,
    clauseEmbed c₁ i ≠ selectorEmbed c₂

/-- The full coupled verifier for a multi-clause system -/
noncomputable def fullCoupledVerifier {m : ℕ} (F : Type*) [Field F]
    (sys : MultiClauseSystem m) :
    MvPolynomial (Fin sys.totalVars) F :=
  Finset.univ.prod (fun (c : Fin m) =>
    let v₁ := sys.clauseEmbed c ⟨0, by omega⟩
    let v₂ := sys.clauseEmbed c ⟨1, by omega⟩
    let v₃ := sys.clauseEmbed c ⟨2, by omega⟩
    let zc := sys.selectorEmbed c
    let vc := (1 - X v₁) * (1 - X v₂) * (1 - X v₃)
    1 - X zc * vc * vc)

/-- isSelector for multi-clause: marks selector variables -/
def multiIsSelector {m : ℕ} (sys : MultiClauseSystem m) :
    Fin sys.totalVars → Bool :=
  fun v => (Finset.univ.filter (fun c : Fin m => sys.selectorEmbed c = v)).card > 0

/-- isVerifier for multi-clause: marks clause + selector variables (not compute) -/
def multiIsVerifier {m : ℕ} (sys : MultiClauseSystem m) :
    Fin sys.totalVars → Bool :=
  fun v =>
    multiIsSelector sys v ||
    (Finset.univ.filter (fun (ci : Fin m × Fin 3) =>
      sys.clauseEmbed ci.1 ci.2 = v)).card > 0

/-- Helper: aeval that keeps non-selector vars is identity on clause vars -/
private theorem aeval_restrict_clause_var {m : ℕ} {N : ℕ} (F : Type*) [Field F]
    (isS : Fin N → Bool) (val : Fin N → F)
    (v : Fin N) (hv : isS v = false) :
    aeval (fun w : Fin N =>
      if isS w then (C (val w) : MvPolynomial (Fin N) F) else X w)
      (X v : MvPolynomial (Fin N) F) = X v := by
  simp [MvPolynomial.aeval_X, hv]

/-- Helper: aeval that keeps verifier vars is identity on them -/
private theorem aeval_project_verifier_var {N : ℕ} (F : Type*) [Field F]
    (isV : Fin N → Bool)
    (v : Fin N) (hv : isV v = true) :
    aeval (fun w : Fin N =>
      if isV w then (X w : MvPolynomial (Fin N) F) else 0)
      (X v : MvPolynomial (Fin N) F) = X v := by
  simp [MvPolynomial.aeval_X, hv]

/-- After restricting all selectors to 1 and projecting to verifier vars,
    the coupled verifier becomes ∏(1 - V_C²).

    This is the multi-clause generalization of restrict_selector_gadget +
    project_after_restrict. -/
theorem multi_clause_extraction {m : ℕ} (F : Type*) [Field F]
    (sys : MultiClauseSystem m) :
    ExtractionPipeline.projectPoly (multiIsVerifier sys)
      (ExtractionPipeline.restrictPoly (multiIsSelector sys) (fun _ => 1)
        (fullCoupledVerifier F sys)) =
    Finset.univ.prod (fun (c : Fin m) =>
      let v₁ := sys.clauseEmbed c ⟨0, by omega⟩
      let v₂ := sys.clauseEmbed c ⟨1, by omega⟩
      let v₃ := sys.clauseEmbed c ⟨2, by omega⟩
      let vc := (1 - X v₁) * (1 - X v₂) * (1 - X v₃)
      1 - vc * vc) := by
  -- Clause vars are not selectors
  have hclause_not_sel : ∀ c : Fin m, ∀ i : Fin 3,
      multiIsSelector sys (sys.clauseEmbed c i) = false := by
    intro c i
    show multiIsSelector sys (sys.clauseEmbed c i) = false
    unfold multiIsSelector
    simp only [gt_iff_lt, Nat.pos_iff_ne_zero, ne_eq, decide_eq_false_iff_not, not_not,
               Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c' _
    exact fun h => sys.clause_selector_disjoint c i c' h.symm
  -- Selectors are selectors
  have hsel_is_sel : ∀ c : Fin m,
      multiIsSelector sys (sys.selectorEmbed c) = true := by
    intro c; unfold multiIsSelector
    simp [Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_univ]
  -- Clause vars are verifier vars
  have hclause_verif : ∀ c : Fin m, ∀ i : Fin 3,
      multiIsVerifier sys (sys.clauseEmbed c i) = true := by
    intro c i; unfold multiIsVerifier
    simp [Bool.or_eq_true, Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_univ]
  -- Unfold and distribute over products
  unfold fullCoupledVerifier ExtractionPipeline.restrictPoly ExtractionPipeline.projectPoly
  rw [map_prod, map_prod]
  congr 1; ext c
  -- Distribute over the factor's arithmetic
  simp only [map_sub, map_one, map_mul, MvPolynomial.aeval_X, map_ofNat, MvPolynomial.aeval_C]
  -- Apply the concrete values for selectors and clause vars
  simp [hsel_is_sel c, hclause_not_sel c 0, hclause_not_sel c 1, hclause_not_sel c 2,
        hclause_verif c 0, hclause_verif c 1, hclause_verif c 2, MvPolynomial.C_1]

end ClauseGadget
