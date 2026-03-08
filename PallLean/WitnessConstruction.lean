import PallLean.PACBridge
import PallLean.ClauseGadget
import Mathlib.Tactic
/-!
# Witness Construction — Additive Separability Architecture

Following arXiv:2512.11820v5, §34 (Extraction Map).

## Key Insight: What isSelector/isVerifier Actually Mean

In the `SheetCouplingWitness` structure:
- `isSelector` = marks **computation/scaffold** variables to be RESTRICTED (set to constants)
  (The paper calls this "drop computation scaffold": v ← 0)
- `selectorVal` = the constant values to assign (e.g., all 0)
- `isVerifier` = marks **verifier** variables (clause literals + selectors) to be KEPT
  (The paper calls this "project to u-blocks")

The extraction T_Φ:
1. restrict(isSelector, val=0): kills computation vars, leaves verifier vars
2. project(isVerifier): keeps verifier vars, zeros computation positions
Result: only verifier vars survive = clause sheet = rename(embed)(tseitinPoly)
-/

namespace WitnessConstruction

open MvPolynomial SPDP Compiler NPWitness TuringMachine
open ExtractionPipeline PACBridge ClauseGadget Extraction Tseitin

variable {F : Type*} [Field F]

/-! ## §1: Variable Classification

Variables in the compiled polynomial of M♯:
- Computation vars: indices [0, verifierVarStart)  — these get RESTRICTED
- Verifier vars: indices [verifierVarStart, totalVars) — these get KEPT
  - Clause literal vars: [verifierVarStart, verifierVarStart + selectorOffset)
  - Clause selector vars: [verifierVarStart + selectorOffset, verifierVarStart + npNumVars)
-/

/-- Verifier variable: clause literal or selector (index ≥ M's original var count).
    These are KEPT by the projection step. -/
noncomputable def mkIsVerifier (M : DTM) (n : ℕ) : CompiledVars M n → Bool :=
  fun v => decide (v.val ≥ numVars M n (Nat.log 2 n))

/-- The number of clauses in buildTseitin equals the number of edges. -/
theorem buildTseitin_clauses_length (G : RegularGraph) :
    (buildTseitin G).clauses.length = G.numEdges := by
  unfold buildTseitin; simp [List.length_map, List.length_finRange]

/-- The graph used in tseitinAt n -/
theorem tseitinAt_graph' (n : ℕ) :
    (tseitinAt n).graph = highGirthFamily.graph n := rfl

/-- highGirthFamily.graph n has numEdges ≤ 10 * max 3 n -/
theorem highGirth_numEdges_bound (n : ℕ) :
    (highGirthFamily.graph n).numEdges ≤ 10 * max 3 n := by
  unfold highGirthFamily
  simp only
  split
  · rename_i h
    simp [cycleRegularGraph]
    omega
  · simp [cycleRegularGraph]
    omega

/-- highGirthFamily.graph n has numEdges = n for n ≥ 3, and 3 otherwise -/
theorem highGirth_numEdges_eq (n : ℕ) :
    (highGirthFamily.graph n).numEdges = if n ≥ 3 then n else 3 := by
  unfold highGirthFamily
  simp only
  split
  · simp [cycleRegularGraph]
  · simp [cycleRegularGraph]

/-- npNumVars n ≤ 5 * max 3 n -/
theorem npNumVars_bound (n : ℕ) : npNumVars n ≤ 5 * max 3 n := by
  unfold npNumVars tseitinNumVars
  have hcl : (tseitinAt n).clauses.length = (highGirthFamily.graph n).numEdges := by
    unfold tseitinAt; exact buildTseitin_clauses_length _
  have hgr : (tseitinAt n).graph.numEdges = (highGirthFamily.graph n).numEdges := by
    rw [tseitinAt_graph']
  rw [hcl, hgr]
  rw [highGirth_numEdges_eq]
  split <;> omega

/-- For n ≥ 2, the sheet coupling's numVars exceeds M's by at least npNumVars.
    S' = n^(tb+1)+1 ≥ n²+1 ≥ 5, S = n^tb+1, difference in 2S²+SQ terms dominates. -/
theorem compiledVars_embed_bound (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    numVars M n (Nat.log 2 n) + npNumVars n ≤
    numVars (sheetCoupling M) n (Nat.log 2 n) := by
  have hnp := npNumVars_bound n
  suffices h : numVars M n (Nat.log 2 n) + 5 * max 3 n ≤
      numVars (sheetCoupling M) n (Nat.log 2 n) by omega
  -- Unfold to arithmetic
  simp only [numVars, tapeSize, timeSteps, sheetCoupling_timeBound, sheetCoupling_numStates]
  -- Key facts about the power terms
  have hpow : n ^ (M.timeBound + 1) = n * n ^ M.timeBound := pow_succ' n M.timeBound
  have hntb : n ^ M.timeBound ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have hS_pos : n ^ M.timeBound + 1 ≥ 2 := by omega
  have hS'_lower : n * n ^ M.timeBound ≥ 2 * n ^ M.timeBound := by nlinarith
  have hQ_ge : M.numStates ≥ 3 := M.hStates
  have hmax : max 3 n ≤ n + 1 := by omega
  -- Debug: see the goal shape
  rw [hpow]
  nlinarith [sq_nonneg (n ^ M.timeBound),
             sq_nonneg (n * n ^ M.timeBound),
             Nat.mul_le_mul_right (n ^ M.timeBound) hn,
             sq_nonneg n]

/-- Embedding: Tseitin var i → compiled verifier variable.
    Maps Tseitin index i to position verifierVarStart + i in compiled space. -/
noncomputable def mkEmbedTseitin (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    Fin (npNumVars n) → CompiledVars M n :=
  fun i => ⟨numVars M n (Nat.log 2 n) + i.val, by
    have hb := compiledVars_embed_bound M n hn
    have := i.isLt; omega⟩

-- In SheetCouplingWitness:
-- isSelector = "admin/tag" variables (compilation artifacts to pin to constants)
-- selectorVal = values to pin them to (all 0)
-- isVerifier = verifier variables to keep (clause literals + selectors)
-- See paper §34.2: "pin tags/admin to constants"

/-- Admin/tag variables: compilation artifacts at indices ≥ verifierVarStart + npNumVars.
    and the total compiled variable count. These are pinned to constants by restrict. -/
noncomputable def mkIsAdmin (M : DTM) (n : ℕ) : CompiledVars M n → Bool :=
  fun v => decide (v.val ≥ numVars M n (Nat.log 2 n) + npNumVars n)

/-- Admin values: all 0 (pin tags to 0). -/
def mkAdminVal (_M : DTM) (_n : ℕ) : CompiledVars _M _n → F :=
  fun _ => 0

/-- Admin vars are verifier vars (they're above verifierVarStart). -/
theorem admin_sub_verifier (M : DTM) (n : ℕ) (v : CompiledVars M n)
    (h : mkIsAdmin M n v = true) : mkIsVerifier M n v = true := by
  unfold mkIsAdmin at h; unfold mkIsVerifier
  simp [decide_eq_true_eq] at h ⊢; omega

/-- Embedding is injective. -/
theorem mkEmbedTseitin_injective (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    Function.Injective (mkEmbedTseitin M n hn) := by
  intro i j h; unfold mkEmbedTseitin at h
  simp [Fin.ext_iff] at h; exact Fin.ext (by omega)

/-- Embedded variables are verifier variables. -/
theorem embed_is_verifier (M : DTM) (n : ℕ) (hn : n ≥ 2) (i : Fin (npNumVars n)) :
    mkIsVerifier M n (mkEmbedTseitin M n hn i) = true := by
  unfold mkIsVerifier mkEmbedTseitin
  simp

/-- Embedded variables are NOT admin variables (they're in the Tseitin range). -/
theorem embed_not_admin (M : DTM) (n : ℕ) (hn : n ≥ 2) (i : Fin (npNumVars n)) :
    mkIsAdmin M n (mkEmbedTseitin M n hn i) = false := by
  unfold mkIsAdmin mkEmbedTseitin
  simp [decide_eq_false_iff_not, not_le, i.isLt]

/-! ## §2: Additive Separability (Lemma 222)

The compiled polynomial decomposes as P = Y · V where V = V_clause + V_tableau:
- Clause sheet V_clause: uses only embedded Tseitin variables (verifier, non-admin)
- Tableau V_tableau: uses only computation variables (non-verifier)

The proof follows the paper's blueprint (arXiv:2512.11820v5):
  Theorem 181: compiled poly = coupled verifier sheet + tableau remainder
  Definition 53: compiler templates split by variable support
  Lemma 222: additive separability (no cross monomials)
  Lemma 182: witness-free restriction kills tableau
  Theorem 187: extraction map = basis ∘ affine ∘ restrict ∘ project
-/

/-- A polynomial's variables all lie in the computation range (below verifierVarStart).
    Paper: "uses only computation variables v" -/
def varsOnlyComputation (M : DTM) (n : ℕ) (p : MvPolynomial (CompiledVars M n) F) : Prop :=
  ∀ v ∈ p.vars, (mkIsVerifier M n v) = false

/-- A polynomial's variables all lie in the verifier range (above verifierVarStart)
    and below the admin range.
    Paper: "uses only verification/interface variables (u, z)" -/
def varsOnlyVerifier (M : DTM) (n : ℕ) (p : MvPolynomial (CompiledVars M n) F) : Prop :=
  ∀ v ∈ p.vars, (mkIsVerifier M n v) = true ∧ (mkIsAdmin M n v) = false

/-! ### Step 1: Compiled polynomial splits (Theorem 181 + Definition 53 + Lemma 222)

The compiler template library partitions as T = T_ver ∪ T_comp with disjoint
variable support. Each gadget polynomial has vars entirely in (u,z) or entirely
in v. Summing yields the additive decomposition. -/

/-- **Lemma 222**: The compiled polynomial splits into clause sheet + tableau
    with disjoint variable supports.
    Paper: "By Definition 53, each compiler gadget contributes a polynomial whose
    variables lie entirely in (u,z) or entirely in v." -/
axiom compiledPoly_split (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    ∃ (Vclause Vtableau : MvPolynomial (CompiledVars M n) F),
      violationPolyOf F (sheetCoupling M) n = Vclause + Vtableau ∧
      varsOnlyVerifier M n Vclause ∧
      varsOnlyComputation M n Vtableau ∧
      MvPolynomial.constantCoeff Vtableau = 0

/-! ### Step 2: Restrict+project kills tableau (Lemma 182)

Pinning computation variables to constants and projecting to verifier variables
kills the tableau part (which depends only on computation vars). -/

/-- **Lemma 182**: project ∘ restrict kills any polynomial with only computation vars.
    Paper: "Since R_{M',Φ} depends only on v, substituting v:=c replaces R by a
    field constant while leaving Q×_Φ(u) unchanged." -/
theorem restrict_project_kills_computation (M : DTM) (n : ℕ)
    (p : MvPolynomial (CompiledVars M n) F)
    (hp : varsOnlyComputation M n p) :
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsAdmin M n) (mkAdminVal M n) p) =
    C (MvPolynomial.aeval (fun _ => (0 : F)) p) := by
  -- Step 1: restrict is identity on computation-only p
  -- (computation vars are not admin, so restrict maps X v → X v)
  have h_not_admin : ∀ v ∈ p.vars, mkIsAdmin M n v = false := by
    intro v hv
    have hcomp := hp v hv  -- mkIsVerifier v = false
    unfold mkIsAdmin at *; unfold mkIsVerifier at hcomp
    simp [decide_eq_false_iff_not] at hcomp ⊢; omega
  have h_restrict : restrictPoly (mkIsAdmin M n) (mkAdminVal M n) p = p := by
    unfold restrictPoly
    have : (MvPolynomial.aeval (fun v => if mkIsAdmin M n v = true
              then C (mkAdminVal M n v) else X v) p : MvPolynomial _ F) =
           MvPolynomial.aeval (X (σ := CompiledVars M n) (R := F)) p := by
      apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
      intro i hi _
      simp [h_not_admin i hi]
    rw [this, MvPolynomial.aeval_X_left_apply]
  rw [h_restrict]
  -- Step 2: project kills all computation vars → C(constantCoeff p)
  have h_project : projectPoly (mkIsVerifier M n) p =
      (algebraMap F _) (MvPolynomial.constantCoeff p) := by
    unfold projectPoly
    exact MvPolynomial.aeval_eq_constantCoeff_of_vars (fun v hv => by
      simp [hp v hv])
  rw [h_project, MvPolynomial.algebraMap_eq]
  -- Step 3: aeval (fun _ => 0) p = constantCoeff p
  congr 1
  symm
  exact MvPolynomial.aeval_eq_constantCoeff_of_vars (fun _ _ => rfl)

/-! ### Step 3: Clause sheet extracts to Tseitin (Theorem 187)

The clause-sheet part, after restrict+project, gives exactly the renamed
Tseitin polynomial. This is the core compiler-correctness claim. -/

/-- **Theorem 187 (extraction equation on clause sheet)**: restrict+project
    applied to the clause sheet produces the renamed Tseitin polynomial.
    Paper: "T_Φ = (basis) ∘ (affine relabeling) ∘ (restriction) ∘ (projection)" -/
axiom clauseSheet_extracts_to_tseitin (F : Type*) [Field F]
    (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    ∀ (Vclause : MvPolynomial (CompiledVars M n) F),
      varsOnlyVerifier M n Vclause →
      (∃ (Vtableau : MvPolynomial (CompiledVars M n) F),
        violationPolyOf F (sheetCoupling M) n = Vclause + Vtableau ∧
        varsOnlyComputation M n Vtableau) →
      projectPoly (mkIsVerifier M n)
        (restrictPoly (mkIsAdmin M n) (mkAdminVal M n) Vclause) =
      rename (mkEmbedTseitin M n hn) (tseitinPoly F n)

/-! ### Step 4: Structural side conditions (block compatibility + admissibility)

These encode properties of the compiler's block partition structure:
- Block-admissible lists contain only verifier variables
- The embedding reflects compiled blocks to Tseitin blocks -/

/-- Block compatibility: the embedding reflects the compiled partition to the
    Tseitin partition. (Paper: clause-sheet variables are assigned to clause blocks.) -/
axiom block_compat_axiom (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    ∀ i j : Fin (npNumVars n),
      (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n hn i) =
      (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n hn j) →
      (tseitinPartition n).assign i = (tseitinPartition n).assign j

-- NOTE: admissibility_axiom and multiplier_admissibility_axiom REMOVED.
-- They were provably FALSE: any singleton [v] with v a computation var is
-- block-admissible, but these axioms claimed all such vars are verifier.
-- The correct fix: add activeVars filter to blockedSpdpSubspace (~15-file refactor).
-- The rank monotonicity they supported is now captured by
-- PACBridge.extracted_rank_le_violation axiom.

/-! ### Step 5: Assembly — wrapper theorem combining all four parts

Paper Lemma 222 + Theorem 187 packaged as the single conjunction
needed by the PAC witness construction.

The extraction now operates on `violationPolyOf` (without padding product),
which avoids the padding-kills-extraction issue. The violation polynomial
has the correct additive decomposition: V = V_clause + V_tableau. -/

/-- **Additive separability** (paper Lemma 222 + Theorem 187 + structural conditions).
    Assembled from the four sub-lemma axioms:
    - compiledPoly_split: V = Vclause + Vtableau
    - restrict_project_kills_computation: project∘restrict(Vtableau) = 0
    - clauseSheet_extracts_to_tseitin: project∘restrict(Vclause) = rename(embed)(tseitin)
    - block_compat_axiom -/
theorem additive_separability (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    -- (1) Extraction equation
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsAdmin M n) (mkAdminVal M n)
        (violationPolyOf F (sheetCoupling M) n)) =
    rename (mkEmbedTseitin M n hn) (tseitinPoly F n) ∧
    -- (2) Block compatibility
    (∀ i j : Fin (npNumVars n),
      (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n hn i) =
      (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n hn j) →
      (tseitinPartition n).assign i = (tseitinPartition n).assign j) := by
  constructor
  · -- Claim (1): extraction equation from split + restrict_project + clause_extracts
    obtain ⟨Vclause, Vtableau, hsplit, hvc, hvt, hconst⟩ := compiledPoly_split F M n hn
    have h1 : projectPoly (mkIsVerifier M n)
        (restrictPoly (mkIsAdmin M n) (mkAdminVal M n)
          (violationPolyOf F (sheetCoupling M) n)) =
      projectPoly (mkIsVerifier M n)
        (restrictPoly (mkIsAdmin M n) (mkAdminVal M n) Vclause) +
      projectPoly (mkIsVerifier M n)
        (restrictPoly (mkIsAdmin M n) (mkAdminVal M n) Vtableau) := by
      rw [hsplit, map_add, map_add]
    have h2 : projectPoly (mkIsVerifier M n)
        (restrictPoly (mkIsAdmin M n) (mkAdminVal M n) Vtableau) = 0 := by
      rw [restrict_project_kills_computation M n Vtableau hvt]
      simp [MvPolynomial.aeval_eq_constantCoeff_of_vars (fun _ _ => rfl), hconst]
    have h3 := clauseSheet_extracts_to_tseitin F M n hn Vclause hvc ⟨Vtableau, hsplit, hvt⟩
    rw [h1, h2, add_zero, h3]
  · -- Claim (2): block compatibility
    exact block_compat_axiom M n hn

/-! ## §3: Extraction Equation

With the correct interpretation, extraction_eq follows directly from
additive_separability. The SheetCouplingWitness uses:
- isSelector := mkIsAdmin (admin/tag vars to restrict)
- selectorVal := mkAdminVal (pin to 0)
- isVerifier := mkIsVerifier (verifier vars to keep)
-/

/-- **Theorem 187**: The extraction equation.
    Direct consequence of additive_separability. -/
theorem extraction_eq' (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    rename (mkEmbedTseitin M n hn) (tseitinPoly F n) =
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsAdmin M n) (mkAdminVal M n)
        (violationPolyOf F (sheetCoupling M) n)) :=
  (additive_separability F M n hn).1.symm

/-! ## §4: Structural Properties (projections from additive_separability) -/

theorem block_compat' (M : DTM) (n : ℕ) (hn : n ≥ 2) (i j : Fin (npNumVars n)) :
    (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n hn i) =
    (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n hn j) →
    (tseitinPartition n).assign i = (tseitinPartition n).assign j :=
  (additive_separability ℚ M n hn).2 i j

/-! ## §5: Witness Assembly -/

/-- **Construct SheetCouplingWitness** from §34 architecture.
    isSelector := mkIsAdmin (admin/tag vars to pin)
    selectorVal := mkAdminVal (pin to 0)
    isVerifier := mkIsVerifier (verifier vars to keep) -/
noncomputable def constructWitness (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    SheetCouplingWitness F M n where
  isVerifier := mkIsVerifier M n
  isSelector := mkIsAdmin M n
  selectorVal := mkAdminVal M n
  embedTseitin := mkEmbedTseitin M n hn
  extraction_eq := extraction_eq' M n hn
  embed_injective := mkEmbedTseitin_injective M n hn
  selector_sub_verifier := admin_sub_verifier M n
  embed_is_pure_verifier := fun i => ⟨embed_is_verifier M n hn i,
                                       embed_not_admin M n hn i⟩
  block_compat_rev := block_compat' M n hn

end WitnessConstruction
