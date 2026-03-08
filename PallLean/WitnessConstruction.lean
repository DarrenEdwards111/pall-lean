import PallLean.PACBridge
import PallLean.ClauseGadget
import Mathlib.Tactic
/-!
# Witness Construction — Building SheetCouplingWitness

## Strategy

The SheetCouplingWitness needs:
1. **extraction_eq**: rename(embed)(tseitin) = project(restrict(compiled(M♯)))
2. **Block compatibility**: injective, block-reflecting embedding
3. **Admissibility**: variable classification respects block structure

We construct this bottom-up:
- Single clause gadget correctness (ClauseGadget.lean ✅)
- Multi-clause composition (ClauseGadget.multi_clause_extraction ✅)
- Bridge from MultiClauseSystem to SheetCouplingWitness (this file)

## Key Insight

The compiled polynomial of M♯ has the form:

  P_{M♯,n} = Y · (V_M + V_clause)

where V_M are M's original constraints and V_clause are the
clause-checking constraints from the 3 extra states.

The extraction restrict+project:
- Kills V_M (original constraints don't involve selector/clause vars)
- Preserves V_clause (clause gadgets are what we designed them for)
- Multi-clause extraction (ClauseGadget) handles V_clause

## Architecture

We define:
1. `clauseSystemOf` — extracts a MultiClauseSystem from M♯'s variable layout
2. `witnessOf` — constructs SheetCouplingWitness from clauseSystemOf
-/

namespace WitnessConstruction

open MvPolynomial SPDP Compiler NPWitness TuringMachine
open ExtractionPipeline PACBridge ClauseGadget Extraction

variable {F : Type*} [Field F]

/-! ## Variable Classification

For M♯ = sheetCoupling M, the variables fall into three categories:
1. **Computation variables**: tape, state, head from M's original states
2. **Clause variables**: the literal values u_{C,1}, u_{C,2}, u_{C,3}
3. **Selector variables**: z_C for each clause C

The isVerifier predicate marks (2) + (3).
The isSelector predicate marks only (3).
-/

/-- Number of clauses in an n-variable 3-SAT instance.
    For Tseitin on a graph with n vertices: m = |E| edges. -/
abbrev numClauses (n : ℕ) : ℕ := n * (n - 1) / 2  -- complete graph edges, upper bound

/-- The verifier variables start after M's original compilation variables -/
def verifierVarStart (M : DTM) (n : ℕ) : ℕ :=
  numVars M n (Nat.log 2 n)

/-- Total variables in M♯'s compilation: M's vars + 4 per clause (3 clause + 1 selector) -/
theorem sheetCoupling_numVars_ge (M : DTM) (n : ℕ) :
    numVars (sheetCoupling M) n (Nat.log 2 n) ≥ numVars M n (Nat.log 2 n) := by
  unfold numVars tapeSize timeSteps sheetCoupling
  -- S(M♯) = n^(tb+1) + 1 ≥ S(M) = n^tb + 1 since n^(tb+1) ≥ n^tb
  -- numVars = S² + S*Q + S² + n + κ, S and Q both grow
  sorry -- nonlinear arithmetic about n^(tb+1) ≥ n^tb

/-! ## Embedding Construction

The embedding maps Tseitin variable indices to compiled variable indices.
Tseitin variables are exactly the clause literal variables. -/

/-- The isSelector predicate: marks selector variables (one per clause).
    Selector for clause c is at position verifierVarStart + 3*numClauses + c -/
noncomputable def mkIsSelector (M : DTM) (n : ℕ) :
    Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Bool :=
  fun v => decide (v.val ≥ verifierVarStart M n + 3 * numClauses n ∧
                   v.val < verifierVarStart M n + 3 * numClauses n + numClauses n)

/-- The isVerifier predicate: marks clause + selector variables -/
noncomputable def mkIsVerifier (M : DTM) (n : ℕ) :
    Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Bool :=
  fun v => decide (v.val ≥ verifierVarStart M n)

/-- Selector values: all set to 1 (activate all clause checking) -/
def mkSelectorVal (M : DTM) (n : ℕ) :
    Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → F :=
  fun _ => 1

/-- The embedding maps Tseitin variable i to clause variable i in
    the compiled variable space -/
noncomputable def mkEmbedTseitin (M : DTM) (n : ℕ) :
    Fin (npNumVars n) → Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) :=
  fun i => ⟨verifierVarStart M n + i.val, by
    have := i.isLt
    have := sheetCoupling_numVars_ge M n
    sorry⟩  -- need: verifierVarStart + npNumVars ≤ numVars(M♯)

/-- The embedding is injective -/
theorem mkEmbedTseitin_injective (M : DTM) (n : ℕ) :
    Function.Injective (mkEmbedTseitin M n : Fin (npNumVars n) →
      Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) := by
  intro i j h
  unfold mkEmbedTseitin at h
  simp [Fin.ext_iff] at h
  exact Fin.ext (by omega)

/-- Embedded clause variables are not selectors -/
theorem embed_not_selector (M : DTM) (n : ℕ) (i : Fin (npNumVars n))
    (hn : npNumVars n ≤ 3 * numClauses n) :
    mkIsSelector M n (mkEmbedTseitin M n i) = false := by
  unfold mkIsSelector mkEmbedTseitin
  simp [decide_eq_false_iff_not]
  intro h
  have := i.isLt
  omega

/-- Embedded clause variables are verifier variables -/
theorem embed_is_verifier (M : DTM) (n : ℕ) (i : Fin (npNumVars n)) :
    mkIsVerifier M n (mkEmbedTseitin M n i) = true := by
  unfold mkIsVerifier mkEmbedTseitin
  simp [decide_eq_true_eq]

/-! ## The Extraction Equation

The extraction equation connects the compiled polynomial to the Tseitin polynomial.
The proof splits into two parts:

### Part A: Compiled polynomial structure
The compiled polynomial P = Y · V where V = Σ C² includes:
- **Original constraints**: booleanity + transition for M's states
- **Clause constraints**: from the Q→Q+1→Q+2 cycle

The clause constraints arise because the transition function at states
Q, Q+1, Q+2 interacts with specific tape cells containing literal values.
Each 3-step cycle (one per clause) generates a clause gadget term.

### Part B: Extraction kills originals, preserves clause gadgets
- restrict(selectors←1): activates all clause checking
- project(verifier vars): kills computation variables
- Original constraints vanish (they don't involve verifier vars)
- Clause gadgets survive → product = Tseitin poly

This decomposition mirrors ClauseGadget.multi_clause_extraction.
-/

/-- **The extraction equation** — core theorem of the construction.

    For a polytime M deciding 3-SAT, the compiled polynomial of M♯,
    after restricting selectors and projecting to verifier variables,
    equals the renamed Tseitin polynomial.

    The proof requires that compiledPolyOf(M♯) contains clause gadget
    terms from the Q→Q+1→Q+2 cycle. This is the deep connection between:
    - TM compilation (Compiler.lean)
    - Sheet coupling transitions (SheetCoupling.lean)
    - Clause gadget algebra (ClauseGadget.lean)

    Architecture:
    1. compiledPolyOf(M♯) = Y · (V_orig + V_clause)
    2. V_clause = Σ_c (z_c · V_c)²  (from clause-checking transitions)
    3. restrict(z_c←1): V_clause → Σ_c V_c²
    4. project(verifier): kills V_orig terms, keeps V_clause
    5. rename(embed): maps clause var indices to compiled var indices
    6. Result = tseitinPoly (by ClauseGadget.multi_clause_extraction)
-/
theorem extraction_eq_of_construction (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    rename (mkEmbedTseitin M n) (tseitinPoly F n) =
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsSelector M n) (mkSelectorVal M n)
        (compiledPolyOf F (sheetCoupling M) n)) := by
  /- The compiled polynomial of sheetCoupling M contains clause gadget
     terms from the 3 extra states. The restrict+project extracts exactly
     these terms, yielding the Tseitin polynomial.

     Key steps (each could be a separate lemma):
     Step 1: compiledPolyOf decomposes as Y · (V_orig + V_clause)
     Step 2: restrict distributes: restrict(Y · (V_o + V_c)) = restrict(Y) · (restrict(V_o) + restrict(V_c))
     Step 3: restrict(V_clause) = Σ V_c² (by ClauseGadget.restrict_selector_gadget)
     Step 4: project kills V_orig (computation-only vars)
     Step 5: project preserves V_clause (verifier vars)
     Step 6: result = rename(embed)(tseitinPoly)
  -/
  sorry

/-! ## Decomposition Lemmas

These lemmas break the extraction equation into independently verifiable steps. -/

/-- Step 1: The compiled polynomial decomposes additively in its violation part.
    V(M♯) = V_orig + V_clause where V_orig uses only computation vars
    and V_clause uses clause + selector vars. -/
theorem violation_decomposition (M : DTM) (n : ℕ) :
    ∃ (V_orig V_clause : MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F),
      violationPoly F (sheetCoupling M) n (Nat.log 2 n)
        (compilationConstraints F (sheetCoupling M) n) = V_orig + V_clause ∧
      (∀ v ∈ V_orig.vars, mkIsVerifier M n v = false) ∧
      (∀ v ∈ V_clause.vars, mkIsVerifier M n v = true ∨ mkIsSelector M n v = true) :=
  sorry

/-- Step 2: Restricting then projecting V_orig gives 0 (no verifier vars). -/
theorem restrict_project_orig_zero (M : DTM) (n : ℕ)
    (p : MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F)
    (h : ∀ v ∈ p.vars, mkIsVerifier M n v = false) :
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsSelector M n) (mkSelectorVal M n) p) = 0 :=
  sorry

/-- Step 3: V_clause after restrict+project = renamed Tseitin. -/
theorem restrict_project_clause_eq_tseitin (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    ∃ (V_clause : MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F),
      projectPoly (mkIsVerifier M n)
        (restrictPoly (mkIsSelector M n) (mkSelectorVal M n) V_clause) =
      rename (mkEmbedTseitin M n) (tseitinPoly F n) :=
  sorry

/-! ## Full Witness Assembly -/

/-- Construct the full SheetCouplingWitness from the clause system.
    Depends on extraction_eq_of_construction and admissibility lemmas. -/
noncomputable def constructWitness (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    SheetCouplingWitness F M n where
  isVerifier := mkIsVerifier M n
  isSelector := mkIsSelector M n
  selectorVal := mkSelectorVal M n
  embedTseitin := mkEmbedTseitin M n
  extraction_eq := extraction_eq_of_construction M n hn
  embed_injective := mkEmbedTseitin_injective M n
  selector_sub_verifier := by
    intro v hv
    unfold mkIsSelector at hv
    unfold mkIsVerifier
    simp [decide_eq_true_eq] at hv ⊢
    omega
  block_compat_rev := by
    intro i j h
    -- The compiled partition assigns each variable to a block based on
    -- its index. Embedded Tseitin vars map to positions that preserve
    -- the Tseitin block structure.
    sorry
  admissible_non_selector := by
    intro S hadm i hi
    -- Block-admissible lists in the compiled partition pick at most one
    -- variable per block. Selector variables are in separate blocks from
    -- computation variables, and admissible lists come from the
    -- compilation structure which doesn't generate selector indices.
    sorry
  admissible_verifier := by
    intro S hadm i hi
    sorry
  admissible_mult_non_selector := by
    intro m S hm hadm v hv
    sorry
  admissible_mult_verifier := by
    intro m S hm hadm v hv
    sorry

end WitnessConstruction
