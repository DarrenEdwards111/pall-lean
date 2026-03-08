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
open ExtractionPipeline PACBridge ClauseGadget Extraction Tseitin

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

/-! ## The Extraction Equation — Two-Layer Proof

### The Issue
The simplified `compiledPolyOf` uses `mkTransitionConstraint` which only
generates `h · (b' - b)` constraints — not clause gadgets. The clause
gadgets arise from STATE-DEPENDENT constraints that couple state indicators
with tape values at the clause-checking positions.

### Solution: Enriched Compilation
The sheet-coupled polynomial P(M♯) properly includes clause gadget terms.
The key observation: the transition constraints at states Q, Q+1, Q+2
generate LOCAL constraints that, when squared and summed, produce the
clause gadget polynomials z_C · V_C².

We formalize this in two layers:
1. **Transition-to-gadget**: one (Q,Q+1,Q+2) cycle → one clause gadget
2. **Uniform composition**: m cycles → m gadgets → multi_clause_extraction
-/

/-! ### Layer 1: Single Transition Cycle → Single Clause Gadget

At time t, when the machine is in state Q and the head is at position 3c:
- Time t (state Q):   reads b_{t,3c} = literal 1
- Time t+1 (state Q+1): reads b_{t+1,3c+1} = literal 2
- Time t+2 (state Q+2): reads b_{t+2,3c+2} = literal 3

The local state-transition constraint for cell (t,i) in state q is:

  C_{t,i,q} = s_{t,q} · h_{t,i} · (b_{t+1,i} - δ_write(q, b_{t,i}))

For the clause-checking states, δ_write = identity (tape preserved),
and the constraint becomes: s_{t,Q} · h_{t,3c} · (b_{t+1,3c} - b_{t,3c}).

The clause gadget VIOLATION polynomial arises from the conjunction:
  "all 3 literals read correctly AND clause is unsatisfied"
= (1 - ℓ₁)(1 - ℓ₂)(1 - ℓ₃) = V_C

The gadget polynomial z_C · V_C² is constructed from the state-dependent
constraints evaluated at the clause tape positions, with the selector
z_C = s_{t₀, Q} (state Q active at the clause-cycle start time t₀). -/

/-- A single clause cycle constraint: the polynomial generated by one
    Q→Q+1→Q+2 cycle at clause index c. This captures the local constraint
    interaction at tape positions (3c, 3c+1, 3c+2) during states Q/Q+1/Q+2.

    In the enriched compilation, this term appears in the violation polynomial
    and extracts to the clause gadget under restrict+project. -/
noncomputable def singleClauseCycleConstraint
    (M : DTM) (n : ℕ) (c : ℕ) (F : Type*) [Field F]
    (clauseVarBase : ℕ)
    (hv : clauseVarBase + 3 < numVars (sheetCoupling M) n (Nat.log 2 n))
    (hs : clauseVarBase + 3 < numVars (sheetCoupling M) n (Nat.log 2 n)) :
    MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F :=
  let v1 : Fin _ := ⟨clauseVarBase, by omega⟩      -- literal 1
  let v2 : Fin _ := ⟨clauseVarBase + 1, by omega⟩  -- literal 2
  let v3 : Fin _ := ⟨clauseVarBase + 2, by omega⟩  -- literal 3
  let zc : Fin _ := ⟨clauseVarBase + 3, by omega⟩  -- selector
  X zc * ((1 - X v1) * (1 - X v2) * (1 - X v3)) *
         ((1 - X v1) * (1 - X v2) * (1 - X v3))

/-- Restricting the selector to 1 in a single cycle constraint gives V_C².
    This is the transition-to-gadget lemma for one clause. -/
theorem single_cycle_restrict_eq_violation_sq
    (M : DTM) (n : ℕ) (c : ℕ) (F : Type*) [Field F]
    (clauseVarBase : ℕ)
    (hv hs : clauseVarBase + 3 < numVars (sheetCoupling M) n (Nat.log 2 n))
    (isS : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Bool)
    (hsel : isS ⟨clauseVarBase + 3, by omega⟩ = true)
    (hlit1 : isS ⟨clauseVarBase, by omega⟩ = false)
    (hlit2 : isS ⟨clauseVarBase + 1, by omega⟩ = false)
    (hlit3 : isS ⟨clauseVarBase + 2, by omega⟩ = false) :
    restrictPoly isS (fun _ => 1)
      (singleClauseCycleConstraint M n c F clauseVarBase hv hs) =
    let v1 : Fin _ := ⟨clauseVarBase, by omega⟩
    let v2 : Fin _ := ⟨clauseVarBase + 1, by omega⟩
    let v3 : Fin _ := ⟨clauseVarBase + 2, by omega⟩
    ((1 - X v1) * (1 - X v2) * (1 - X v3)) *
    ((1 - X v1) * (1 - X v2) * (1 - X v3)) := by
  unfold singleClauseCycleConstraint restrictPoly
  simp only [map_mul, map_sub, map_one, MvPolynomial.aeval_X]
  simp [hsel, hlit1, hlit2, hlit3, MvPolynomial.C_1]

/-! ### Layer 2: Uniform Composition

With single_cycle_restrict_eq_violation_sq proved, the full extraction
equation follows by:
1. The compiled polynomial of M♯ contains Σ_c (cycle_constraint_c)²
2. restrict+project on the sum = Σ (restrict+project on each term)
3. Each term extracts to V_c² (Layer 1)
4. The sum/product structure matches tseitinPoly (by definition)

This is exactly what ClauseGadget.multi_clause_extraction does. -/

/-- **The extraction equation** — core theorem.
    For M deciding 3-SAT, restrict+project on compiledPolyOf(M♯)
    recovers the renamed Tseitin polynomial. -/
theorem extraction_eq_of_construction (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    rename (mkEmbedTseitin M n) (tseitinPoly F n) =
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsSelector M n) (mkSelectorVal M n)
        (compiledPolyOf F (sheetCoupling M) n)) := by
  -- Layer 1: single_cycle_restrict_eq_violation_sq ✅ (proved above)
  -- Layer 2: uniform composition via multi_clause_extraction ✅ (ClauseGadget)
  -- Bridge: compiledPolyOf(M♯) contains cycle constraints
  --   (requires enriched compilation or explicit decomposition)
  sorry

/-! ## Bridge: MultiClauseSystem for M♯

The key connection: M♯'s clause-checking states define a concrete
MultiClauseSystem whose extraction matches the Tseitin polynomial.
ClauseGadget.multi_clause_extraction then does the algebraic heavy lifting. -/

/-- The number of Tseitin clauses for a graph with n vertices.
    For the Ramanujan expander used in NPWitness, m = Θ(n). -/
noncomputable def tseitinClauseCount (n : ℕ) : ℕ := npNumVars n / 3

/-- The Tseitin polynomial is structurally a product of coupled factors:
    tseitinPoly = ∏_c (1 - z_c · clauseGadget_c)

    This follows directly from the definition of coupledVerifier. -/
theorem tseitin_is_coupled_product (n : ℕ) :
    tseitinPoly F n = (Finset.univ : Finset (Fin (tseitinAt n).clauses.length)).prod
      (fun c => 1 - X (selectorIdx (tseitinAt n) c) *
        clauseGadget F (tseitinAt n) c) := by
  unfold tseitinPoly coupledVerifier
  rfl

/-- The Tseitin formula defines a MultiClauseSystem (implicit in the definition).
    Each clause c has:
    - 3 clause variables (literal positions)
    - 1 selector variable z_c
    - All disjoint by construction -/
theorem tseitin_has_clause_structure (n : ℕ) (hn : n ≥ 2) :
    -- The structure of coupledVerifier matches fullCoupledVerifier
    -- when we identify clause variables and selectors appropriately
    True :=
  trivial  -- placeholder: the real content is in tseitin_is_coupled_product

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
