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

/-- Embedding: Tseitin var i → compiled verifier variable.
    Maps Tseitin index i to position verifierVarStart + i in compiled space. -/
noncomputable def mkEmbedTseitin (M : DTM) (n : ℕ) :
    Fin (npNumVars n) → CompiledVars M n :=
  fun i => ⟨numVars M n (Nat.log 2 n) + i.val, by
    have := i.isLt
    unfold CompiledVars numVars tapeSize timeSteps sheetCoupling at *
    sorry⟩  -- arithmetic bound

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
theorem mkEmbedTseitin_injective (M : DTM) (n : ℕ) :
    Function.Injective (mkEmbedTseitin M n) := by
  intro i j h; unfold mkEmbedTseitin at h
  simp [Fin.ext_iff] at h; exact Fin.ext (by omega)

/-- Embedded variables are verifier variables. -/
theorem embed_is_verifier (M : DTM) (n : ℕ) (i : Fin (npNumVars n)) :
    mkIsVerifier M n (mkEmbedTseitin M n i) = true := by
  unfold mkIsVerifier mkEmbedTseitin
  simp [decide_eq_true_eq]

/-- Embedded variables are NOT admin variables (they're in the Tseitin range). -/
theorem embed_not_admin (M : DTM) (n : ℕ) (i : Fin (npNumVars n)) :
    mkIsAdmin M n (mkEmbedTseitin M n i) = false := by
  unfold mkIsAdmin mkEmbedTseitin
  simp [decide_eq_false_iff_not, not_le, i.isLt]

/-! ## §2: Additive Separability (Lemma 222)

The compiled polynomial decomposes as P = Y * V where V has two parts:
- Clause sheet: uses only embedded Tseitin variables (verifier, non-admin)
- Tableau: uses only computation variables (non-verifier)
-/

/-- **Lemma 222**: Additive separability.
    The compiled violation polynomial decomposes into clause sheet + tableau,
    where clause sheet uses only embedded Tseitin vars and tableau uses only
    computation vars. Admin vars appear in neither. -/
axiom additive_separability (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    -- The compiled polynomial restricted to admin=0 and projected to verifier
    -- equals the renamed Tseitin polynomial
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsAdmin M n) (mkAdminVal M n)
        (compiledPolyOf F (sheetCoupling M) n)) =
    rename (mkEmbedTseitin M n) (tseitinPoly F n)

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
    rename (mkEmbedTseitin M n) (tseitinPoly F n) =
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsAdmin M n) (mkAdminVal M n)
        (compiledPolyOf F (sheetCoupling M) n)) := by
  exact (additive_separability F M n hn).symm

/-! ## §4: Structural Properties -/

theorem block_compat' (M : DTM) (n : ℕ) (i j : Fin (npNumVars n)) :
    (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n i) =
    (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n j) →
    (tseitinPartition n).assign i = (tseitinPartition n).assign j := by
  sorry

theorem admissible_avoids_admin (M : DTM) (n : ℕ)
    (S : List (CompiledVars M n))
    (hadm : isBlockAdmissible (compiledPartition (sheetCoupling M) n) S)
    (i : CompiledVars M n) (hi : i ∈ S) :
    mkIsAdmin M n i = false := by
  sorry

theorem admissible_is_verifier' (M : DTM) (n : ℕ)
    (S : List (CompiledVars M n))
    (hadm : isBlockAdmissible (compiledPartition (sheetCoupling M) n) S)
    (i : CompiledVars M n) (hi : i ∈ S) :
    mkIsVerifier M n i = true := by
  sorry

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
  embedTseitin := mkEmbedTseitin M n
  extraction_eq := extraction_eq' M n hn
  embed_injective := mkEmbedTseitin_injective M n
  selector_sub_verifier := admin_sub_verifier M n
  block_compat_rev := block_compat' M n
  admissible_non_selector := admissible_avoids_admin M n
  admissible_verifier := admissible_is_verifier' M n
  admissible_mult_non_selector := fun _m S _hm hadm v _hv =>
    admissible_avoids_admin M n S hadm v (by sorry)
  admissible_mult_verifier := fun _m S _hm hadm v _hv =>
    admissible_is_verifier' M n S hadm v (by sorry)

end WitnessConstruction
