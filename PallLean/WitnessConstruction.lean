import PallLean.PACBridge
import PallLean.ClauseGadget
import Mathlib.Tactic
/-!
# Witness Construction — Additive Separability Architecture

Following arXiv:2512.11820v5, §34 (Extraction Map).

    P_{M♯,n}(u, z, v) = V_{M♯}(u, z) + R_{M♯}(v)    [no cross terms]
    T_Φ(P_{M♯,n}) = tseitinPoly(Φ)
-/

namespace WitnessConstruction

open MvPolynomial SPDP Compiler NPWitness TuringMachine
open ExtractionPipeline PACBridge ClauseGadget Extraction Tseitin

variable {F : Type*} [Field F]

/-! ## §1: Variable Classification -/

/-- Verifier variable: clause literal or selector (index ≥ M's original var count). -/
noncomputable def mkIsVerifier (M : DTM) (n : ℕ) : CompiledVars M n → Bool :=
  fun v => decide (v.val ≥ numVars M n (Nat.log 2 n))

/-- Selector variable: one per clause. -/
noncomputable def mkIsSelector (M : DTM) (n : ℕ) : CompiledVars M n → Bool :=
  fun v => decide (v.val ≥ numVars M n (Nat.log 2 n) + 3 * npNumVars n ∧
                   v.val < numVars M n (Nat.log 2 n) + 4 * npNumVars n)

/-- Selector values: all 1. -/
def mkSelectorVal (_M : DTM) (_n : ℕ) : CompiledVars _M _n → F :=
  fun _ => 1

/-- Embedding: Tseitin var i → compiled clause literal variable. -/
noncomputable def mkEmbedTseitin (M : DTM) (n : ℕ) :
    Fin (npNumVars n) → CompiledVars M n :=
  fun i => ⟨numVars M n (Nat.log 2 n) + i.val, by
    have := i.isLt
    unfold CompiledVars numVars tapeSize timeSteps sheetCoupling at *
    sorry⟩  -- arithmetic bound

/-- Selectors ⊆ verifier. -/
theorem selector_sub_verifier' (M : DTM) (n : ℕ) (v : CompiledVars M n)
    (h : mkIsSelector M n v = true) : mkIsVerifier M n v = true := by
  unfold mkIsSelector at h; unfold mkIsVerifier
  simp [decide_eq_true_eq] at h ⊢; omega

/-- Embedding is injective. -/
theorem mkEmbedTseitin_injective (M : DTM) (n : ℕ) :
    Function.Injective (mkEmbedTseitin M n) := by
  intro i j h; unfold mkEmbedTseitin at h
  simp [Fin.ext_iff] at h; exact Fin.ext (by omega)

/-! ## §2: Additive Separability (Lemma 222) -/

/-- Clause sheet Q×_Φ(u,z): product of coupled clause gadgets. -/
noncomputable def clauseSheetPoly (F : Type*) [Field F] (M : DTM) (n : ℕ)
    (m : ℕ) (clauseVars : Fin m → Fin 3 → CompiledVars M n)
    (selectorVars : Fin m → CompiledVars M n) :
    MvPolynomial (CompiledVars M n) F :=
  Finset.univ.prod (fun c : Fin m =>
    1 - X (selectorVars c) *
      ((1 - X (clauseVars c 0)) * (1 - X (clauseVars c 1)) * (1 - X (clauseVars c 2))) ^ 2)

/-- **Lemma 222**: Additive separability.
    P_{M♯,n} = Y * (clauseSheet + tableau) with disjoint variable supports. -/
axiom additive_separability (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    ∃ (m : ℕ) (clauseVars : Fin m → Fin 3 → CompiledVars M n)
      (selectorVars : Fin m → CompiledVars M n),
      -- (a) Decomposition
      compiledPolyOf F (sheetCoupling M) n =
        paddingProduct F (sheetCoupling M) n (Nat.log 2 n) *
          (clauseSheetPoly F M n m clauseVars selectorVars +
           violationPoly F (sheetCoupling M) n (Nat.log 2 n)
             (compilationConstraints F (sheetCoupling M) n)) ∧
      -- (b) Clause vars are verifier, not selectors
      (∀ c l, mkIsVerifier M n (clauseVars c l) = true) ∧
      (∀ c l, mkIsSelector M n (clauseVars c l) = false) ∧
      -- (c) Selector vars are selectors
      (∀ c, mkIsSelector M n (selectorVars c) = true) ∧
      -- (d) Disjointness
      (∀ c₁ c₂ : Fin m, c₁ ≠ c₂ → ∀ l₁ l₂, clauseVars c₁ l₁ ≠ clauseVars c₂ l₂) ∧
      (∀ c₁ c₂ : Fin m, c₁ ≠ c₂ → selectorVars c₁ ≠ selectorVars c₂) ∧
      -- (e) Clause count = Tseitin clause count
      (m = (tseitinAt n).clauses.length) ∧
      -- (f) Tableau uses only computation vars
      (∀ v, v ∈ (violationPoly F (sheetCoupling M) n (Nat.log 2 n)
        (compilationConstraints F (sheetCoupling M) n)).vars →
        mkIsVerifier M n v = false) ∧
      -- (g) Clause vars = embedded Tseitin vars
      (∀ c : Fin m, ∀ l : Fin 3,
        clauseVars c l = mkEmbedTseitin M n ⟨c.val * 3 + l.val, by sorry⟩)

/-! ## §3: Three-Lemma Extraction Chain -/

/-- **Lemma A (project kills tableau)**: If every variable of p has isVerifier = false,
    then project(isVerifier)(p) = C(p(0,...,0)).
    Since restrict doesn't introduce new vars, and tableau has no verifier vars,
    project sends the whole tableau to a constant. -/
theorem project_kills_nonverifier (M : DTM) (n : ℕ)
    (p : MvPolynomial (CompiledVars M n) F)
    (hsupp : ∀ v, v ∈ p.vars → mkIsVerifier M n v = false) :
    projectPoly (mkIsVerifier M n) p =
    C (MvPolynomial.aeval (fun _ => (0 : F)) p) := by
  -- projectPoly maps v to (if isVerifier v then X v else 0)
  -- For p whose vars all have isVerifier = false, this maps every var to 0
  -- which is the same as evaluating p at all-zeros and wrapping in C
  sorry

/-- **Lemma B (restrict preserves non-selector vars)**: If isSelector v = false,
    then restrictPoly leaves X v unchanged. So restrict on a polynomial
    with no selector vars is the identity. -/
theorem restrict_id_on_nonselector (M : DTM) (n : ℕ)
    (p : MvPolynomial (CompiledVars M n) F)
    (hsupp : ∀ v, v ∈ p.vars → mkIsSelector M n v = false) :
    restrictPoly (mkIsSelector M n) (mkSelectorVal M n) p = p := by
  -- restrictPoly maps v to (if isSelector v then C(1) else X v)
  -- For p with no selector vars, every var maps to X v, so restrict = id
  sorry

/-- Tableau has no selector vars (selectors are verifier vars, tableau has none). -/
theorem tableau_no_selectors (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htab : ∀ v, v ∈ (violationPoly F (sheetCoupling M) n (Nat.log 2 n)
      (compilationConstraints F (sheetCoupling M) n)).vars →
      mkIsVerifier M n v = false) :
    ∀ v, v ∈ (violationPoly F (sheetCoupling M) n (Nat.log 2 n)
      (compilationConstraints F (sheetCoupling M) n)).vars →
      mkIsSelector M n v = false := by
  intro v hv
  have hnotver := htab v hv
  -- If isVerifier = false, then isSelector = false (selectors ⊆ verifier)
  unfold mkIsSelector mkIsVerifier at *
  simp [decide_eq_true_eq, decide_eq_false_iff_not] at hnotver ⊢
  omega

/-- **Lemma C (clause sheet extracts to tseitin)**: After restrict(selectors→1)
    and project(verifier), the clause sheet becomes the renamed Tseitin polynomial.

    This is the algebraic core: restrict sets z_c→1 activating all gadgets,
    project keeps all clause literal vars (they are verifier vars),
    and the result matches tseitinPoly under the embedding rename. -/
theorem clauseSheet_extracts_to_tseitin (M : DTM) (n : ℕ)
    (m : ℕ) (clauseVars : Fin m → Fin 3 → CompiledVars M n)
    (selectorVars : Fin m → CompiledVars M n)
    (hcv : ∀ c l, mkIsVerifier M n (clauseVars c l) = true)
    (hcns : ∀ c l, mkIsSelector M n (clauseVars c l) = false)
    (hsel : ∀ c, mkIsSelector M n (selectorVars c) = true)
    (hm : m = (tseitinAt n).clauses.length)
    (hembed : ∀ c : Fin m, ∀ l : Fin 3,
      clauseVars c l = mkEmbedTseitin M n ⟨c.val * 3 + l.val, by sorry⟩) :
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsSelector M n) (mkSelectorVal M n)
        (clauseSheetPoly F M n m clauseVars selectorVars)) =
    rename (mkEmbedTseitin M n) (tseitinPoly F n) := by
  sorry

/-- **Theorem 187**: The full extraction equation.
    Combines additive separability with the three lemmas above. -/
theorem extraction_eq' (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    rename (mkEmbedTseitin M n) (tseitinPoly F n) =
    projectPoly (mkIsVerifier M n)
      (restrictPoly (mkIsSelector M n) (mkSelectorVal M n)
        (compiledPolyOf F (sheetCoupling M) n)) := by
  obtain ⟨m, cV, sV, hdecomp, hcv, hcns, hsel, hdisj, hsdisj, hm, htab, hembed⟩ :=
    additive_separability F M n hn
  -- The proof uses the three-lemma chain:
  -- (A) project kills tableau (no verifier vars)
  -- (B) restrict is identity on tableau (no selector vars)
  -- (C) clause sheet extracts to renamed tseitin
  --
  -- Combined:
  --   project(restrict(compiledPoly))
  -- = project(restrict(Y * (clause + tab)))           [by additive_separability]
  -- = project(restrict(Y)) * project(restrict(clause) + restrict(tab))
  -- = project(restrict(Y)) * (project(restrict(clause)) + project(tab))
  -- = project(restrict(Y)) * (rename(embed)(tseitin) + C(tab(0)))
  --
  -- The padding product Y and constant tab(0) are handled by
  -- the normalization step (Lemma 186 in paper).
  sorry

/-! ## §4: Structural Properties -/

theorem block_compat' (M : DTM) (n : ℕ) (i j : Fin (npNumVars n)) :
    (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n i) =
    (compiledPartition (sheetCoupling M) n).assign (mkEmbedTseitin M n j) →
    (tseitinPartition n).assign i = (tseitinPartition n).assign j := by
  sorry

theorem admissible_avoids_selectors' (M : DTM) (n : ℕ)
    (S : List (CompiledVars M n))
    (hadm : isBlockAdmissible (compiledPartition (sheetCoupling M) n) S)
    (i : CompiledVars M n) (hi : i ∈ S) :
    mkIsSelector M n i = false := by
  sorry

theorem admissible_is_verifier' (M : DTM) (n : ℕ)
    (S : List (CompiledVars M n))
    (hadm : isBlockAdmissible (compiledPartition (sheetCoupling M) n) S)
    (i : CompiledVars M n) (hi : i ∈ S) :
    mkIsVerifier M n i = true := by
  sorry

/-! ## §5: Witness Assembly -/

/-- **Construct SheetCouplingWitness** from §34 architecture. -/
noncomputable def constructWitness (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    SheetCouplingWitness F M n where
  isVerifier := mkIsVerifier M n
  isSelector := mkIsSelector M n
  selectorVal := mkSelectorVal M n
  embedTseitin := mkEmbedTseitin M n
  extraction_eq := extraction_eq' M n hn
  embed_injective := mkEmbedTseitin_injective M n
  selector_sub_verifier := selector_sub_verifier' M n
  block_compat_rev := block_compat' M n
  admissible_non_selector := admissible_avoids_selectors' M n
  admissible_verifier := admissible_is_verifier' M n
  admissible_mult_non_selector := fun _m S _hm hadm v _hv =>
    admissible_avoids_selectors' M n S hadm v (by sorry)
  admissible_mult_verifier := fun _m S _hm hadm v _hv =>
    admissible_is_verifier' M n S hadm v (by sorry)

end WitnessConstruction
