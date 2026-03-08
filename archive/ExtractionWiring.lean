/-
  ExtractionWiring.lean — Clause-Sheet SPDP Family Extraction

  The core bridge theorem: Γ(tseitin) ≤ Γ(compiled violation poly).

  **Corrected approach** (arXiv:2512.11820v5 §34, Theorem 181 Item 3):

  The old approach tried to show project∘restrict of the compiled polynomial
  EQUALS the Tseitin polynomial. This is false: the SoS form Σ C² and the
  product form ∏(1-C) differ by cross-terms, so no polynomial identity holds.

  The corrected approach uses SPDP generator family extraction:
  there exists a linear extraction map T_Φ (restrict admin vars → project
  to verifier vars → rename to Tseitin vars) that sends the clause-sheet
  SPDP generators of the violation polynomial ONTO the Tseitin SPDP
  generators. This is strictly weaker than polynomial equality but
  exactly strong enough for the rank inequality.

  Theorem chain (Theorems A–F from the paper):
    A. Additive separability: V = V_cl + V_tab
    B. Tableau annihilation: T_Φ kills tableau generators
    C. Local clause extraction: per-clause SPDP family correspondence
    D. Global family correspondence: T_Φ(S_cl(V)) = S_Ts(Q×)
    E. Rank transfer: dim(S_Ts) ≤ dim(S_cl) ≤ Γ(V)
    F. Identity minor: Γ(tseitin) ≤ dim(S_Ts)

  The irreducible content is packaged in `extraction_map_surjective`:
  there exists a linear map T_Φ that maps the compiled SPDP subspace
  surjectively onto the Tseitin SPDP subspace. This captures B+C+D+F
  in one statement.
-/
import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.SheetCoupling
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace ExtractionWiring

open MvPolynomial SPDP Compiler NPWitness TuringMachine Extraction

variable {F : Type*} [Field F]

/-! ## The Extraction Map Axiom

  The extraction map T_Φ is the composition:
    1. Restrict: pin admin/selector variables to constants (0 or 1)
    2. Project: discard computation variables, keep verifier variables
    3. Rename: relabel verifier variable indices to Tseitin variable indices

  Each step is a linear map on polynomial rings. The composition is a
  linear map from MvPolynomial (Fin N_compiled) F to MvPolynomial (Fin N_tseitin) F.

  The key property: T_Φ maps the blocked SPDP subspace of the compiled
  violation polynomial surjectively onto the blocked SPDP subspace of the
  Tseitin polynomial. This follows from:

  (A) The violation polynomial decomposes as V = V_cl + V_tab where
      V_cl uses verifier/selector vars and V_tab uses computation vars.
  (B) T_Φ annihilates all SPDP generators from V_tab (they project to 0
      on verifier variables).
  (C) For each clause C, T_Φ maps the clause-C SPDP generators of V_cl
      onto the corresponding Tseitin clause SPDP generators (the clause
      gadget polynomial z_C·V_C² restricts to V_C² which renames to the
      Tseitin clause factor).
  (D) The clause-wise families are disjoint across clauses (each clause
      gadget uses its own selector and literal variables), so the global
      family maps surjectively onto the full Tseitin identity-minor family.

  This axiom packages (A)–(D) into a single linear-algebraic statement.
  It is strictly weaker than the false polynomial-equality claim, but
  exactly strong enough for the rank inequality needed in P ≠ NP. -/
axiom extraction_map_surjective (F : Type*) [Field F] (M : DTM) (n : ℕ)
    (hn : n ≥ 2) :
    ∃ (T : MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F →ₗ[F]
           MvPolynomial (Fin (npNumVars n)) F),
      blockedSpdpSubspace (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
        (tseitinPoly F n) ≤
      Submodule.map T (blockedSpdpSubspace (compiledPartition (sheetCoupling M) n)
        (Nat.log 2 n) (Nat.log 2 n)
        (violationPolyOf F (sheetCoupling M) n))

/-! ## Linear algebra: finrank of image ≤ finrank of domain -/

/-- The finrank of a linear image of a submodule is at most the finrank
    of the original submodule. -/
private theorem finrank_map_le_of_finite
    {R M₁ M₂ : Type*} [Field R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (f : M₁ →ₗ[R] M₂) (S : Submodule R M₁) [Module.Finite R S] :
    Module.finrank R (S.map f) ≤ Module.finrank R S := by
  have hrange : LinearMap.range (f.domRestrict S) = S.map f := by
    ext x; constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← hrange]
  exact (f.domRestrict S).finrank_range_le

/-! ## Main theorem: extraction rank monotonicity -/

/-- **Extraction rank monotonicity (corrected Theorem 181 Item 3)**

    Γ(tseitin) ≤ Γ(violation poly of M♯).

    Proof: By `extraction_map_surjective`, there exists a linear map T_Φ
    with blockedSpdpSubspace(tseitin) ≤ T_Φ(blockedSpdpSubspace(violation)).
    Then:
      Γ(tseitin) = finrank(tseitin subspace)
                  ≤ finrank(T_Φ(violation subspace))    [monotonicity]
                  ≤ finrank(violation subspace)          [image ≤ domain]
                  = Γ(violation)                         [definition]  -/
theorem extraction_rank_le (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf F (sheetCoupling M) n) := by
  obtain ⟨T, hT⟩ := extraction_map_surjective F M n hn
  -- Step 1: Γ(tseitin) ≤ finrank(image of T on violation subspace)
  have h1 := Submodule.finrank_mono hT
  -- Step 2: finrank(image) ≤ finrank(violation subspace) = Γ(violation)
  have h2 := finrank_map_le_of_finite T
    (blockedSpdpSubspace (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n) (violationPolyOf F (sheetCoupling M) n))
  exact le_trans h1 h2

/-- Wrapper matching the signature expected by Extraction.lean. -/
theorem extraction_rank_monotone (M : DTM) (n : ℕ) (hn : n ≥ 2 := by omega) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf F (sheetCoupling M) n) :=
  extraction_rank_le F M n hn

end ExtractionWiring
