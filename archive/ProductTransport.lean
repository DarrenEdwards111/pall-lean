import PallLean.ProductProfileSlices
import PallLean.Tseitin

/-!
# ProductTransport

Transport theorem from actual SPDP generators of the coupled verifier product to the
allocation-generated span coming from the Leibniz decomposition.

This is the next concrete step in the profile-compression route: it connects the
real multilinear blocked-SPDP generators of the verifier polynomial to the abstract
allocation/profile machinery.
-/

namespace ProductTransport

open SPDP
open MultilinearSPDP
open ProductProfileSlices
open Tseitin
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- The per-clause product factors of the coupled verifier. -/
noncomputable def verifierFactor
    (Φ : TseitinFormula)
    (c : Fin Φ.clauses.length) :
    MvPolynomial (Fin (tseitinNumVars Φ)) F :=
  1 - X (selectorIdx Φ c) * clauseGadget F Φ c

/-- The coupled verifier is exactly the product of its clause factors. -/
theorem coupledVerifier_eq_prod
    (Φ : TseitinFormula) :
    coupledVerifier F Φ = ∏ c : Fin Φ.clauses.length, verifierFactor (F := F) Φ c := by
  unfold coupledVerifier verifierFactor
  simp

/-- Unbounded allocation span for the coupled verifier factors. -/
noncomputable def verifierAllocSpan
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ) :
    Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F) :=
  Submodule.span F
    { q | ∃ (α : DerivAlloc κ Φ.clauses.length),
        q = shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α }

/--
The raw derivative of the coupled verifier lies in the allocation-product span.
-/
theorem iterDerivList_coupledVerifier_mem_allocSpan
    (Φ : TseitinFormula)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ) :
    iterDerivList S (coupledVerifier F Φ) ∈
      Submodule.span F
        { q | ∃ (α : DerivAlloc κ Φ.clauses.length),
            q = allocProduct (F := F) (verifierFactor (F := F) Φ) S hS α } := by
  rw [coupledVerifier_eq_prod (F := F) Φ]
  simpa [allocProduct] using
    (iterDerivList_prod_in_alloc_span
      (n := tseitinNumVars Φ)
      (F := F)
      (m := Φ.clauses.length)
      (factor := verifierFactor (F := F) Φ)
      (S := S) (hS := hS))

/--
After multiplying by a shift and applying multilinear projection, a genuine verifier
SPDP generator still lies in the shifted allocation span.
-/
theorem shiftedGenerator_coupledVerifier_mem_allocSpan
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ) :
    mlProj (shift * iterDerivList S (coupledVerifier F Φ)) ∈
      verifierAllocSpan (F := F) Φ shift S hS := by
  let L : MvPolynomial (Fin (tseitinNumVars Φ)) F →ₗ[F]
      MvPolynomial (Fin (tseitinNumVars Φ)) F :=
    (mlProjLinearMap (Fin (tseitinNumVars Φ)) F).comp
      { toFun := fun q => shift * q
        map_add' := by intro a b; rw [mul_add]
        map_smul' := by intro c q; rw [smul_eq_mul, smul_eq_mul, mul_assoc] }
  have hmem := iterDerivList_coupledVerifier_mem_allocSpan (F := F) (κ := κ) Φ S hS
  have hmap : L (iterDerivList S (coupledVerifier F Φ)) ∈
      Submodule.map L
        (Submodule.span F
          { q | ∃ (α : DerivAlloc κ Φ.clauses.length),
              q = allocProduct (F := F) (verifierFactor (F := F) Φ) S hS α }) :=
    Submodule.mem_map_of_mem hmem
  change mlProj (shift * iterDerivList S (coupledVerifier F Φ)) ∈ _ at hmap
  have hle :
      Submodule.map L
        (Submodule.span F
          { q | ∃ (α : DerivAlloc κ Φ.clauses.length),
              q = allocProduct (F := F) (verifierFactor (F := F) Φ) S hS α })
      ≤ verifierAllocSpan (F := F) Φ shift S hS := by
    apply Submodule.map_span_le
    intro q hq
    rcases hq with ⟨α, rfl⟩
    apply Submodule.subset_span
    exact ⟨α, rfl⟩
  exact hle hmap

/--
Every concrete multilinear blocked-SPDP generator of the coupled verifier belongs to
the shifted allocation span.
-/
theorem mlBlockedSpdp_generator_coupledVerifier_mem_allocSpan
    (Φ : TseitinFormula)
    (S : List (Fin (tseitinNumVars Φ)))
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (hS : S.length = κ)
    (hdeg : shift.totalDegree ≤ ℓ)
    (hvars : shift.vars ⊆ S.toFinset)
    (hadm : isBlockAdmissible (tseitinPartition (Φ.graph.numVertices)) S) :
    mlProj (shift * iterDerivList S (coupledVerifier F Φ)) ∈
      verifierAllocSpan (F := F) Φ shift S hS :=
  shiftedGenerator_coupledVerifier_mem_allocSpan (F := F) (κ := κ) Φ shift S hS

end ProductTransport
