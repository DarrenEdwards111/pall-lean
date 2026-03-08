/-
  ExtractionPipeline.lean — Concrete extraction stage definitions +
  generic rank monotonicity under pipeline composition.
  
  Based on Darren's skeleton: stages as AlgHom, stagewise subspace inclusion
  hypotheses, endpoint composition theorem.
-/
import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import Mathlib.Tactic

namespace ExtractionPipeline

open MvPolynomial SPDP

section Core

variable {F : Type*} [Field F]
variable {σ : Type*} [DecidableEq σ]

/-! ## Concrete stage operations -/

/-- PROJECT: set dropped variables to 0. keep v = true → keep X_v; else X_v := 0. -/
noncomputable def projectPoly (keep : σ → Bool) : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  MvPolynomial.aeval (fun v => if keep v then X v else 0)

/-- RESTRICT: set trace variables to constants. isTrace v = true → plug assign(v). -/
noncomputable def restrictPoly (isTrace : σ → Bool) (assign : σ → F) :
    MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  MvPolynomial.aeval (fun v => if isTrace v then C (assign v) else X v)

/-- RELABEL: rename variables along ρ : σ → τ. -/
noncomputable def relabelPoly {τ : Type*} [DecidableEq τ] (ρ : σ → τ) :
    MvPolynomial σ F →ₐ[F] MvPolynomial τ F :=
  MvPolynomial.aeval (fun v => X (ρ v))

/-- GAUGE: multiply by nonzero scalar * monomial (a unit in the polynomial ring). -/
noncomputable def gaugePoly (a : F) (ha : a ≠ 0) (m : σ →₀ ℕ) :
    MvPolynomial σ F → MvPolynomial σ F :=
  fun p => (C a) * (monomial m 1) * p

/-! ## Blocked SPDP rank interface (parameterized by generators) -/

variable (blockedSpdpGens : ℕ → ℕ → MvPolynomial σ F → Set (MvPolynomial σ F))

def blockedSpdpSubspace' (κ ℓ : ℕ) (p : MvPolynomial σ F) : Submodule F (MvPolynomial σ F) :=
  Submodule.span F (blockedSpdpGens κ ℓ p)

noncomputable def blockedSpdpRank' (κ ℓ : ℕ) (p : MvPolynomial σ F) : ℕ :=
  Module.finrank F (blockedSpdpSubspace' blockedSpdpGens κ ℓ p)

/-! ## Generic monotonicity: subspace inclusion → rank inequality -/

theorem blockedSpdpRank_mono' (κ ℓ : ℕ) {p q : MvPolynomial σ F}
    [Module.Finite F ↥(blockedSpdpSubspace' blockedSpdpGens κ ℓ q)]
    (h : blockedSpdpSubspace' blockedSpdpGens κ ℓ p ≤
         blockedSpdpSubspace' blockedSpdpGens κ ℓ q) :
    blockedSpdpRank' blockedSpdpGens κ ℓ p ≤
    blockedSpdpRank' blockedSpdpGens κ ℓ q := by
  exact Submodule.finrank_mono h

/-! ## Stagewise hypotheses -/

variable (κ ℓ : ℕ)

variable
  (H_project : ∀ (keep : σ → Bool) (p : MvPolynomial σ F),
    blockedSpdpSubspace' blockedSpdpGens κ ℓ (projectPoly keep p) ≤
    blockedSpdpSubspace' blockedSpdpGens κ ℓ p)
  (H_restrict : ∀ (isTrace : σ → Bool) (assign : σ → F) (p : MvPolynomial σ F),
    blockedSpdpSubspace' blockedSpdpGens κ ℓ (restrictPoly isTrace assign p) ≤
    blockedSpdpSubspace' blockedSpdpGens κ ℓ p)
  (H_gauge : ∀ (a : F) (ha : a ≠ 0) (m : σ →₀ ℕ) (p : MvPolynomial σ F),
    blockedSpdpSubspace' blockedSpdpGens κ ℓ (gaugePoly a ha m p) ≤
    blockedSpdpSubspace' blockedSpdpGens κ ℓ p)

/-! ## Endpoint theorem: pipeline is rank-nonincreasing -/

/-- Pipeline on σ-variables: gauge ∘ restrict ∘ project.
    Relabel handled separately (changes variable type). -/
theorem extraction_rank_monotone_sigma
    (H_project : ∀ (keep : σ → Bool) (p : MvPolynomial σ F),
      blockedSpdpSubspace' blockedSpdpGens κ ℓ (projectPoly keep p) ≤
      blockedSpdpSubspace' blockedSpdpGens κ ℓ p)
    (H_restrict : ∀ (isTrace : σ → Bool) (assign : σ → F) (p : MvPolynomial σ F),
      blockedSpdpSubspace' blockedSpdpGens κ ℓ (restrictPoly isTrace assign p) ≤
      blockedSpdpSubspace' blockedSpdpGens κ ℓ p)
    (H_gauge : ∀ (a : F) (ha : a ≠ 0) (m : σ →₀ ℕ) (p : MvPolynomial σ F),
      blockedSpdpSubspace' blockedSpdpGens κ ℓ (gaugePoly a ha m p) ≤
      blockedSpdpSubspace' blockedSpdpGens κ ℓ p)
    (keep : σ → Bool) (isTrace : σ → Bool) (assign : σ → F)
    (a : F) (ha : a ≠ 0) (m : σ →₀ ℕ) (p : MvPolynomial σ F)
    [Module.Finite F ↥(blockedSpdpSubspace' blockedSpdpGens κ ℓ p)] :
    blockedSpdpRank' blockedSpdpGens κ ℓ
      (gaugePoly a ha m (restrictPoly isTrace assign (projectPoly keep p))) ≤
    blockedSpdpRank' blockedSpdpGens κ ℓ p := by
  -- Chain: gauge ≤ restrict ≤ project ≤ original via H_gauge, H_restrict, H_project
  -- Each step uses blockedSpdpRank_mono' (needs Module.Finite instances from degree bounds)
  have h1 := H_gauge a ha m (restrictPoly isTrace assign (projectPoly keep p))
  have h2 := H_restrict isTrace assign (projectPoly keep p)
  have h3 := H_project keep p
  have h12 : blockedSpdpSubspace' blockedSpdpGens κ ℓ
      (restrictPoly isTrace assign (projectPoly keep p)) ≤
    blockedSpdpSubspace' blockedSpdpGens κ ℓ p := le_trans h2 h3
  have h123 : blockedSpdpSubspace' blockedSpdpGens κ ℓ
      (gaugePoly a ha m (restrictPoly isTrace assign (projectPoly keep p))) ≤
    blockedSpdpSubspace' blockedSpdpGens κ ℓ p := le_trans h1 h12
  exact Submodule.finrank_mono h123

/-!
## Wiring guide

To replace `extraction_rank_monotone` in your project:
1. Instantiate σ as your compiled variable type (e.g. `Fin v`)
2. Set p := compiledPolyOf F M n
3. Define keep, isTrace, assign, a, ha, m for the paper's extraction
4. Prove (or axiomatize) H_project, H_restrict, H_gauge for your gens
5. Show tseitinPoly = gaugePoly a ha m (restrictPoly isTrace assign (projectPoly keep p))
6. Apply extraction_rank_monotone_sigma

Relabeling across different variable namespaces:
Use MvPolynomial.renameAlgHom and prove rank invariance by transporting
generators through the induced algebra isomorphism.
-/

end Core

end ExtractionPipeline
