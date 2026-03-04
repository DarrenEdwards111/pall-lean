/-
  ExtractionPipeline.lean — Concrete extraction stage definitions +
  generic rank monotonicity under pipeline composition.
-/
import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import Mathlib.Tactic

namespace ExtractionPipeline

open MvPolynomial SPDP

variable {F : Type*} [Field F]
variable {σ : Type*} [DecidableEq σ]

/-! ## Stage 1: PROJECT — set dropped variables to 0 -/

noncomputable def projectPoly (keep : σ → Bool) :
    MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  MvPolynomial.aeval (fun v => if keep v then X v else 0)

/-! ## Stage 2: RESTRICT — set trace variables to constants -/

noncomputable def restrictPoly (isTrace : σ → Bool) (assign : σ → F) :
    MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  MvPolynomial.aeval (fun v => if isTrace v then C (assign v) else X v)

/-! ## Stage 3: RELABEL — rename variables along ρ : σ → τ -/

noncomputable def relabelPoly {τ : Type*} [DecidableEq τ] (ρ : σ → τ) :
    MvPolynomial σ F →ₐ[F] MvPolynomial τ F :=
  MvPolynomial.aeval (fun v => X (ρ v))

/-! ## Stage 4: GAUGE — multiply by invertible element -/

noncomputable def gaugePoly (u : MvPolynomial σ F) (hu : u ≠ 0) :
    MvPolynomial σ F → MvPolynomial σ F :=
  fun p => u * p

/-! ## Generic rank monotonicity -/

/-- If V ≤ W as submodules, then finrank V ≤ finrank W. -/
theorem finrank_mono_of_le {V W : Submodule F (MvPolynomial σ F)}
    [Module.Finite F V] [Module.Finite F W]
    (h : V ≤ W) : Module.finrank F V ≤ Module.finrank F W :=
  Submodule.finrank_mono h

/-! ## Stage-level rank monotonicity lemmas -/

/-- Projection doesn't increase blockedSpdpRank.
    Proof idea: projectPoly maps each generator ∂^α p to ∂^α (project p),
    which is in the span of generators of the projected polynomial. -/
theorem project_rank_le {n : ℕ} (keep : Fin n → Bool)
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (projectPoly keep p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- Setting variables to 0 maps generators into the span
  -- ∂^α (eval p) = eval (∂^α p) by chain rule (evaluation commutes with derivation)
  -- So the subspace of the projected poly ≤ subspace of original
  sorry

/-- Restriction doesn't increase blockedSpdpRank. -/
theorem restrict_rank_le {n : ℕ} (isTrace : Fin n → Bool) (assign : Fin n → F)
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (restrictPoly isTrace assign p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- Same argument as projection: eval₂ commutes with derivation
  sorry

/-- Relabeling by injection preserves blockedSpdpRank.
    (Injective rename = algebra isomorphism on the image.) -/
theorem relabel_rank_le {τ : Type*} [DecidableEq τ] {n m : ℕ}
    (ρ : Fin n → Fin m) (hρ : Function.Injective ρ)
    (B : BlockPartition n) (B' : BlockPartition m) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B' κ ℓ (relabelPoly ρ p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- Injective rename sends generators bijectively
  sorry

/-- Gauge (multiply by unit) preserves blockedSpdpRank.
    Multiplication by invertible element is an automorphism. -/
theorem gauge_rank_le {n : ℕ}
    (u : MvPolynomial (Fin n) F) (hu : u ≠ 0)
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (u * p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- u*p generators are u * (generators of p), spanning a subspace of same dim
  sorry

/-! ## Pipeline composition -/

/-- The full extraction pipeline is rank-nonincreasing.
    This follows by composing the four stage lemmas. -/
theorem pipeline_rank_mono {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p_compiled p_tseitin : MvPolynomial (Fin n) F)
    (keep : Fin n → Bool) (isTrace : Fin n → Bool) (assign : Fin n → F)
    (u : MvPolynomial (Fin n) F) (hu : u ≠ 0)
    (hpipe : p_tseitin = u * restrictPoly isTrace assign (projectPoly keep p_compiled)) :
    blockedSpdpRank B κ ℓ p_tseitin ≤
    blockedSpdpRank B κ ℓ p_compiled := by
  rw [hpipe]
  calc blockedSpdpRank B κ ℓ (u * restrictPoly isTrace assign (projectPoly keep p_compiled))
      ≤ blockedSpdpRank B κ ℓ (restrictPoly isTrace assign (projectPoly keep p_compiled)) :=
        gauge_rank_le u hu B κ ℓ _
    _ ≤ blockedSpdpRank B κ ℓ (projectPoly keep p_compiled) :=
        restrict_rank_le isTrace assign B κ ℓ _
    _ ≤ blockedSpdpRank B κ ℓ p_compiled :=
        project_rank_le keep B κ ℓ p_compiled

end ExtractionPipeline
