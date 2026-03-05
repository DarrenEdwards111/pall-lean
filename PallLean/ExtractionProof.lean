/-
  ExtractionProof.lean — Proof of extraction_rank_monotone (Theorem 12.2)

  Strategy:
  1. Module.Finite for blockedSpdpSubspace via restrictTotalDegree
  2. H_restrict: pderiv commutes with aeval on untouched vars
     (uses Mathlib's aeval_sumElim_pderiv_inl)
  3. H_project: special case of restrict (constants = 0)
  4. H_relabel: rename is isomorphism (pderiv_rename)
  5. H_gauge: multiplication by unit preserves span
  6. Compose via subspace inclusion chain
-/
import PallLean.SPDPDefs
import PallLean.ExtractionPipeline
import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace ExtractionProof

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [Field F]

/-! ## Step 1: Module.Finite for blockedSpdpSubspace

All generators m * iterDerivList S p have totalDegree ≤ ℓ + totalDegree p,
so blockedSpdpSubspace ≤ restrictTotalDegree (ℓ + totalDegree p).
Since Fin n is finite, restrictTotalDegree is Module.Finite. -/

/-- pderiv preserves restrictTotalDegree: if p has totalDegree ≤ N,
    then pderiv i p has totalDegree ≤ N. (Derivatives can only reduce degree.) -/
theorem pderiv_mem_restrictTotalDegree (N : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin n) F) (hp : p ∈ restrictTotalDegree (Fin n) F N) :
    pderiv i p ∈ restrictTotalDegree (Fin n) F N := by
  rw [mem_restrictTotalDegree] at hp ⊢
  -- pderiv i p is a sum of monomials, each with degree ≤ degree of
  -- the corresponding original monomial (pderiv_monomial drops degree).
  -- So totalDegree(pderiv i p) ≤ totalDegree(p) ≤ N.
  sorry

/-- Iterated pderiv preserves restrictTotalDegree -/
theorem iterDerivList_mem_restrictTotalDegree (N : ℕ) (S : List (Fin n))
    (p : MvPolynomial (Fin n) F) (hp : p ∈ restrictTotalDegree (Fin n) F N) :
    iterDerivList S p ∈ restrictTotalDegree (Fin n) F N := by
  induction S generalizing p with
  | nil => exact hp
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl]
    exact ih _ (pderiv_mem_restrictTotalDegree N i p hp)

/-- Iterated partial derivative does not increase total degree -/
theorem totalDegree_iterDerivList_le (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList S p).totalDegree ≤ p.totalDegree := by
  have hp : p ∈ restrictTotalDegree (Fin n) F p.totalDegree := by
    rw [mem_restrictTotalDegree]
  have := iterDerivList_mem_restrictTotalDegree p.totalDegree S p hp
  rwa [mem_restrictTotalDegree] at this

/-- Generators of blockedSpdpSubspace have bounded total degree -/
theorem generator_totalDegree_le
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F)
    (q : MvPolynomial (Fin n) F)
    (hq : q ∈ { r : MvPolynomial (Fin n) F | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        r = m * iterDerivList S p }) :
    q.totalDegree ≤ ℓ + p.totalDegree := by
  obtain ⟨S, m, _, hdeg, _, rfl⟩ := hq
  calc (m * iterDerivList S p).totalDegree
      ≤ m.totalDegree + (iterDerivList S p).totalDegree := totalDegree_mul m _
    _ ≤ ℓ + p.totalDegree := by linarith [totalDegree_iterDerivList_le S p]

/-- blockedSpdpSubspace sits inside restrictTotalDegree -/
theorem blockedSpdpSubspace_le_restrictTotalDegree
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    blockedSpdpSubspace B κ ℓ p ≤
      restrictTotalDegree (Fin n) F (ℓ + p.totalDegree) := by
  unfold blockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro q hq
  rw [SetLike.mem_coe, mem_restrictTotalDegree]
  exact generator_totalDegree_le B κ ℓ p q hq

/-- blockedSpdpSubspace is Module.Finite -/
instance blockedSpdpSubspace_finite
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Module.Finite F ↥(blockedSpdpSubspace B κ ℓ p) := by
  have h := blockedSpdpSubspace_le_restrictTotalDegree B κ ℓ p
  exact Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

/-! ## Step 2: Rank monotonicity from subspace inclusion -/

/-- If subspace A ≤ subspace B, then finrank A ≤ finrank B -/
theorem blockedSpdpRank_mono_of_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p q : MvPolynomial (Fin n) F)
    (h : blockedSpdpSubspace B κ ℓ p ≤ blockedSpdpSubspace B κ ℓ q) :
    blockedSpdpRank B κ ℓ p ≤ blockedSpdpRank B κ ℓ q := by
  unfold blockedSpdpRank
  exact Submodule.finrank_mono h

/-! ## Step 3: Restriction stage — the hard one

We need to show: if we apply aeval (setting some variables to constants),
the generators of the blocked subspace map into the original subspace.

Key Mathlib lemma: aeval_sumElim_pderiv_inl

For our setup with Fin n variables, we model restriction as:
  restrictPoly isTrace assign : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F
  restrictPoly isTrace assign = aeval (fun v => if isTrace v then C (assign v) else X v)

The key property: pderiv i (restrictPoly ... p) = restrictPoly ... (pderiv i p)
when isTrace i = false (i.e., we're differentiating w.r.t. a non-restricted variable).
-/

/-- pderiv commutes with restriction on non-restricted variables.
    Proved by induction on the polynomial, following Mathlib's
    proof pattern from aeval_sumElim_pderiv_inl. -/
theorem pderiv_restrictPoly_comm
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (i : Fin n) (hi : isTrace i = false)
    (p : MvPolynomial (Fin n) F) :
    pderiv i (ExtractionPipeline.restrictPoly isTrace assign p) =
    ExtractionPipeline.restrictPoly isTrace assign (pderiv i p) := by
  unfold ExtractionPipeline.restrictPoly
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v h =>
    -- LHS: pderiv i (aeval f (p * X v)) = pderiv i (aeval f p * f v)
    -- RHS: aeval f (pderiv i (p * X v)) = aeval f (pderiv i p * X v + p * pderiv i (X v))
    simp only [map_mul, aeval_X]
    rw [Derivation.leibniz (pderiv i) (aeval _ p) _, Derivation.leibniz (pderiv i) p (X v)]
    simp only [pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X]
    rw [h]
    -- Now both sides have aeval f (pderiv i p) * f v + ...
    -- LHS extra: aeval f p * pderiv i (f v)
    -- RHS extra: aeval f p * aeval f (Pi.single i 1 v)
    -- Need: pderiv i (f v) = aeval f (Pi.single i 1 v)
    by_cases hv : v = i
    · subst hv; simp [hi]
    · -- pderiv i (f v) where f v = if isTrace v then C _ else X v
      -- In either case, when v ≠ i, pderiv i gives 0
      -- And Pi.single i 1 v = 0 when v ≠ i
      have h1 : pderiv i (if isTrace v then (C (assign v) : MvPolynomial (Fin n) F) else X v) = 0 := by
        split
        · simp
        · exact pderiv_X_of_ne hv
      simp [h1, hv]

/-- iterDerivList commutes with restriction on non-restricted variables -/
theorem iterDerivList_restrictPoly_comm
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (S : List (Fin n)) (hS : ∀ i ∈ S, isTrace i = false)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList S (ExtractionPipeline.restrictPoly isTrace assign p) =
    ExtractionPipeline.restrictPoly isTrace assign (iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl]
    rw [pderiv_restrictPoly_comm isTrace assign i (hS i (by simp))]
    exact ih (fun j hj => hS j (by simp [hj])) (pderiv i p)

/-- restrictPoly fixes polynomials whose vars are all non-trace.
    Since R(X v) = X v for non-trace v, and R is an algebra hom,
    R(m) = m for any m with vars ⊆ non-trace variables. -/
theorem restrictPoly_eq_of_vars_nonTrace
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (m : MvPolynomial (Fin n) F)
    (hm : ∀ v ∈ m.vars, isTrace v = false) :
    ExtractionPipeline.restrictPoly isTrace assign m = m := by
  unfold ExtractionPipeline.restrictPoly
  sorry

/-- Restriction stage: rank of restricted polynomial ≤ rank of original.
    Block-admissible multipliers use only non-trace variables, so R(m) = m.
    Then R(m * ∂^S p) = m * ∂^S(R(p)), mapping generators to generators.
    finrank(image of R) ≤ finrank(source) gives the result. -/
theorem restrict_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (p : MvPolynomial (Fin n) F)
    -- Block-admissible derivative indices are non-trace
    (hB : ∀ (S : List (Fin n)), isBlockAdmissible B S →
          ∀ i ∈ S, isTrace i = false)
    -- Block-admissible multipliers use only non-trace variables
    -- (paper: multipliers are block-local, blocks are non-trace)
    (hM : ∀ (m : MvPolynomial (Fin n) F) (S : List (Fin n)),
          m.totalDegree ≤ ℓ → isBlockAdmissible B S →
          ∀ v ∈ m.vars, isTrace v = false) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.restrictPoly isTrace assign p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- R is an AlgHom. By block admissibility, derivative indices and multiplier
  -- variables are all non-trace. So R acts as identity on multipliers and
  -- commutes with derivatives (pderiv_restrictPoly_comm).
  -- Therefore: blockedSpdpSubspace(R(p)) ⊆ Submodule.map R (blockedSpdpSubspace(p))
  -- and finrank(map R S) ≤ finrank(S).
  unfold blockedSpdpRank
  have hmap : blockedSpdpSubspace B κ ℓ
      (ExtractionPipeline.restrictPoly isTrace assign p) ≤
      Submodule.map (ExtractionPipeline.restrictPoly isTrace assign).toLinearMap
        (blockedSpdpSubspace B κ ℓ p) := by
    unfold blockedSpdpSubspace
    apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hadm, hq⟩
    rw [hq, iterDerivList_restrictPoly_comm isTrace assign S (hB S hadm)]
    -- q = m * R(∂^S p). Need to show this is in image of R applied to span.
    -- Since m uses only admissible (non-trace) vars, R(m) = m.
    -- So m * R(∂^S p) = R(m) * R(∂^S p) = R(m * ∂^S p).
    -- And m * ∂^S p is a generator of the original subspace.
    -- m * R(∂^S p) = R(m) * R(∂^S p) = R(m * ∂^S p) since R(m) = m
    rw [← restrictPoly_eq_of_vars_nonTrace isTrace assign m (hM m S hdeg hadm)]
    -- Now: R(m) * R(∂^S p) = R(m * ∂^S p)
    rw [← map_mul]
    -- R(m * ∂^S p) is in the image of R
    exact Submodule.mem_map.mpr ⟨m * iterDerivList S p,
      Submodule.subset_span ⟨S, m, hlen, hdeg, hadm, rfl⟩, rfl⟩
  calc Module.finrank F ↥(blockedSpdpSubspace B κ ℓ
        (ExtractionPipeline.restrictPoly isTrace assign p))
      ≤ Module.finrank F ↥(Submodule.map
          (ExtractionPipeline.restrictPoly isTrace assign).toLinearMap
          (blockedSpdpSubspace B κ ℓ p)) :=
        Submodule.finrank_mono hmap
    _ ≤ Module.finrank F ↥(blockedSpdpSubspace B κ ℓ p) :=
        Submodule.finrank_map_le _ _

/-! ## Steps 4-5: Easy stages -/

/-- Project: setting some variables to 0. Special case of restrict. -/
theorem project_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (keep : Fin n → Bool)
    (p : MvPolynomial (Fin n) F)
    (hB : ∀ (S : List (Fin n)), isBlockAdmissible B S →
          ∀ i ∈ S, keep i = true)
    (hM : ∀ (m : MvPolynomial (Fin n) F) (S : List (Fin n)),
          m.totalDegree ≤ ℓ → isBlockAdmissible B S →
          ∀ v ∈ m.vars, keep v = true) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.projectPoly keep p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- projectPoly keep = restrictPoly (fun v => !keep v) (fun _ => 0)
  -- So this is a special case of restrict_rank_le
  -- projectPoly keep p = aeval (fun v => if keep v then X v else 0)
  -- restrictPoly isTrace assign p = aeval (fun v => if isTrace v then C (assign v) else X v)
  -- With isTrace = (fun v => !keep v) and assign = (fun _ => 0):
  --   fun v => if !keep v then C 0 else X v = fun v => if keep v then X v else 0
  -- So projectPoly = restrictPoly (!keep) (fun _ => 0)
  have heq : ExtractionPipeline.projectPoly keep p =
      ExtractionPipeline.restrictPoly (fun v => !keep v) (fun _ => (0 : F)) p := by
    unfold ExtractionPipeline.projectPoly ExtractionPipeline.restrictPoly
    congr 1; ext v
    cases hk : keep v <;> simp [hk, MvPolynomial.C_0]
  rw [heq]
  apply restrict_rank_le
  · intro S hadm i hi
    simp [Bool.not_eq_true']
    exact hB S hadm i hi
  · intro m S hdeg hadm v hv
    simp [Bool.not_eq_true']
    exact hM m S hdeg hadm v hv

/-- Gauge: multiplication by unit. Rank-preserving. -/
theorem gauge_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (a : F) (ha : a ≠ 0) (m_mono : (Fin n) →₀ ℕ)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.gaugePoly a ha m_mono p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- Gauge multiplies p by u = C(a) * monomial(m,1), a unit in MvPolynomial.
  -- Multiplication by u is an invertible linear map (with inverse: multiply by u⁻¹).
  -- Invertible linear maps preserve rank: rank(u*p) = rank(p), hence ≤.
  -- Concretely: blockedSpdpSubspace(u*p) ≤ image of (·*u) on blockedSpdpSubspace(p),
  -- because m' * ∂^S(u*p) involves Leibniz terms that all lie in the u-scaled span.
  -- Since u is invertible, finrank is preserved.
  sorry

/-! ## Step 6: Composition — wiring to the axiom signature -/

-- The actual wiring to `extraction_rank_monotone` requires:
-- 1. Defining the specific keep/isTrace/assign/gauge for the Tseitin extraction
-- 2. Showing tseitinPoly = gauge(restrict(project(compiledPoly)))
-- 3. Applying the stage lemmas in sequence
-- This is left for the final wiring step.

end ExtractionProof
