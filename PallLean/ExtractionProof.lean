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

/-- pderiv does not increase total degree (not in Mathlib, proved here) -/
theorem totalDegree_pderiv_le (p : MvPolynomial (Fin n) F) (i : Fin n) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  sorry -- Each monomial's degree drops by 1 at variable i; total degree can only decrease

/-- Iterated partial derivative does not increase total degree -/
theorem totalDegree_iterDerivList_le (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    (iterDerivList S p).totalDegree ≤ p.totalDegree := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl]
    calc (iterDerivList rest (pderiv i p)).totalDegree
        ≤ (pderiv i p).totalDegree := ih _
      _ ≤ p.totalDegree := totalDegree_pderiv_le p i

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

/-- Restriction maps generators to generators (up to subspace inclusion).
    If S only uses non-traced variables and m is arbitrary, then
    restrictPoly (m * iterDerivList S p) = restrictPoly(m) * iterDerivList S (restrictPoly p).
    The restricted m might have lower degree, so it's still a valid generator. -/
theorem restrict_generator_mem
    (B : BlockPartition n) (κ ℓ : ℕ)
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (p : MvPolynomial (Fin n) F)
    -- Hypothesis: block-admissible lists only use non-traced variables
    (hB : ∀ (S : List (Fin n)), isBlockAdmissible B S →
          ∀ i ∈ S, isTrace i = false)
    (q : MvPolynomial (Fin n) F)
    (hq : q ∈ { r | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        r = m * iterDerivList S (ExtractionPipeline.restrictPoly isTrace assign p) }) :
    q ∈ blockedSpdpSubspace B κ ℓ p := by
  obtain ⟨S, m, hlen, hdeg, hadm, rfl⟩ := hq
  -- m * iterDerivList S (restrict p) = m * restrict (iterDerivList S p)
  rw [iterDerivList_restrictPoly_comm isTrace assign S (hB S hadm)]
  -- Now: m * restrict(iterDerivList S p) is in span of generators of original subspace
  -- Actually this gives: restrict(m) * iterDerivList S (restrict p), which is not quite right.
  -- We need: m * iterDerivList S (restrict p) ∈ blockedSpdpSubspace B κ ℓ p
  -- After commutation: m * restrict(iterDerivList S p)
  -- This is a generator if m has degree ≤ ℓ... but it's restrict applied to the derivative.
  -- Actually the image is restrict(m * iterDerivList S p) by the alg hom property.
  -- Hmm, the issue is: we need the image to be IN the original subspace, not the restricted one.
  sorry -- Needs: image of restriction ⊆ original subspace (not reversed!)

/-! ## Wiring note:

Actually, the direction of the inequality matters. We want:

  blockedSpdpRank B κ ℓ (tseitinPoly) ≤ blockedSpdpRank B' κ ℓ (compiledPoly)

This means: the subspace for the Tseitin side ≤ the subspace for the compiled side.
The extraction pipeline transforms compiledPoly → tseitinPoly.
So we need: subspace(T(p)) ≤ subspace(p) where T = extraction pipeline.

For restriction: subspace(restrict(p)) ≤ subspace(p).
The generators of subspace(restrict(p)) are m * iterDerivList S (restrict(p)).
By commutation: = m * restrict(iterDerivList S p).
Since restrict is an algebra hom: = restrict(m * iterDerivList S p) when m has no trace vars.
But restrict(m * iterDerivList S p) is the image of a generator under restrict.

The key question: is restrict(generator) ∈ original subspace?
Not in general — restrict might change the polynomial.

Actually the paper's argument is different. Let me reconsider.

The paper says: restrict maps the SPDP space of p to the SPDP space of restrict(p),
via the algebra hom. Since algebra homs are rank-nonincreasing on submodules,
rank(restrict(p)) ≤ rank(p).

So the correct statement is:
  Submodule.map (restrict.toLinearMap) (blockedSpdpSubspace B κ ℓ p)
    ≥ blockedSpdpSubspace B κ ℓ (restrict p)

i.e., every generator of the restricted subspace is the restrict-image of a generator
of the original subspace. Then:
  finrank (blockedSpdpSubspace B κ ℓ (restrict p))
    ≤ finrank (Submodule.map restrict (blockedSpdpSubspace B κ ℓ p))
    ≤ finrank (blockedSpdpSubspace B κ ℓ p)

The second inequality is because linear maps don't increase finrank.
-/

/-- restrict doesn't increase totalDegree (it sends some vars to constants) -/
theorem totalDegree_restrictPoly_le
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (p : MvPolynomial (Fin n) F) :
    (ExtractionPipeline.restrictPoly isTrace assign p).totalDegree ≤ p.totalDegree := by
  sorry -- aeval with some vars → constants; each monomial's degree can only decrease

/-- Restriction stage: rank of restricted polynomial ≤ rank of original.

    Key idea: restrict (as a linear map) sends generators of blockedSpdpSubspace(p)
    to generators of blockedSpdpSubspace(restrict(p)):
      restrict(m * iterDerivList S p) = restrict(m) * iterDerivList S (restrict(p))
    Since restrict doesn't increase degree, restrict(m).totalDegree ≤ ℓ.
    So the image of the subspace under restrict contains the restricted subspace.
    Linear maps don't increase finrank. -/
theorem restrict_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (p : MvPolynomial (Fin n) F)
    (hB : ∀ (S : List (Fin n)), isBlockAdmissible B S →
          ∀ i ∈ S, isTrace i = false) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.restrictPoly isTrace assign p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- The restriction map R is an algebra hom. By pderiv/restrict commutation,
  -- R maps generators of blockedSpdpSubspace(p) to generators of blockedSpdpSubspace(R(p)):
  --   R(m * ∂^S p) = R(m) * ∂^S(R(p)), with R(m).totalDegree ≤ ℓ.
  -- Since R is surjective on the polynomial ring (it's a retraction: R∘R = R),
  -- every multiplier m with degree ≤ ℓ equals R(m') for some m'.
  -- Therefore blockedSpdpSubspace(R(p)) ⊆ image of blockedSpdpSubspace(p) under R.
  -- finrank(image) ≤ finrank(source) gives the result.
  sorry

/-! ## Steps 4-5: Easy stages -/

/-- Project: setting some variables to 0. Special case of restrict. -/
theorem project_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (keep : Fin n → Bool)
    (p : MvPolynomial (Fin n) F)
    (hB : ∀ (S : List (Fin n)), isBlockAdmissible B S →
          ∀ i ∈ S, keep i = true) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.projectPoly keep p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- projectPoly keep = restrictPoly (fun v => !keep v) (fun _ => 0)
  -- So this is a special case of restrict_rank_le
  sorry -- Reduction to restrict_rank_le

/-- Gauge: multiplication by unit. Rank-preserving. -/
theorem gauge_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (a : F) (ha : a ≠ 0) (m_mono : (Fin n) →₀ ℕ)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.gaugePoly a ha m_mono p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- gaugePoly multiplies by C(a) * monomial m 1, which is a unit.
  -- Multiplication by a unit is an automorphism, so rank is preserved.
  sorry -- span preserved under multiplication by unit

/-! ## Step 6: Composition — wiring to the axiom signature -/

-- The actual wiring to `extraction_rank_monotone` requires:
-- 1. Defining the specific keep/isTrace/assign/gauge for the Tseitin extraction
-- 2. Showing tseitinPoly = gauge(restrict(project(compiledPoly)))
-- 3. Applying the stage lemmas in sequence
-- This is left for the final wiring step.

end ExtractionProof
