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
  -- Use support-level characterization directly.
  -- mem_restrictSupport_iff: p ∈ restrictSupport s ↔ p.support ⊆ s
  -- restrictTotalDegree N = restrictSupport { n | n.sum id ≤ N }
  -- p = ∑ s ∈ p.support, monomial s (p.coeff s) [MvPolynomial.as_sum]
  -- pderiv i is linear, so pderiv i p = ∑ s ∈ p.support, pderiv i (monomial s (p.coeff s))
  -- Each term: pderiv i (monomial s c) = monomial (s - single i 1) (c * s i) ∈ restrictTotalDegree N
  -- Sum of members is a member (submodule).
  have : pderiv i p = ∑ s ∈ p.support, pderiv i (monomial s (MvPolynomial.coeff s p)) := by
    conv_lhs => rw [p.as_sum]; rw [map_sum]
  rw [this]
  apply Submodule.sum_mem
  intro s hs
  -- pderiv i (monomial s (p.coeff s)) = monomial (s - single i 1) (p.coeff s * s i)
  rw [pderiv_monomial]
  -- Need: monomial (s - single i 1) (...) ∈ restrictTotalDegree N
  show _ ∈ restrictSupport F _
  rw [mem_restrictSupport_iff]
  intro t ht
  have ht' := Finset.mem_singleton.mp (support_monomial_subset ht)
  subst ht'
  calc (s - Finsupp.single i 1).sum (fun _ e => e)
      ≤ s.sum (fun _ e => e) := by
        apply Finsupp.sum_le_sum_index tsub_le_self
        · intro j _ a b hab; exact hab
        · intro j _; rfl
    _ ≤ N := hp (Finset.mem_coe.mpr hs)

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
        (∀ i ∈ S, i ∈ (Finset.univ : Finset (Fin n))) ∧
        (∀ v ∈ m.vars, v ∈ (Finset.univ : Finset (Fin n))) ∧
        r = m * iterDerivList S p }) :
    q.totalDegree ≤ ℓ + p.totalDegree := by
  obtain ⟨S, m, _, hdeg, _, _, _, rfl⟩ := hq
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
  -- aeval f m where f v = if isTrace v then C(assign v) else X v
  -- For all v ∈ m.vars, isTrace v = false, so f v = X v.
  -- aeval X m = m (by aeval_X_left).
  -- Use eval₂Hom_congr' to equate aeval f m = aeval X m.
  conv_rhs => rw [← AlgHom.id_apply (R := F) m, ← aeval_X_left]
  apply eval₂Hom_congr' rfl _ rfl
  intro i hi _
  simp [hm i hi]

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
    intro q ⟨S, m, hlen, hdeg, hadm, _, _, hq⟩
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
      Submodule.subset_span ⟨S, m, hlen, hdeg, hadm, (fun _ _ => Finset.mem_univ _), (fun _ _ => Finset.mem_univ _), rfl⟩, rfl⟩
  calc Module.finrank F ↥(blockedSpdpSubspace B κ ℓ
        (ExtractionPipeline.restrictPoly isTrace assign p))
      ≤ Module.finrank F ↥(Submodule.map
          (ExtractionPipeline.restrictPoly isTrace assign).toLinearMap
          (blockedSpdpSubspace B κ ℓ p)) :=
        Submodule.finrank_mono hmap
    _ ≤ Module.finrank F ↥(blockedSpdpSubspace B κ ℓ p) :=
        Submodule.finrank_map_le _ _

/-- Restriction with explicit activeVars: when all active vars are non-trace,
    restriction is rank-nonincreasing. This matches the paper (Lemma 33):
    after restriction, the SPDP matrix lives in the smaller ring of free variables.
    The activeVars constraint bakes this in — no external admissibility hypotheses needed. -/
theorem restrict_rank_le_active
    (B : BlockPartition n) (κ ℓ : ℕ)
    (isTrace : Fin n → Bool) (assign : Fin n → F)
    (p : MvPolynomial (Fin n) F)
    (activeVars : Finset (Fin n))
    -- All active vars are non-trace (the only hypothesis needed)
    (hActive : ∀ v ∈ activeVars, isTrace v = false) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.restrictPoly isTrace assign p) activeVars ≤
    blockedSpdpRank B κ ℓ p activeVars := by
  unfold blockedSpdpRank
  have hmap : blockedSpdpSubspace B κ ℓ
      (ExtractionPipeline.restrictPoly isTrace assign p) activeVars ≤
      Submodule.map (ExtractionPipeline.restrictPoly isTrace assign).toLinearMap
        (blockedSpdpSubspace B κ ℓ p activeVars) := by
    unfold blockedSpdpSubspace
    apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hadm, hSa, hma, hq⟩
    -- All S indices are active hence non-trace
    have hSnonTrace : ∀ i ∈ S, isTrace i = false := fun i hi => hActive i (hSa i hi)
    rw [hq, iterDerivList_restrictPoly_comm isTrace assign S hSnonTrace]
    -- All m.vars are active hence non-trace
    have hMnonTrace : ∀ v ∈ m.vars, isTrace v = false := fun v hv => hActive v (hma v hv)
    rw [← restrictPoly_eq_of_vars_nonTrace isTrace assign m hMnonTrace]
    rw [← map_mul]
    exact Submodule.mem_map.mpr ⟨m * iterDerivList S p,
      Submodule.subset_span ⟨S, m, hlen, hdeg, hadm, hSa, hma, rfl⟩, rfl⟩
  -- Need Module.Finite for activeVars-filtered subspaces
  have hfin_p : Module.Finite F ↥(blockedSpdpSubspace B κ ℓ p activeVars) :=
    Module.Finite.of_injective
      (Submodule.inclusion (blockedSpdpSubspace_activeVars_mono B κ ℓ p (Finset.subset_univ activeVars)))
      (Submodule.inclusion_injective _)
  have hfin_rp : Module.Finite F ↥(blockedSpdpSubspace B κ ℓ
      (ExtractionPipeline.restrictPoly isTrace assign p) activeVars) :=
    Module.Finite.of_injective
      (Submodule.inclusion (blockedSpdpSubspace_activeVars_mono B κ ℓ _ (Finset.subset_univ activeVars)))
      (Submodule.inclusion_injective _)
  calc Module.finrank F ↥(blockedSpdpSubspace B κ ℓ
        (ExtractionPipeline.restrictPoly isTrace assign p) activeVars)
      ≤ Module.finrank F ↥(Submodule.map
          (ExtractionPipeline.restrictPoly isTrace assign).toLinearMap
          (blockedSpdpSubspace B κ ℓ p activeVars)) :=
        Submodule.finrank_mono hmap
    _ ≤ Module.finrank F ↥(blockedSpdpSubspace B κ ℓ p activeVars) :=
        Submodule.finrank_map_le _ _

/-- Project with explicit activeVars. Special case of restrict_rank_le_active. -/
theorem project_rank_le_active
    (B : BlockPartition n) (κ ℓ : ℕ)
    (keep : Fin n → Bool)
    (p : MvPolynomial (Fin n) F)
    (activeVars : Finset (Fin n))
    (hActive : ∀ v ∈ activeVars, keep v = true) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.projectPoly keep p) activeVars ≤
    blockedSpdpRank B κ ℓ p activeVars := by
  have heq : ExtractionPipeline.projectPoly keep p =
      ExtractionPipeline.restrictPoly (fun v => !keep v) (fun _ => (0 : F)) p := by
    unfold ExtractionPipeline.projectPoly ExtractionPipeline.restrictPoly
    congr 1; ext v
    cases hk : keep v <;> simp [hk, MvPolynomial.C_0]
  rw [heq]
  apply restrict_rank_le_active
  intro v hv
  simp [Bool.not_eq_true']
  exact hActive v hv

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

/-- Multiplication by C(a) is a linear equivalence (a ≠ 0). -/
noncomputable def mulCLinearEquiv (a : F) (ha : a ≠ 0) :
    MvPolynomial (Fin n) F ≃ₗ[F] MvPolynomial (Fin n) F where
  toLinearMap :=
  { toFun := fun p => MvPolynomial.C a * p
    map_add' := fun p q => by ring
    map_smul' := fun r p => by simp [mul_comm (MvPolynomial.C a), mul_assoc, Algebra.smul_mul_assoc] }
  invFun := fun p => MvPolynomial.C a⁻¹ * p
  left_inv := fun p => by simp [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha]
  right_inv := fun p => by simp [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha]

/-- Gauge (scalar only): multiplication by C(a). Rank-preserving via LinearEquiv. -/
theorem gauge_scalar_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (a : F) (ha : a ≠ 0)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (MvPolynomial.C a * p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- pderiv i (C(a) * p) = C(a) * pderiv i p (since pderiv i (C a) = 0)
  -- So iterDerivList S (C(a)*p) = C(a) * iterDerivList S p.
  -- Generator: m * iterDerivList S (C(a)*p) = m * C(a) * iterDerivList S p
  --   = (C(a) * m) * iterDerivList S p
  -- totalDegree(C(a)*m) = totalDegree(m) ≤ ℓ (C has degree 0).
  -- So each generator of subspace(C(a)*p) is a generator of subspace(p).
  apply Submodule.finrank_mono
  unfold blockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, _, _, hq⟩
  -- Show: iterDerivList S (C a * p) = C a * iterDerivList S p
  have hcomm : ∀ (q : MvPolynomial (Fin n) F) (T : List (Fin n)),
      iterDerivList T (MvPolynomial.C a * q) =
      MvPolynomial.C a * iterDerivList T q := by
    intro q T
    induction T generalizing q with
    | nil => simp [iterDerivList]
    | cons i rest ih =>
      simp only [iterDerivList, List.foldl]
      have hpd : MvPolynomial.pderiv i (MvPolynomial.C a * q) =
          MvPolynomial.C a * MvPolynomial.pderiv i q := by
        rw [Derivation.leibniz]; simp [MvPolynomial.pderiv_C]
      rw [hpd]
      exact ih (MvPolynomial.pderiv i q)
  rw [hq, hcomm p S, ← mul_assoc]
  -- (m * C a) * iterDerivList S p is a generator with multiplier (m * C a)
  -- totalDegree(m * C a) ≤ totalDegree(m) + totalDegree(C a) = totalDegree(m) + 0
  have hdeg' : (m * MvPolynomial.C a).totalDegree ≤ ℓ := by
    calc (m * MvPolynomial.C a).totalDegree
        ≤ m.totalDegree + (MvPolynomial.C a).totalDegree := MvPolynomial.totalDegree_mul m _
      _ = m.totalDegree + 0 := by rw [MvPolynomial.totalDegree_C]
      _ = m.totalDegree := by ring
      _ ≤ ℓ := hdeg
  exact Submodule.subset_span ⟨S, m * MvPolynomial.C a, hlen, hdeg', hadm, (fun _ _ => Finset.mem_univ _), (fun _ _ => Finset.mem_univ _), rfl⟩

/-- pderiv commutes with multiplication by a monomial when the variable
    is not in the monomial's support (pderiv of the monomial is 0). -/
theorem pderiv_mul_monomial_comm
    (m_mono : (Fin n) →₀ ℕ) (i : Fin n) (hi : m_mono i = 0)
    (q : MvPolynomial (Fin n) F) :
    pderiv i (monomial m_mono (1 : F) * q) =
    monomial m_mono (1 : F) * pderiv i q := by
  rw [Derivation.leibniz]
  have : pderiv i (monomial m_mono (1 : F)) = 0 := by
    rw [pderiv_monomial]
    simp [hi]
  simp [this]

/-- iterDerivList commutes with monomial multiplication when all derivative
    variables are outside the monomial's support. -/
theorem iterDerivList_mul_monomial_comm
    (m_mono : (Fin n) →₀ ℕ) (S : List (Fin n))
    (hS : ∀ i ∈ S, m_mono i = 0)
    (q : MvPolynomial (Fin n) F) :
    iterDerivList S (monomial m_mono (1 : F) * q) =
    monomial m_mono (1 : F) * iterDerivList S q := by
  induction S generalizing q with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl]
    rw [pderiv_mul_monomial_comm m_mono i (hS i (by simp))]
    exact ih (fun j hj => hS j (by simp [hj])) (pderiv i q)

/-- Gauge with trivial monomial (m_mono = 0): reduces to scalar gauge. -/
theorem gauge_rank_le_trivial
    (B : BlockPartition n) (κ ℓ : ℕ)
    (a : F) (ha : a ≠ 0)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.gaugePoly a ha 0 p) ≤
    blockedSpdpRank B κ ℓ p := by
  -- gaugePoly a ha 0 p = C(a) * monomial 0 1 * p = C(a) * 1 * p = C(a) * p
  have : ExtractionPipeline.gaugePoly a ha 0 p = MvPolynomial.C a * p := by
    unfold ExtractionPipeline.gaugePoly
    simp [monomial_zero']
  rw [this]
  exact gauge_scalar_rank_le B κ ℓ a ha p

/-- ℓ-monotonicity: larger multiplier degree budget → larger (or equal) rank.
    This is the key composition device for the extraction pipeline. -/
theorem blockedSpdpRank_ell_mono
    (B : BlockPartition n) (κ ℓ ℓ' : ℕ) (hℓ : ℓ ≤ ℓ')
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ p ≤ blockedSpdpRank B κ ℓ' p := by
  unfold blockedSpdpRank
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  intro q ⟨S, m, hlen, hdeg, hadm, hav1, hav2, hq⟩
  exact ⟨S, m, hlen, le_trans hdeg hℓ, hadm, hav1, hav2, hq⟩

theorem gauge_rank_le
    (B : BlockPartition n) (κ ℓ : ℕ)
    (a : F) (ha : a ≠ 0) (m_mono : (Fin n) →₀ ℕ)
    (p : MvPolynomial (Fin n) F)
    (hG : ∀ (S : List (Fin n)), isBlockAdmissible B S →
          ∀ i ∈ S, m_mono i = 0) :
    blockedSpdpRank B κ ℓ (ExtractionPipeline.gaugePoly a ha m_mono p) ≤
    blockedSpdpRank B κ (ℓ + m_mono.sum (fun _ e => e)) p := by
  -- gaugePoly = C(a) * monomial(m_mono, 1) * p
  -- By block-disjointness, both factors commute with admissible derivatives.
  -- Generator: m * ∂^S(C(a) * monomial(m_mono,1) * p)
  --          = m * C(a) * monomial(m_mono,1) * ∂^S(p)
  -- Multiplier degree: deg(m * C(a) * monomial(m_mono,1)) ≤ ℓ + 0 + Δ = ℓ + Δ
  unfold ExtractionPipeline.gaugePoly blockedSpdpRank
  apply Submodule.finrank_mono
  unfold blockedSpdpSubspace
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, _, _, hq⟩
  -- Commutation: derivatives pass through C(a) and monomial(m_mono,1)
  have hcomm_C : ∀ (r : MvPolynomial (Fin n) F) (T : List (Fin n)),
      iterDerivList T (MvPolynomial.C a * r) =
      MvPolynomial.C a * iterDerivList T r := by
    intro r T; induction T generalizing r with
    | nil => simp [iterDerivList]
    | cons j rest ih =>
      simp only [iterDerivList, List.foldl]
      have : pderiv j (MvPolynomial.C a * r) = MvPolynomial.C a * pderiv j r := by
        rw [Derivation.leibniz]; simp [pderiv_C]
      rw [this]; exact ih _
  rw [hq]
  -- Goal: m * iterDerivList S (C a * monomial m_mono 1 * p) ∈ ...
  -- Reassociate: C a * monomial m_mono 1 * p = C a * (monomial m_mono 1 * p)
  rw [show MvPolynomial.C a * monomial m_mono (1 : F) * p =
      MvPolynomial.C a * (monomial m_mono (1 : F) * p) from by ring]
  rw [hcomm_C, iterDerivList_mul_monomial_comm m_mono S (hG S hadm),
      ← mul_assoc, ← mul_assoc]
  -- Multiplier: m * C(a) * monomial(m_mono,1), degree ≤ ℓ + Δ
  have hdeg' : (m * MvPolynomial.C a * monomial m_mono (1 : F)).totalDegree
      ≤ ℓ + m_mono.sum (fun _ e => e) := by
    calc (m * MvPolynomial.C a * monomial m_mono 1).totalDegree
        ≤ (m * MvPolynomial.C a).totalDegree + (monomial m_mono (1 : F)).totalDegree :=
          totalDegree_mul _ _
      _ ≤ m.totalDegree + (monomial m_mono (1 : F)).totalDegree := by
          have : (MvPolynomial.C a : MvPolynomial (Fin n) F).totalDegree = 0 := totalDegree_C a
          linarith [totalDegree_mul m (MvPolynomial.C a)]
      _ ≤ ℓ + m_mono.sum (fun _ e => e) := by
          have hm := MvPolynomial.totalDegree_monomial_le m_mono (1 : F)
          have : m_mono.sum (fun _ => id) = m_mono.sum (fun _ e => e) := by congr 1
          linarith
  exact Submodule.subset_span ⟨S, m * MvPolynomial.C a * monomial m_mono 1,
    hlen, hdeg', hadm, (fun _ _ => Finset.mem_univ _), (fun _ _ => Finset.mem_univ _), rfl⟩

/-! ## Step 6: Composition — wiring to the axiom signature -/

-- The actual wiring to `extraction_rank_monotone` requires:
-- 1. Defining the specific keep/isTrace/assign/gauge for the Tseitin extraction
-- 2. Showing tseitinPoly = gauge(restrict(project(compiledPoly)))
-- 3. Applying the stage lemmas in sequence
-- This is left for the final wiring step.

end ExtractionProof
