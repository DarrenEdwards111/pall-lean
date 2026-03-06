/-
  ExtractionWiring.lean — Replace extraction_rank_monotone axiom

  Decomposes the monolithic axiom into:
  1. One structural axiom (extraction factorization)
  2. One proved theorem (relabel_generators_subset — from bijectivity + partition compat)
  3. Three proved stages (project, restrict, gauge) via ExtractionProof lemmas
  4. A composition theorem connecting them across two polynomial rings

  Net effect: axiom count reduced to 2 (profile_decomposition +
  extraction_factorization). relabel_generators_subset is now a theorem.
-/
import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.SheetCoupling
import PallLean.ExtractionProof
import PallLean.ExtractionPipeline
import Mathlib.Tactic

namespace ExtractionWiring

open MvPolynomial SPDP Compiler NPWitness TuringMachine ExtractionProof Extraction

variable {F : Type*} [Field F]

/-! ## Helper: iterDerivList commutes with rename for injective maps -/

private theorem iterDerivList_rename_map {n₁ n₂ : ℕ} {F : Type*} [CommRing F]
    (ρ : Fin n₁ → Fin n₂) (hρ : Function.Injective ρ)
    (S : List (Fin n₁)) (p : MvPolynomial (Fin n₁) F) :
    iterDerivList (S.map ρ) (MvPolynomial.rename ρ p) =
    MvPolynomial.rename ρ (iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    -- iterDerivList (ρ i :: rest.map ρ) (rename ρ p)
    -- = iterDerivList (rest.map ρ) (pderiv (ρ i) (rename ρ p))   [by def]
    -- = iterDerivList (rest.map ρ) (rename ρ (pderiv i p))        [by pderiv_rename]
    -- = rename ρ (iterDerivList rest (pderiv i p))                 [by IH]
    simp only [iterDerivList, List.map_cons, List.foldl]
    rw [show List.foldl (fun q j => pderiv j q) (pderiv (ρ i) (MvPolynomial.rename ρ p))
            (List.map ρ rest) =
          iterDerivList (rest.map ρ) (pderiv (ρ i) (MvPolynomial.rename ρ p)) from rfl]
    rw [pderiv_rename hρ i p]
    exact ih (pderiv i p)

/-! ## Theorem: relabel_generators_subset (was axiom)

    When we rename variables via a bijective ρ that maps compiled blocks into
    tseitin blocks, the generators of the renamed subspace sit inside the
    image of the source subspace under rename.
-/
theorem relabel_generators_subset
    {n₁ n₂ : ℕ}
    (B₁ : BlockPartition n₁) (B₂ : BlockPartition n₂)
    (ρ : Fin n₁ → Fin n₂)
    (hρ_inj : Function.Injective ρ)
    (hρ_surj : Function.Surjective ρ)
    (hcompat : ∀ i j : Fin n₁, B₁.assign i = B₁.assign j → B₂.assign (ρ i) = B₂.assign (ρ j))
    (p : MvPolynomial (Fin n₁) F)
    (κ ℓ : ℕ) :
    blockedSpdpSubspace B₂ κ ℓ (MvPolynomial.rename ρ p) ≤
    (blockedSpdpSubspace B₁ κ ℓ p).map (MvPolynomial.rename ρ).toLinearMap := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, hq⟩
  have hbij : Function.Bijective ρ := ⟨hρ_inj, hρ_surj⟩
  let e : Fin n₁ ≃ Fin n₂ := Equiv.ofBijective ρ hbij
  let S' := S.map e.symm
  let m' := MvPolynomial.rename e.symm m
  -- ρ ∘ e.symm = id (key rewriting lemma)
  have hρe : ∀ x, ρ (e.symm x) = x := fun x => e.apply_symm_apply x
  have hρe_comp : ρ ∘ e.symm = id := funext hρe
  -- S = S'.map ρ
  have hS_eq : S = S'.map ρ := by
    simp only [S', List.map_map, hρe_comp, List.map_id]
  -- m = rename ρ m'
  have hm_eq : m = MvPolynomial.rename ρ m' := by
    have h1 : MvPolynomial.rename (ρ ∘ ⇑e.symm) m = m := by
      rw [hρe_comp]; simp [MvPolynomial.rename_id, AlgHom.id_apply]
    rw [← h1]; exact (MvPolynomial.rename_rename e.symm ρ m).symm
  -- iterDerivList S (rename ρ p) = rename ρ (iterDerivList S' p)
  have hiter : iterDerivList S (MvPolynomial.rename ρ p) =
      MvPolynomial.rename ρ (iterDerivList S' p) := by
    rw [hS_eq]; exact iterDerivList_rename_map ρ hρ_inj S' p
  -- S'.length = κ
  have hlen' : S'.length = κ := by simp [S', hlen]
  -- m'.totalDegree ≤ ℓ
  have hdeg' : m'.totalDegree ≤ ℓ :=
    le_trans (totalDegree_rename_le _ _) hdeg
  -- S' is block-admissible w.r.t. B₁
  have hadm' : isBlockAdmissible B₁ S' := by
    refine ⟨hadm.1.map e.symm.injective, fun b₁ => ?_⟩
    -- Goal: ((S.map e.symm).filter (B₁.assign · = b₁)).length ≤ 1
    -- Strategy: this filter, mapped back through e, gives a sublist of some B₂-filter on S.
    -- Use monotone_filter_right on S.
    -- First relate the S.map(e.symm) filter to a filter on S:
    -- (S.map e.symm).filter p has same length as S.filter (p ∘ e.symm)
    -- because filter distributes over map (for injective maps, it's a sublist relation;
    -- but actually length equality comes from the bijection).
    -- Actually: for any f and predicate p,
    -- (L.map f).filter p = (L.filter (p ∘ f)).map f  (provable by induction)
    -- So length is the same.
    -- First, relate (S.map e.symm).filter to S.filter
    have hfilt_len : ∀ (L : List (Fin n₂)),
        ((L.map e.symm).filter (fun i => decide (B₁.assign i = b₁))).length =
        (L.filter (fun j => decide (B₁.assign (e.symm j) = b₁))).length := by
      intro L; induction L with
      | nil => simp
      | cons a rest ih =>
        simp only [List.map_cons, List.filter_cons]
        by_cases hc : decide (B₁.assign (e.symm a) = b₁) = true
        · rw [if_pos hc, if_pos hc]; simp [ih]
        · rw [if_neg hc, if_neg hc]; exact ih
    rw [show ((S.map e.symm).filter (fun i => decide (B₁.assign i = b₁))).length =
        (S.filter (fun j => decide (B₁.assign (e.symm j) = b₁))).length from hfilt_len S]
    -- Now show S.filter(B₁.assign(e.symm ·) = b₁) has length ≤ 1
    -- Now show S.filter(B₁.assign(e.symm ·) = b₁) has length ≤ 1
    -- If empty, done. Otherwise pick an element to determine the B₂-block.
    by_cases hempty : (S.filter (fun j => decide (B₁.assign (e.symm j) = b₁))) = []
    · rw [hempty]; simp
    · -- nonempty
      obtain ⟨j₀, hj₀⟩ := List.exists_mem_of_ne_nil _ hempty
      have hj₀_pred : B₁.assign (e.symm j₀) = b₁ := by
        have := List.of_mem_filter hj₀; simp at this; exact this
      -- All elements in this filter map to the same B₂-block
      let b₂ := B₂.assign j₀
      -- This filter is a sublist of S.filter(B₂.assign · = b₂) via monotone_filter_right
      have hsub : (S.filter (fun j => decide (B₁.assign (e.symm j) = b₁))).Sublist
          (S.filter (fun j => decide (B₂.assign j = b₂))) := by
        apply List.monotone_filter_right
        intro j hj
        simp only [decide_eq_true_eq] at hj ⊢
        -- B₁.assign (e.symm j) = b₁ = B₁.assign (e.symm j₀)
        -- By hcompat: B₂.assign (e (e.symm j)) = B₂.assign (e (e.symm j₀))
        -- i.e., B₂.assign j = B₂.assign j₀ = b₂
        have h1 := hcompat (e.symm j) (e.symm j₀) (by rw [hj, hj₀_pred])
        -- h1 : B₂.assign (ρ (e.symm j)) = B₂.assign (ρ (e.symm j₀))
        -- ρ (e.symm x) = x by hρe
        rw [hρe j, hρe j₀] at h1
        exact h1
      calc (S.filter (fun j => decide (B₁.assign (e.symm j) = b₁))).length
          ≤ (S.filter (fun j => decide (B₂.assign j = b₂))).length := hsub.length_le
        _ ≤ 1 := hadm.2 b₂
  -- Assemble
  rw [hq, hiter, hm_eq, ← map_mul]
  exact Submodule.mem_map.mpr
    ⟨m' * iterDerivList S' p, Submodule.subset_span ⟨S', m', hlen', hdeg', hadm', rfl⟩, rfl⟩

/-! ## Structural Axiom: Extraction factorization (includes bijectivity + compat)

    tseitinPoly = C(a) * rename ρ (restrict(project(compiledPoly)))
    with ρ bijective and block-compatible.
-/
axiom extraction_factorization
    (M : DTM) (n : ℕ) :
    ∃ (keep : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Bool)
      (isTrace : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Bool)
      (assign : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → F)
      (ρ : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Fin (npNumVars n))
      (a : F) (_ : a ≠ 0),
    Function.Injective ρ ∧
    Function.Surjective ρ ∧
    (∀ i j, (compiledPartition (sheetCoupling M) n).assign i =
            (compiledPartition (sheetCoupling M) n).assign j →
            (tseitinPartition n).assign (ρ i) = (tseitinPartition n).assign (ρ j)) ∧
    (∀ (S : List (Fin (numVars (sheetCoupling M) n (Nat.log 2 n)))),
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ i ∈ S, isTrace i = false) ∧
    (∀ (S : List (Fin (numVars (sheetCoupling M) n (Nat.log 2 n)))),
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ i ∈ S, keep i = true) ∧
    (∀ (m : MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F)
       (S : List (Fin (numVars (sheetCoupling M) n (Nat.log 2 n)))),
      m.totalDegree ≤ Nat.log 2 n →
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ v ∈ m.vars, isTrace v = false) ∧
    (∀ (m : MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F)
       (S : List (Fin (numVars (sheetCoupling M) n (Nat.log 2 n)))),
      m.totalDegree ≤ Nat.log 2 n →
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ v ∈ m.vars, keep v = true) ∧
    (tseitinPoly F n = C a * MvPolynomial.rename ρ
      (ExtractionPipeline.restrictPoly isTrace assign
        (ExtractionPipeline.projectPoly keep
          (compiledPolyOf F (sheetCoupling M) n))))

/-! ## Main theorem: extraction_rank_monotone — now a theorem, not an axiom -/

theorem extraction_rank_monotone (M : DTM) (n : ℕ) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n) := by
  obtain ⟨keep, isTrace, assign, ρ, a, ha, hρ_inj, hρ_surj, hcompat,
          hB_trace, hB_keep, hM_trace, hM_keep, hfact⟩ :=
    extraction_factorization (F := F) M n
  let κ := Nat.log 2 n
  let ℓ := Nat.log 2 n
  let B := compiledPartition (sheetCoupling M) n
  let cp := compiledPolyOf F (sheetCoupling M) n
  let p1 := ExtractionPipeline.projectPoly keep cp
  let p2 := ExtractionPipeline.restrictPoly isTrace assign p1
  let p3 := MvPolynomial.rename ρ p2
  show blockedSpdpRank (tseitinPartition n) κ ℓ (tseitinPoly F n) ≤
       blockedSpdpRank B κ ℓ cp
  rw [hfact]
  unfold blockedSpdpRank
  -- Stage 1: Gauge (scalar C(a)) — rank nonincreasing
  have h_gauge : blockedSpdpSubspace (tseitinPartition n) κ ℓ (C a * p3) ≤
      blockedSpdpSubspace (tseitinPartition n) κ ℓ p3 := by
    apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, hdeg, hadm, hq⟩
    have hcomm : ∀ (r : MvPolynomial (Fin (npNumVars n)) F) (T : List (Fin (npNumVars n))),
        iterDerivList T (C a * r) = C a * iterDerivList T r := by
      intro r T; induction T generalizing r with
      | nil => simp [iterDerivList]
      | cons j rest ih =>
        simp only [iterDerivList, List.foldl]
        have : pderiv j (C a * r) = C a * pderiv j r := by
          rw [Derivation.leibniz]; simp
        rw [this]; exact ih _
    rw [hq, hcomm p3 S, ← mul_assoc]
    have hdeg' : (m * C a).totalDegree ≤ ℓ :=
      calc (m * C a).totalDegree ≤ m.totalDegree + (C a).totalDegree := totalDegree_mul m _
        _ = m.totalDegree := by rw [totalDegree_C]; ring
        _ ≤ ℓ := hdeg
    exact Submodule.subset_span ⟨S, m * C a, hlen, hdeg', hadm, rfl⟩
  -- Stage 2: Relabel (rename ρ) — rank nonincreasing via proved theorem
  have h_relabel := relabel_generators_subset B (tseitinPartition n) ρ hρ_inj hρ_surj hcompat p2 κ ℓ
  -- Stage 3: Restrict — rank nonincreasing
  have h_restrict : blockedSpdpRank B κ ℓ p2 ≤ blockedSpdpRank B κ ℓ p1 :=
    restrict_rank_le B κ ℓ isTrace assign p1 (hB_trace) (hM_trace)
  -- Stage 4: Project — rank nonincreasing
  have h_project : blockedSpdpRank B κ ℓ p1 ≤ blockedSpdpRank B κ ℓ cp :=
    project_rank_le B κ ℓ keep cp (hB_keep) (hM_keep)
  -- Compose: gauge → relabel → restrict → project
  calc Module.finrank F ↥(blockedSpdpSubspace (tseitinPartition n) κ ℓ (C a * p3))
      ≤ Module.finrank F ↥(blockedSpdpSubspace (tseitinPartition n) κ ℓ p3) :=
        Submodule.finrank_mono h_gauge
    _ ≤ Module.finrank F ↥((blockedSpdpSubspace B κ ℓ p2).map
          (MvPolynomial.rename ρ).toLinearMap) :=
        Submodule.finrank_mono h_relabel
    _ ≤ Module.finrank F ↥(blockedSpdpSubspace B κ ℓ p2) :=
        Submodule.finrank_map_le _ _
    _ ≤ Module.finrank F ↥(blockedSpdpSubspace B κ ℓ p1) := h_restrict
    _ ≤ Module.finrank F ↥(blockedSpdpSubspace B κ ℓ cp) := h_project

end ExtractionWiring
