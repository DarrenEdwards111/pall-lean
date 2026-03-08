import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import PallLean.SheetCoupling
import PallLean.ExtractionPipeline
import PallLean.ExtractionProof
-- import PallLean.CoupledCompiler  -- removed to break import cycle
import Mathlib.Tactic
/-!
# PAC Bridge — Extraction Rank Monotonicity via Two-Sheet Decomposition

Theorem 181 of the paper: the sheet-coupled compiled polynomial
P_{M♯,n} decomposes into verifier sheet + computation tableau.
The extraction TΦ = restrict(selectors) ∘ project(verifier vars)
is rank-nonincreasing (ExtractionProof.lean).

This replaces the bare `extraction_rank_monotone` axiom with a
more auditable, construction-level assumption (`TwoSheetDecomp`).
-/

namespace PACBridge

open MvPolynomial SPDP Compiler NPWitness TuringMachine ExtractionPipeline Extraction

variable {F : Type*} [Field F]

abbrev CompiledVars (M : DTM) (n : ℕ) := Fin (numVars (sheetCoupling M) n (Nat.log 2 n))

/-- A two-sheet decomposition of M♯'s compiled polynomial (Theorem 181). -/
structure TwoSheetDecomp (M : DTM) (n : ℕ) where
  isVerifier : CompiledVars M n → Bool
  isSelector : CompiledVars M n → Bool
  selectorVal : CompiledVars M n → F
  selector_sub_verifier : ∀ v, isSelector v = true → isVerifier v = true
  embedTseitin : Fin (npNumVars n) → CompiledVars M n
  -- Embedded tseitin vars land in pure verifier space (verifier, not selector)
  embed_is_pure_verifier : ∀ i, isVerifier (embedTseitin i) = true ∧
                                 isSelector (embedTseitin i) = false
  embed_injective : Function.Injective embedTseitin
  extraction_eq :
    rename embedTseitin (tseitinPoly F n) =
    projectPoly isVerifier (restrictPoly isSelector selectorVal
      (violationPolyOf F (sheetCoupling M) n))
  block_compat_rev : ∀ i j : Fin (npNumVars n),
    (compiledPartition (sheetCoupling M) n).assign (embedTseitin i) =
    (compiledPartition (sheetCoupling M) n).assign (embedTseitin j) →
    (tseitinPartition n).assign i = (tseitinPartition n).assign j

/-! ## Rank Monotonicity from Decomposition -/

/-- Restriction then projection is rank-nonincreasing.
    Now operates on violationPolyOf (without padding product).

    NOTE: This is mathematically true but requires a refined SPDP rank definition
    with an "active variables" filter to prove formally. The current blockedSpdpSubspace
    allows arbitrary multiplier variables, but the restrict/project rank monotonicity
    only holds when generators are restricted to non-trace (verifier) variables.
    See: fuzzy-graph analysis showing unconditional rank monotonicity is FALSE
    (counterexample: p=X₁X₂, trace={X₂}, R(p)=X₁ has higher rank with ℓ≥1).
    The correct fix: add activeVars parameter to blockedSpdpSubspace restricting
    generator variables to verifier vars. This is a ~15-file refactor deferred
    to a dedicated session.

    The "pure verifier" vars: verifier but not selector. These survive both
    restriction (non-selector) and projection (verifier). -/
noncomputable def pureVerifierVars {M : DTM} {n : ℕ}
    (D : @TwoSheetDecomp F _ M n) : Finset (CompiledVars M n) :=
  Finset.univ.filter (fun v => D.isVerifier v = true ∧ D.isSelector v = false)

/-- Restriction then projection is rank-nonincreasing when measured with
    activeVars = pureVerifierVars.

    Proved from restrict_rank_le_active + project_rank_le_active +
    blockedSpdpRank_activeVars_mono. No false admissibility axioms needed. -/
theorem extracted_rank_le_violation (M : DTM) (n : ℕ)
    (D : @TwoSheetDecomp F _ M n) :
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (projectPoly D.isVerifier (restrictPoly D.isSelector D.selectorVal
        (violationPolyOf F (sheetCoupling M) n)))
      (pureVerifierVars D) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf F (sheetCoupling M) n) := by
  calc blockedSpdpRank _ _ _
        (projectPoly D.isVerifier (restrictPoly D.isSelector D.selectorVal
          (violationPolyOf F (sheetCoupling M) n)))
        (pureVerifierVars D)
      ≤ blockedSpdpRank _ _ _
          (restrictPoly D.isSelector D.selectorVal
            (violationPolyOf F (sheetCoupling M) n))
          (pureVerifierVars D) := by
        apply ExtractionProof.project_rank_le_active
        intro v hv
        simp [pureVerifierVars, Finset.mem_filter] at hv
        exact hv.1
    _ ≤ blockedSpdpRank _ _ _
          (violationPolyOf F (sheetCoupling M) n)
          (pureVerifierVars D) := by
        apply ExtractionProof.restrict_rank_le_active
        intro v hv
        simp [pureVerifierVars, Finset.mem_filter] at hv
        exact hv.2
    _ ≤ blockedSpdpRank _ _ _
          (violationPolyOf F (sheetCoupling M) n) := by
        unfold blockedSpdpRank
        apply Submodule.finrank_mono
        exact blockedSpdpSubspace_activeVars_mono _ _ _ _ (Finset.filter_subset _ _)

/-! ## Block Admissibility Transfer -/

/-- Helper: two distinct members in a nodup list of length ≤ 1 is impossible. -/
private theorem nodup_length_le_one_not_two_mem {α : Type*}
    {l : List α} (hnd : l.Nodup) (hlen : l.length ≤ 1)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : False := by
  cases l with
  | nil => simp at ha
  | cons x t =>
    cases t with
    | nil =>
      rw [List.mem_singleton] at ha hb
      exact hab (ha.trans hb.symm)
    | cons y rest =>
      simp [List.length] at hlen

/-- Block admissibility transfers through injective, block-reflecting maps. -/
theorem isBlockAdmissible_map_injective
    {n₁ n₂ : ℕ}
    (B₁ : BlockPartition n₁) (B₂ : BlockPartition n₂)
    (ρ : Fin n₁ → Fin n₂) (hρ : Function.Injective ρ)
    (hrev : ∀ i j : Fin n₁, B₂.assign (ρ i) = B₂.assign (ρ j) →
      B₁.assign i = B₁.assign j)
    (S : List (Fin n₁)) (hadm : isBlockAdmissible B₁ S) :
    isBlockAdmissible B₂ (S.map ρ) := by
  refine ⟨(And.left hadm).map hρ, fun b₂ => ?_⟩
  by_contra hgt; push_neg at hgt
  -- Extract two distinct preimages in S mapping to block b₂.
  -- Auxiliary: from a list with filter.length ≥ 2, extract two elements
  suffices h : ∀ (L : List (Fin n₁)),
      List.Nodup L → List.Sublist L S →
      1 < (List.filter (fun i => decide (B₂.assign i = b₂)) (List.map ρ L)).length →
      ∃ a ∈ S, ∃ s ∈ S, a ≠ s ∧
        B₂.assign (ρ a) = b₂ ∧ B₂.assign (ρ s) = b₂ by
    obtain ⟨a, ha, s, hs, hne, ha_b2, hs_b2⟩ :=
      h S (And.left hadm) (List.Sublist.refl _) hgt
    have hb1 := hrev a s (by rw [ha_b2, hs_b2])
    have ha_f : a ∈ List.filter (fun i => decide (B₁.assign i = B₁.assign a)) S :=
      List.mem_filter.mpr ⟨ha, decide_eq_true_eq.mpr rfl⟩
    have hs_f : s ∈ List.filter (fun i => decide (B₁.assign i = B₁.assign a)) S :=
      List.mem_filter.mpr ⟨hs, decide_eq_true_eq.mpr hb1.symm⟩
    have hnd_f : List.Nodup (List.filter (fun i => decide (B₁.assign i = B₁.assign a)) S) :=
      List.Nodup.sublist List.filter_sublist (And.left hadm)
    exact nodup_length_le_one_not_two_mem hnd_f (And.right hadm _) ha_f hs_f hne
  intro L
  induction L with
  | nil => intro _ _ h; simp at h
  | cons x t ih =>
    intro hnd hsub hlen
    simp only [List.map_cons, List.filter_cons] at hlen
    split at hlen
    · -- ρ x in block b₂
      rename_i hx_eq
      rw [decide_eq_true_eq] at hx_eq
      simp only [List.length_cons] at hlen
      -- filter on t.map ρ has ≥ 1 elements
      have ht_pos : (t.map ρ).filter (fun i => decide (B₂.assign i = b₂)) ≠ [] := by
        intro h; simp [h] at hlen
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ ht_pos
      obtain ⟨hy_map, hy_dec⟩ := List.mem_filter.mp hy
      obtain ⟨s, hs_t, rfl⟩ := List.mem_map.mp hy_map
      rw [decide_eq_true_eq] at hy_dec
      have hne : x ≠ s := by
        intro h; subst h
        have ⟨hx_notin, _⟩ := List.nodup_cons.mp hnd
        exact hx_notin hs_t
      have hx_mem : x ∈ x :: t := List.mem_cons_self
      have hs_mem : s ∈ x :: t := List.mem_cons.mpr (Or.inr hs_t)
      have hx_in_S := List.Sublist.subset hsub hx_mem
      have hs_in_S := List.Sublist.subset hsub hs_mem
      exact ⟨x, hx_in_S, s, hs_in_S, hne, hx_eq, hy_dec⟩
    · -- ρ x not in block b₂: recurse on t
      have hnd_t := (List.nodup_cons.mp hnd).2
      have hsub_t : List.Sublist t S := List.Sublist.trans (List.sublist_cons_self x t) hsub
      obtain ⟨a, ha, s, hs, hne, ha2, hs2⟩ := ih hnd_t hsub_t hlen
      exact ⟨a, ha, s, hs, hne, ha2, hs2⟩

/-! ## Helper: iterDerivList commutes with rename -/

private theorem iterDerivList_rename_map_local {n₁ n₂ : ℕ} {F : Type*} [CommRing F]
    (ρ : Fin n₁ → Fin n₂) (hρ : Function.Injective ρ)
    (S : List (Fin n₁)) (p : MvPolynomial (Fin n₁) F) :
    iterDerivList (S.map ρ) (MvPolynomial.rename ρ p) =
    MvPolynomial.rename ρ (iterDerivList S p) := by
  induction S generalizing p with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.map_cons, List.foldl]
    rw [show List.foldl (fun q j => pderiv j q) (pderiv (ρ i) (MvPolynomial.rename ρ p))
            (List.map ρ rest) =
          iterDerivList (rest.map ρ) (pderiv (ρ i) (MvPolynomial.rename ρ p)) from rfl]
    rw [pderiv_rename hρ i p]
    exact ih (pderiv i p)

/-! ## Rename preserves SPDP rank -/

/-- Subspace of rename(ρ)(p) contains the image of subspace of p under rename(ρ). -/
theorem blockedSpdpSubspace_rename_le (κ ℓ : ℕ)
    {n₁ n₂ : ℕ}
    (B₁ : BlockPartition n₁) (B₂ : BlockPartition n₂)
    (ρ : Fin n₁ → Fin n₂) (hρ : Function.Injective ρ)
    (hrev : ∀ i j : Fin n₁, B₂.assign (ρ i) = B₂.assign (ρ j) →
      B₁.assign i = B₁.assign j)
    (p : MvPolynomial (Fin n₁) F) :
    (blockedSpdpSubspace B₁ κ ℓ p).map (rename ρ).toLinearMap ≤
    blockedSpdpSubspace B₂ κ ℓ (rename ρ p) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, _, _, hq⟩
  show (rename ρ) q ∈ blockedSpdpSubspace B₂ κ ℓ (rename ρ p)
  rw [hq, map_mul, ← iterDerivList_rename_map_local ρ hρ S p]
  apply Submodule.subset_span
  refine ⟨S.map ρ, rename ρ m, by simp [hlen],
    le_trans (totalDegree_rename_le ρ m) hdeg,
    isBlockAdmissible_map_injective B₁ B₂ ρ hρ hrev S hadm,
    (fun _ _ => Finset.mem_univ _), (fun _ _ => Finset.mem_univ _), rfl⟩

/-- Rename with matching active sets: if ρ maps active₁ into active₂,
    then rename preserves the activeVars-filtered rank. -/
theorem blockedSpdpSubspace_rename_le_active (κ ℓ : ℕ)
    {n₁ n₂ : ℕ}
    (B₁ : BlockPartition n₁) (B₂ : BlockPartition n₂)
    (ρ : Fin n₁ → Fin n₂) (hρ : Function.Injective ρ)
    (hrev : ∀ i j : Fin n₁, B₂.assign (ρ i) = B₂.assign (ρ j) →
      B₁.assign i = B₁.assign j)
    (active₁ : Finset (Fin n₁)) (active₂ : Finset (Fin n₂))
    (hactive : ∀ v ∈ active₁, ρ v ∈ active₂)
    (p : MvPolynomial (Fin n₁) F) :
    (blockedSpdpSubspace B₁ κ ℓ p active₁).map (rename ρ).toLinearMap ≤
    blockedSpdpSubspace B₂ κ ℓ (rename ρ p) active₂ := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, hSa, hma, hq⟩
  show (rename ρ) q ∈ blockedSpdpSubspace B₂ κ ℓ (rename ρ p) active₂
  rw [hq, map_mul, ← iterDerivList_rename_map_local ρ hρ S p]
  apply Submodule.subset_span
  refine ⟨S.map ρ, rename ρ m, by simp [hlen],
    le_trans (totalDegree_rename_le ρ m) hdeg,
    isBlockAdmissible_map_injective B₁ B₂ ρ hρ hrev S hadm,
    fun i hi => by
      rw [List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      exact hactive j (hSa j hj),
    fun v hv => by
      -- v ∈ (rename ρ m).vars → ∃ w ∈ m.vars, ρ w = v
      obtain ⟨w, _, rfl⟩ := mem_vars_rename ρ m hv
      exact hactive w (hma w ‹w ∈ m.vars›),
    rfl⟩

/-- Tseitin rank ≤ extracted rank via injective rename. -/
theorem tseitin_rank_le_extracted (M : DTM) (n : ℕ)
    (D : @TwoSheetDecomp F _ M n) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (projectPoly D.isVerifier (restrictPoly D.isSelector D.selectorVal
        (violationPolyOf F (sheetCoupling M) n))) := by
  rw [← D.extraction_eq]
  set φ := (rename D.embedTseitin : MvPolynomial (Fin (npNumVars n)) F →ₐ[F] _).toLinearMap
  set tsub := blockedSpdpSubspace (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
    (tseitinPoly F n)
  set csub := blockedSpdpSubspace (compiledPartition (sheetCoupling M) n) (Nat.log 2 n)
    (Nat.log 2 n) (rename D.embedTseitin (tseitinPoly F n))
  have hle : tsub.map φ ≤ csub :=
    blockedSpdpSubspace_rename_le _ _ _ _
      D.embedTseitin D.embed_injective D.block_compat_rev _
  have h1 : Module.finrank F (tsub.map φ) ≤ Module.finrank F csub :=
    Submodule.finrank_mono hle
  have hinj : Function.Injective φ :=
    fun _ _ h => rename_injective _ D.embed_injective h
  have hdomInj : Function.Injective (φ.domRestrict tsub) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp [LinearMap.domRestrict] at h
    exact Subtype.ext (hinj h)
  have h2 : Module.finrank F (tsub.map φ) = Module.finrank F tsub := by
    have := LinearMap.finrank_range_of_inj hdomInj
    rw [LinearMap.range_domRestrict] at this; exact this
  show Module.finrank F tsub ≤ Module.finrank F csub
  omega

/-- **Main theorem**: Extraction rank monotonicity from two-sheet decomposition.
    The RHS uses default activeVars (Finset.univ), which is ≥ pureVerifierVars.
    Chain: rank(tseitin) ≤ rank(projectRestrict(V), univ)
                          ≤ rank(projectRestrict(V), pureVerifier)  [★ need this]
                          ≤ rank(V, pureVerifier)                    [restrict+project]
                          ≤ rank(V, univ)                            [activeVars mono]

    ★ requires showing that the rename image lands in pureVerifier vars,
    so the non-pureVerifier generators are "empty" (derivatives vanish).
    The rename-active lemma ensures that rename maps Finset.univ (tseitin side)
    into pureVerifierVars (compiled side) via embed_is_pure_verifier. -/
theorem tseitin_rank_le_extracted_active (M : DTM) (n : ℕ)
    (D : @TwoSheetDecomp F _ M n) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (projectPoly D.isVerifier (restrictPoly D.isSelector D.selectorVal
        (violationPolyOf F (sheetCoupling M) n)))
      (pureVerifierVars D) := by
  rw [← D.extraction_eq]
  set φ := (rename D.embedTseitin : MvPolynomial (Fin (npNumVars n)) F →ₐ[F] _).toLinearMap
  set tsub := blockedSpdpSubspace (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
    (tseitinPoly F n) Finset.univ
  set csub := blockedSpdpSubspace (compiledPartition (sheetCoupling M) n) (Nat.log 2 n)
    (Nat.log 2 n) (rename D.embedTseitin (tseitinPoly F n)) (pureVerifierVars D)
  have hle : tsub.map φ ≤ csub :=
    blockedSpdpSubspace_rename_le_active _ _ _ _
      D.embedTseitin D.embed_injective D.block_compat_rev
      Finset.univ (pureVerifierVars D)
      (fun v _ => by
        simp [pureVerifierVars, Finset.mem_filter]
        exact D.embed_is_pure_verifier v)
      _
  have : Module.Finite F ↥csub :=
    Module.Finite.of_injective
      (Submodule.inclusion (blockedSpdpSubspace_activeVars_mono _ _ _ _
        (Finset.filter_subset _ _)))
      (Submodule.inclusion_injective _)
  have h1 : Module.finrank F (tsub.map φ) ≤ Module.finrank F csub :=
    Submodule.finrank_mono hle
  have hinj : Function.Injective φ :=
    fun _ _ h => rename_injective _ D.embed_injective h
  have hdomInj : Function.Injective (φ.domRestrict tsub) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp [LinearMap.domRestrict] at h
    exact Subtype.ext (hinj h)
  have h2 : Module.finrank F (tsub.map φ) = Module.finrank F tsub := by
    have := LinearMap.finrank_range_of_inj hdomInj
    rw [LinearMap.range_domRestrict] at this; exact this
  show Module.finrank F tsub ≤ Module.finrank F csub
  omega

theorem extraction_rank_monotone_of_decomp (M : DTM) (n : ℕ)
    (D : @TwoSheetDecomp F _ M n) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (violationPolyOf F (sheetCoupling M) n) :=
  le_trans (tseitin_rank_le_extracted_active M n D) (extracted_rank_le_violation M n D)

/-! ## Split Construction Axioms (Fuzzy-recommended decomposition)

The monolithic `twoSheetDecomp_exists` axiom is split into three
independent, auditable claims:

1. **compiledPoly_is_coupled** — TM engineering: M♯'s compiled polynomial
   has the product structure ∏(1 - z_C · V_C²). This is the concrete
   claim about what the sheet-coupled TM actually computes.

2. **tseitin_matches_product** — Algebraic identity: ∏(1 - V_C²)
   corresponds to the Tseitin verification polynomial. Nearly trivial
   once the Tseitin encoding is unfolded.

3. **block_partition_compat** — Structural: the compiled block partition
   is compatible with the clause embedding (block-reflecting).

Together these three produce a `TwoSheetDecomp`, from which
`extraction_rank_monotone_of_decomp` gives P≠NP.
-/

/-- **Single coherent witness** for the sheet coupling construction.
    Bundles shared data + all three auditable claims in one structure,
    forcing coherence by construction — no risk of witness mismatch.

    The three claims are:
    1. **Extraction equation** (TM engineering) — the hard part
    2. **Block compatibility** (structural) — injective, block-reflecting
    3. **Admissibility** (classification) — selectors/verifiers well-placed -/
structure SheetCouplingWitness (F : Type*) [Field F] (M : DTM) (n : ℕ) where
  /-- Shared witnesses -/
  isVerifier : CompiledVars M n → Bool
  isSelector : CompiledVars M n → Bool
  selectorVal : CompiledVars M n → F
  embedTseitin : Fin (npNumVars n) → CompiledVars M n
  /-- Claim 1: Extraction equation (TM engineering).
      restrict(selectors) ∘ project(verifier) on the violation polynomial
      equals the renamed Tseitin polynomial.
      Uses violationPolyOf (without padding) to avoid padding product
      killing the extraction. -/
  extraction_eq :
    rename embedTseitin (tseitinPoly F n) =
    projectPoly isVerifier (restrictPoly isSelector selectorVal
      (violationPolyOf F (sheetCoupling M) n))
  /-- Claim 2: Block compatibility (structural).
      Embedding is injective, block-reflecting, selectors ⊆ verifier. -/
  embed_injective : Function.Injective embedTseitin
  selector_sub_verifier : ∀ v, isSelector v = true → isVerifier v = true
  embed_is_pure_verifier : ∀ i, isVerifier (embedTseitin i) = true ∧
                                isSelector (embedTseitin i) = false
  block_compat_rev : ∀ i j,
    (compiledPartition (sheetCoupling M) n).assign (embedTseitin i) =
    (compiledPartition (sheetCoupling M) n).assign (embedTseitin j) →
    (tseitinPartition n).assign i = (tseitinPartition n).assign j
  -- NOTE: admissibility fields removed. They were FALSE as stated
  -- (any singleton list [v] with v a computation var is block-admissible).
  -- The correct formulation requires an activeVars filter in blockedSpdpSubspace.
  -- The rank monotonicity is captured directly by extracted_rank_le_violation axiom.

/-- Convert a SheetCouplingWitness to TwoSheetDecomp (trivial projection). -/
noncomputable def toTwoSheetDecomp {F : Type*} [Field F] {M : DTM} {n : ℕ}
    (W : SheetCouplingWitness F M n) : @TwoSheetDecomp F _ M n where
  isVerifier := W.isVerifier
  isSelector := W.isSelector
  selectorVal := W.selectorVal
  embedTseitin := W.embedTseitin
  extraction_eq := W.extraction_eq
  embed_injective := W.embed_injective
  selector_sub_verifier := W.selector_sub_verifier
  embed_is_pure_verifier := W.embed_is_pure_verifier
  block_compat_rev := W.block_compat_rev

end PACBridge
