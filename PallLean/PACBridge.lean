import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import PallLean.SheetCoupling
import PallLean.ExtractionPipeline
import PallLean.ExtractionProof
import PallLean.CoupledCompiler
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
  admissible_non_selector :
    ∀ (S : List (CompiledVars M n)),
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ i ∈ S, isSelector i = false
  admissible_mult_non_selector :
    ∀ (m : MvPolynomial (CompiledVars M n) F) (S : List (CompiledVars M n)),
      m.totalDegree ≤ Nat.log 2 n →
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ v ∈ m.vars, isSelector v = false
  admissible_verifier :
    ∀ (S : List (CompiledVars M n)),
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ i ∈ S, isVerifier i = true
  admissible_mult_verifier :
    ∀ (m : MvPolynomial (CompiledVars M n) F) (S : List (CompiledVars M n)),
      m.totalDegree ≤ Nat.log 2 n →
      isBlockAdmissible (compiledPartition (sheetCoupling M) n) S →
      ∀ v ∈ m.vars, isVerifier v = true
  embedTseitin : Fin (npNumVars n) → CompiledVars M n
  embed_injective : Function.Injective embedTseitin
  extraction_eq :
    rename embedTseitin (tseitinPoly F n) =
    projectPoly isVerifier (restrictPoly isSelector selectorVal
      (compiledPolyOf F (sheetCoupling M) n))
  block_compat_rev : ∀ i j : Fin (npNumVars n),
    (compiledPartition (sheetCoupling M) n).assign (embedTseitin i) =
    (compiledPartition (sheetCoupling M) n).assign (embedTseitin j) →
    (tseitinPartition n).assign i = (tseitinPartition n).assign j

/-! ## Rank Monotonicity from Decomposition -/

/-- Restriction then projection is rank-nonincreasing. -/
theorem extracted_rank_le_compiled (M : DTM) (n : ℕ)
    (D : @TwoSheetDecomp F _ M n) :
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (projectPoly D.isVerifier (restrictPoly D.isSelector D.selectorVal
        (compiledPolyOf F (sheetCoupling M) n))) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n) := by
  have h1 := ExtractionProof.restrict_rank_le
    (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
    D.isSelector D.selectorVal (compiledPolyOf F (sheetCoupling M) n)
    D.admissible_non_selector D.admissible_mult_non_selector
  have h2 := ExtractionProof.project_rank_le
    (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
    D.isVerifier
    (restrictPoly D.isSelector D.selectorVal (compiledPolyOf F (sheetCoupling M) n))
    D.admissible_verifier D.admissible_mult_verifier
  linarith

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
  intro q ⟨S, m, hlen, hdeg, hadm, hq⟩
  show (rename ρ) q ∈ blockedSpdpSubspace B₂ κ ℓ (rename ρ p)
  rw [hq, map_mul, ← CoupledCompiler.iterDerivList_rename_map ρ hρ S p]
  apply Submodule.subset_span
  refine ⟨S.map ρ, rename ρ m, by simp [hlen],
    le_trans (totalDegree_rename_le ρ m) hdeg,
    isBlockAdmissible_map_injective B₁ B₂ ρ hρ hrev S hadm, rfl⟩

/-- Tseitin rank ≤ extracted rank via injective rename. -/
theorem tseitin_rank_le_extracted (M : DTM) (n : ℕ)
    (D : @TwoSheetDecomp F _ M n) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (projectPoly D.isVerifier (restrictPoly D.isSelector D.selectorVal
        (compiledPolyOf F (sheetCoupling M) n))) := by
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

/-- **Main theorem**: Extraction rank monotonicity from two-sheet decomposition. -/
theorem extraction_rank_monotone_of_decomp (M : DTM) (n : ℕ)
    (D : @TwoSheetDecomp F _ M n) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n) (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n) :=
  le_trans (tseitin_rank_le_extracted M n D) (extracted_rank_le_compiled M n D)

/-! ## Construction Axiom -/

/-- The sheet coupling produces a two-sheet decomposition (Theorem 181). -/
axiom twoSheetDecomp_exists (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    @TwoSheetDecomp F _ M n

end PACBridge
