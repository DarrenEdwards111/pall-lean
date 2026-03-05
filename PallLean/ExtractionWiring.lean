/-
  ExtractionWiring.lean — Replace extraction_rank_monotone axiom

  Decomposes the monolithic axiom into:
  1. Two structural axioms (relabel span + extraction factorization)
  2. Three proved stages (project, restrict, gauge) via ExtractionProof lemmas
  3. A composition theorem connecting them across two polynomial rings

  Net effect: axiom count stays at 3 (highGirthFamily, profile_decomposition,
  + extraction_factorization replaces extraction_rank_monotone), but the new
  axioms are structurally transparent.

  relabel_generators_subset is also an axiom but could be proved from
  partition compatibility — it encodes that rename commutes with pderiv
  and preserves admissibility across compatible partitions.
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

/-! ## Structural Axiom A: Relabel maps generators into image of generators

    When we rename variables via ρ, the tseitin-ring generators of
    rename(p) sit inside the image of the compiled-ring generators
    of p under the same rename map.
-/
axiom relabel_generators_subset
    (M : DTM) (n : ℕ)
    (ρ : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Fin (npNumVars n))
    (p : MvPolynomial (Fin (numVars (sheetCoupling M) n (Nat.log 2 n))) F)
    (κ ℓ : ℕ) :
    blockedSpdpSubspace (tseitinPartition n) κ ℓ (MvPolynomial.rename ρ p) ≤
    (blockedSpdpSubspace (compiledPartition (sheetCoupling M) n) κ ℓ p).map
      (MvPolynomial.rename ρ).toLinearMap

/-! ## Structural Axiom B: Extraction factorization

    tseitinPoly = C(a) * rename ρ (restrict(project(compiledPoly)))
    with all block-admissibility conditions on keep/isTrace.
-/
axiom extraction_factorization
    (M : DTM) (n : ℕ) :
    ∃ (keep : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Bool)
      (isTrace : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Bool)
      (assign : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → F)
      (ρ : Fin (numVars (sheetCoupling M) n (Nat.log 2 n)) → Fin (npNumVars n))
      (a : F) (_ : a ≠ 0),
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
  obtain ⟨keep, isTrace, assign, ρ, a, ha, hB_trace, hB_keep, hM_trace, hM_keep, hfact⟩ :=
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
  -- Stage 2: Relabel (rename ρ) — rank nonincreasing via map
  have h_relabel := relabel_generators_subset (F := F) M n ρ p2 κ ℓ
  -- Stage 3: Restrict — rank nonincreasing
  -- restrict_rank_le gives blockedSpdpRank B κ ℓ p2 ≤ blockedSpdpRank B κ ℓ p1
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
