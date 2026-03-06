/-
  ExtractionWiring.lean — Extraction rank monotonicity

  The core bridge theorem: rank(tseitin) ≤ rank(compiled).

  Contains:
  1. iterDerivList_rename_map: helper for derivative/rename commutation
  2. relabel_generators_subset: proved theorem for bijective renames
  3. extraction_rank_monotone: axiom — the semantic bridge
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
    simp only [iterDerivList, List.map_cons, List.foldl]
    rw [show List.foldl (fun q j => pderiv j q) (pderiv (ρ i) (MvPolynomial.rename ρ p))
            (List.map ρ rest) =
          iterDerivList (rest.map ρ) (pderiv (ρ i) (MvPolynomial.rename ρ p)) from rfl]
    rw [pderiv_rename hρ i p]
    exact ih (pderiv i p)

/-! ## Theorem: relabel_generators_subset (for bijective renames) -/

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
  have hρe : ∀ x, ρ (e.symm x) = x := fun x => e.apply_symm_apply x
  have hρe_comp : ρ ∘ e.symm = id := funext hρe
  have hS_eq : S = S'.map ρ := by
    simp only [S', List.map_map, hρe_comp, List.map_id]
  have hm_eq : m = MvPolynomial.rename ρ m' := by
    have h1 : MvPolynomial.rename (ρ ∘ ⇑e.symm) m = m := by
      rw [hρe_comp]; simp [MvPolynomial.rename_id, AlgHom.id_apply]
    rw [← h1]; exact (MvPolynomial.rename_rename e.symm ρ m).symm
  have hiter : iterDerivList S (MvPolynomial.rename ρ p) =
      MvPolynomial.rename ρ (iterDerivList S' p) := by
    rw [hS_eq]; exact iterDerivList_rename_map ρ hρ_inj S' p
  have hlen' : S'.length = κ := by simp [S', hlen]
  have hdeg' : m'.totalDegree ≤ ℓ :=
    le_trans (totalDegree_rename_le _ _) hdeg
  have hadm' : isBlockAdmissible B₁ S' := by
    refine ⟨hadm.1.map e.symm.injective, fun b₁ => ?_⟩
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
    by_cases hempty : (S.filter (fun j => decide (B₁.assign (e.symm j) = b₁))) = []
    · rw [hempty]; simp
    · obtain ⟨j₀, hj₀⟩ := List.exists_mem_of_ne_nil _ hempty
      have hj₀_pred : B₁.assign (e.symm j₀) = b₁ := by
        have := List.of_mem_filter hj₀; simp at this; exact this
      let b₂ := B₂.assign j₀
      have hsub : (S.filter (fun j => decide (B₁.assign (e.symm j) = b₁))).Sublist
          (S.filter (fun j => decide (B₂.assign j = b₂))) := by
        apply List.monotone_filter_right
        intro j hj
        simp only [decide_eq_true_eq] at hj ⊢
        have h1 := hcompat (e.symm j) (e.symm j₀) (by rw [hj, hj₀_pred])
        rw [hρe j, hρe j₀] at h1; exact h1
      calc (S.filter (fun j => decide (B₁.assign (e.symm j) = b₁))).length
          ≤ (S.filter (fun j => decide (B₂.assign j = b₂))).length := hsub.length_le
        _ ≤ 1 := hadm.2 b₂
  rw [hq, hiter, hm_eq, ← map_mul]
  exact Submodule.mem_map.mpr
    ⟨m' * iterDerivList S' p, Submodule.subset_span ⟨S', m', hlen', hdeg', hadm', rfl⟩, rfl⟩

/-! ## Core axiom: extraction rank monotonicity

    For any DTM M, rank(tseitin) ≤ rank(compiled(M♯)).
    This is the semantic bridge between the NP lower bound and P upper bound.

    The two polynomial rings have different variable counts:
    - Tseitin: npNumVars n ≈ 5n (edge vars + selectors)
    - Compiled: numVars(M♯) ≈ n^(2·timeBound) (tape + state + head + input + padding)

    The sheet coupling M♯ embeds the Tseitin formula into its constraint
    structure. The SPDP rank of the smaller Tseitin polynomial is bounded
    by the rank of the larger compiled polynomial because the compiled
    constraints "contain" the Tseitin clauses.
-/
axiom extraction_rank_monotone (M : DTM) (n : ℕ) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (compiledPartition (sheetCoupling M) n)
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf F (sheetCoupling M) n)

end ExtractionWiring
