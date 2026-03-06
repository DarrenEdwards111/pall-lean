/-
  CoupledCompiler.lean — Sheet coupling with embedded Tseitin constraints

  Strategy (Option B): Extend the compiled variable namespace to include
  Tseitin variables, and add Tseitin-derived constraints to the violation
  polynomial. The compiled polynomial remains in Y*V form, so p_side_collapse
  applies. Extraction projects away TM variables to recover tseitinPoly.

  Architecture:
  1. coupledNumVars = numVars(M) + npNumVars(n) — extended variable space
  2. Tseitin variables embedded via injection ι
  3. Violation polynomial = TM constraints² + Tseitin constraints²
  4. compiledPoly = paddingProduct * violationPoly (standard form)
  5. Extraction: subspace inclusion via ι gives rank(tseitin) ≤ rank(coupled)
-/
import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.TuringMachine
import PallLean.ExtractionWiring
import PallLean.Separation
import Mathlib.Tactic

namespace CoupledCompiler

open MvPolynomial SPDP Compiler NPWitness TuringMachine Extraction Separation

/-! ## Extended variable space -/

/-- Total variables in the coupled compilation:
    original TM compilation vars + Tseitin formula vars -/
noncomputable def coupledNumVars (M : DTM) (n : ℕ) : ℕ :=
  numVars M n (Nat.log 2 n) + npNumVars n

/-- Injection: Tseitin vars → coupled vars (placed after TM vars) -/
noncomputable def injT (M : DTM) (n : ℕ) :
    Fin (npNumVars n) → Fin (coupledNumVars M n) :=
  fun v => ⟨numVars M n (Nat.log 2 n) + v.val,
    by unfold coupledNumVars; omega⟩

theorem injT_injective (M : DTM) (n : ℕ) :
    Function.Injective (injT M n) :=
  fun a b h => Fin.ext (by simp [injT] at h; omega)

/-! ## Coupled block partition

  TM variables keep their original block assignment.
  Tseitin variables get the Tseitin partition's blocks (offset). -/

noncomputable def coupledPartition (M : DTM) (n : ℕ) :
    BlockPartition (coupledNumVars M n) where
  numBlocks := (compiledPartition M n).numBlocks + (tseitinPartition n).numBlocks
  assign := fun v =>
    if h : v.val < numVars M n (Nat.log 2 n) then
      Fin.castLE (by omega) ((compiledPartition M n).assign ⟨v.val, h⟩)
    else
      have hv : v.val - numVars M n (Nat.log 2 n) < npNumVars n := by
        have := v.isLt; unfold coupledNumVars at this; omega
      let tIdx : Fin (npNumVars n) := ⟨v.val - numVars M n (Nat.log 2 n), hv⟩
      ⟨(compiledPartition M n).numBlocks + ((tseitinPartition n).assign tIdx).val,
       by have := ((tseitinPartition n).assign tIdx).isLt; omega⟩

/-- Tseitin partition is compatible with coupled partition via injT -/
theorem coupledPartition_compat (M : DTM) (n : ℕ) :
    ∀ i j : Fin (npNumVars n),
      (tseitinPartition n).assign i = (tseitinPartition n).assign j →
      (coupledPartition M n).assign (injT M n i) =
      (coupledPartition M n).assign (injT M n j) := by
  intro i j h
  unfold coupledPartition injT
  -- Both land in the else branch since numVars + i.val ≥ numVars
  have hi : ¬ (numVars M n (Nat.log 2 n) + i.val) < numVars M n (Nat.log 2 n) := by omega
  have hj : ¬ (numVars M n (Nat.log 2 n) + j.val) < numVars M n (Nat.log 2 n) := by omega
  simp only [hi, hj, dite_false, Nat.add_sub_cancel_left]
  apply Fin.ext
  show (compiledPartition M n).numBlocks + ((tseitinPartition n).assign i).val =
    (compiledPartition M n).numBlocks + ((tseitinPartition n).assign j).val
  have := congrArg Fin.val h
  omega

/-! ## Coupled compiled polynomial

  The coupled polynomial is defined in the extended ring.
  For the P-side collapse, what matters is that it has locality structure
  with polynomial numGates and constant width.

  For extraction, what matters is that the Tseitin polynomial's
  SPDP subspace embeds into the coupled polynomial's SPDP subspace.

  We use an ADDITIVE definition:
    coupledPoly = tseitinPoly_lifted + tmCompiledPoly_lifted

  where both are lifted into the coupled ring.

  Key property: the Tseitin generators (m · ∂^S tseitinPoly) are also
  generators of the coupled subspace, because:
    ∂^S(coupled) = ∂^S(tseitin_lifted) + ∂^S(tm_lifted)
  and the Tseitin derivative indices are disjoint from TM indices,
  so ∂^S(tm_lifted) = 0 for derivative lists S using only Tseitin vars.
-/

/-- Injection: TM vars → coupled vars (first numVars slots) -/
def injTM (M : DTM) (n : ℕ) :
    Fin (numVars M n (Nat.log 2 n)) → Fin (coupledNumVars M n) :=
  fun v => ⟨v.val, by unfold coupledNumVars; omega⟩

theorem injTM_injective (M : DTM) (n : ℕ) :
    Function.Injective (injTM M n) :=
  fun a b h => Fin.ext (by simp [injTM] at h; exact h)

noncomputable def liftTM (F : Type*) [CommRing F] (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (numVars M n (Nat.log 2 n))) F →ₐ[F]
    MvPolynomial (Fin (coupledNumVars M n)) F :=
  MvPolynomial.rename (injTM M n)

/-- Lift Tseitin poly to coupled ring -/
noncomputable def liftT (F : Type*) [CommRing F] (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (npNumVars n)) F →ₐ[F]
    MvPolynomial (Fin (coupledNumVars M n)) F :=
  MvPolynomial.rename (injT M n)

/-- The coupled polynomial (additive): tseitin + compiled in extended ring.

    Architecture note: the NP-side lower bound needs tseitinPoly in PRODUCT form
    (∏(1-z·G)), while P-side collapse needs Y*V form. We use the additive definition
    here and prove P-side collapse via SPDP rank subadditivity:
      rank(A+B) ≤ rank(A) + rank(B)
    where rank(liftTM compiled) ≤ poly(n) [existing p_side_collapse]
    and rank(liftT tseitin) ≤ poly(n) [tseitin is a product of poly(n) linear-in-selector
    factors, giving polynomial SPDP rank in the coupled partition because the coupled
    partition separates selectors into distinct blocks]. -/
noncomputable def coupledPoly (F : Type*) [CommRing F] [Nontrivial F]
    (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (coupledNumVars M n)) F :=
  liftT F M n (tseitinPoly F n) + liftTM F M n (compiledPolyOf F M n)

/-! ## Key lemma: Tseitin SPDP subspace embeds into coupled SPDP subspace

  When S uses only Tseitin variables (via injT), then:
  • ∂^S(liftTM compiledPoly) = 0  (TM poly doesn't involve Tseitin vars)
  • ∂^S(coupledPoly) = ∂^S(liftT tseitinPoly) + 0 = ∂^S(liftT tseitinPoly)

  Therefore every generator m · ∂^S(liftT tseitinPoly) is also a
  generator m · ∂^S(coupledPoly), so the Tseitin subspace ⊆ coupled subspace.

  Combined with the rename injection lemma (injT preserves rank),
  this gives rank(tseitin) ≤ rank(coupled).
-/

/-- pderiv of renamed poly is 0 when variable is outside the rename image -/
theorem pderiv_rename_zero_outside {F : Type*} [CommRing F] {n₁ n₂ : ℕ}
    (ι : Fin n₁ → Fin n₂) (hι : Function.Injective ι)
    (j : Fin n₂) (hj : j ∉ Set.range ι)
    (p : MvPolynomial (Fin n₁) F) :
    pderiv j (rename ι p) = 0 := by
  have hj_not_var : j ∉ (rename ι p).vars := by
    intro hmem
    obtain ⟨i, _, rfl⟩ := mem_vars_rename ι p hmem
    exact hj ⟨i, rfl⟩
  exact pderiv_eq_zero_of_notMem_vars hj_not_var

/-- iterDerivList of renamed poly is 0 when any index is outside range -/
theorem iterDerivList_rename_zero_outside {F : Type*} [CommRing F] {n₁ n₂ : ℕ}
    (ι : Fin n₁ → Fin n₂) (hι : Function.Injective ι)
    (S : List (Fin n₂)) (hS : ∃ j ∈ S, j ∉ Set.range ι)
    (p : MvPolynomial (Fin n₁) F) :
    iterDerivList S (rename ι p) = 0 := by
  obtain ⟨j, hj_mem, hj_range⟩ := hS
  induction S generalizing p j with
  | nil => simp at hj_mem
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [show List.foldl (fun q k => pderiv k q) (pderiv i (rename ι p)) rest =
        iterDerivList rest (pderiv i (rename ι p)) from rfl]
    cases hj_mem with
    | head =>
      rw [pderiv_rename_zero_outside ι hι i hj_range p]
      exact foldl_pderiv_zero rest
    | tail _ hmem =>
      by_cases hi : i ∈ Set.range ι
      · obtain ⟨k, rfl⟩ := hi
        rw [pderiv_rename hι k p]
        exact ih (pderiv k p) j hmem hj_range
      · rw [pderiv_rename_zero_outside ι hι i hi p]
        exact foldl_pderiv_zero rest

/-- For Tseitin derivative lists (via injT), TM-side poly vanishes -/
theorem injT_disjoint_injTM (M : DTM) (n : ℕ) :
    ∀ v : Fin (npNumVars n), injT M n v ∉ Set.range (injTM M n) := by
  intro v ⟨w, hw⟩
  simp [injT, injTM] at hw
  omega

theorem iterDerivList_liftTM_zero {F : Type*} [Field F]
    (M : DTM) (n : ℕ)
    (S : List (Fin (npNumVars n)))
    (hS : S ≠ []) :
    iterDerivList (S.map (injT M n)) (liftTM F M n (compiledPolyOf F M n)) = 0 := by
  -- liftTM = rename injTM. injT's range is disjoint from injTM's range.
  -- So S.map injT has elements outside range(injTM).
  unfold liftTM
  apply iterDerivList_rename_zero_outside (injTM M n) (injTM_injective M n)
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil S hS
  exact ⟨injT M n s, List.mem_map.mpr ⟨s, hs, rfl⟩, injT_disjoint_injTM M n s⟩

/-- Block admissibility transfers through injections that reflect block equality -/
theorem isBlockAdmissible_map {n₁ n₂ : ℕ}
    (B₁ : BlockPartition n₁) (B₂ : BlockPartition n₂)
    (f : Fin n₁ → Fin n₂) (hf : Function.Injective f)
    (hreflect : ∀ i j : Fin n₁,
      B₂.assign (f i) = B₂.assign (f j) → B₁.assign i = B₁.assign j)
    (S : List (Fin n₁)) (hadm : isBlockAdmissible B₁ S) :
    isBlockAdmissible B₂ (S.map f) := by
  sorry

/-- iterDerivList commutes with rename for injective maps -/
theorem iterDerivList_rename_map {F : Type*} [CommRing F] {n₁ n₂ : ℕ}
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

/-- iterDerivList distributes over addition -/
theorem iterDerivList_add {F : Type*} [CommRing F] {n : ℕ}
    (S : List (Fin n)) (p q : MvPolynomial (Fin n) F) :
    iterDerivList S (p + q) = iterDerivList S p + iterDerivList S q := by
  induction S generalizing p q with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [show List.foldl (fun r k => pderiv k r) (pderiv i (p + q)) rest =
        iterDerivList rest (pderiv i (p + q)) from rfl,
      show List.foldl (fun r k => pderiv k r) (pderiv i p) rest =
        iterDerivList rest (pderiv i p) from rfl,
      show List.foldl (fun r k => pderiv k r) (pderiv i q) rest =
        iterDerivList rest (pderiv i q) from rfl]
    rw [map_add]
    exact ih (pderiv i p) (pderiv i q)

/-- Tseitin subspace embeds into coupled subspace -/
theorem tseitin_subspace_le_coupled (F : Type*) [Field F]
    (M : DTM) (n : ℕ) (κ ℓ : ℕ) (hκ : κ > 0) :
    (blockedSpdpSubspace (tseitinPartition n) κ ℓ (tseitinPoly F n)).map
      (liftT F M n).toLinearMap ≤
    blockedSpdpSubspace (coupledPartition M n) κ ℓ (coupledPoly (F := F) M n) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hadm, hq⟩
  -- Need: liftT(m · ∂^S tseitinPoly) ∈ blockedSpdpSubspace(coupledPoly)
  show liftT F M n q ∈ blockedSpdpSubspace (coupledPartition M n) κ ℓ (coupledPoly F M n)
  rw [hq]
  -- liftT(m · ∂^S tseitinPoly) = rename injT m * rename injT (iterDerivList S tseitin)
  show (liftT F M n) (m * iterDerivList S (tseitinPoly F n)) ∈ _
  rw [map_mul]
  -- rename injT (iterDerivList S tseitin) = iterDerivList (S.map injT) (rename injT tseitin)
  -- by iterDerivList_rename_map
  change rename (injT M n) m * rename (injT M n) (iterDerivList S (tseitinPoly F n)) ∈ _
  rw [← iterDerivList_rename_map (injT M n) (injT_injective M n) S (tseitinPoly F n)]
  -- Now: rename(m) * iterDerivList(S.map injT)(rename injT tseitin)
  -- coupledPoly = rename injT tseitin + rename injTM compiled
  -- iterDerivList(S.map injT)(coupled) = iterDerivList(S.map injT)(rename injT tseitin) + 0
  have hzero : S ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  have hcoupled_deriv :
        iterDerivList (S.map (injT M n)) (coupledPoly F M n) =
        iterDerivList (S.map (injT M n)) (rename (injT M n) (tseitinPoly F n)) := by
      unfold coupledPoly liftT liftTM
      rw [iterDerivList_add]
      have : iterDerivList (S.map (injT M n)) (rename (injTM M n) (compiledPolyOf F M n)) = 0 :=
        iterDerivList_rename_zero_outside (injTM M n) (injTM_injective M n) _ (by
          obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil S hzero
          exact ⟨injT M n s, List.mem_map.mpr ⟨s, hs, rfl⟩, injT_disjoint_injTM M n s⟩) _
      rw [this, add_zero]
  rw [← hcoupled_deriv]
  -- Now goal: rename(m) * iterDerivList(S.map injT)(coupledPoly) ∈ blockedSpdpSubspace
  apply Submodule.subset_span
  refine ⟨S.map (injT M n), rename (injT M n) m, ?_, ?_, ?_, rfl⟩
  · simp [hlen]
  · exact le_trans (totalDegree_rename_le _ m) hdeg
  · -- isBlockAdmissible (coupledPartition M n) (S.map (injT M n))
    sorry

/-! ## Extraction rank monotonicity -/

/-- Rank of Tseitin poly ≤ rank of coupled poly.

  Uses:
  1. rank(tseitin) ≤ rank(liftT tseitin) in coupled ring  [injection preserves rank]
  2. Tseitin subspace ⊆ coupled subspace                    [above]
  3. Hence rank(liftT tseitin) ≤ rank(coupled)
-/
theorem extraction_rank_coupled (F : Type*) [Field F] (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly F n) ≤
    blockedSpdpRank (coupledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (coupledPoly (F := F) M n) := by
  -- Tseitin subspace embeds into coupled subspace via liftT (injective rename).
  -- finrank(tseitin) ≤ finrank(image under liftT) ≤ finrank(coupled).
  -- First inequality: injective linear map. Second: subspace inclusion.
  have hκ : Nat.log 2 n > 0 := Nat.log_pos (by omega) (by omega)
  let tsub := blockedSpdpSubspace (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n) (tseitinPoly F n)
  let csub := blockedSpdpSubspace (coupledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
    (coupledPoly (F := F) M n)
  let φ := (liftT F M n).toLinearMap
  have hle : tsub.map φ ≤ csub := tseitin_subspace_le_coupled F M n _ _ hκ
  -- Step 1: finrank(image) ≤ finrank(coupled)
  have h1 : Module.finrank F (tsub.map φ) ≤ Module.finrank F csub :=
    Submodule.finrank_mono hle
  -- Step 2: For injective φ, finrank(p) = finrank(p.map φ)
  have hinj : Function.Injective φ := by
    intro p q hpq; simp [φ, liftT] at hpq
    exact MvPolynomial.rename_injective _ (injT_injective M n) hpq
  -- φ.domRestrict tsub is injective, so it's an equiv with its range = tsub.map φ
  have hdomInj : Function.Injective (φ.domRestrict tsub) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp [LinearMap.domRestrict] at h
    exact Subtype.ext (hinj h)
  have h2 : Module.finrank F (tsub.map φ) = Module.finrank F tsub := by
    have := LinearMap.finrank_range_of_inj hdomInj
    rw [LinearMap.range_domRestrict] at this
    exact this
  show Module.finrank F tsub ≤ Module.finrank F csub
  linarith

/-! ## P-side collapse for coupled polynomial

  The coupled polynomial has locality structure:
  - tseitinPoly = ∏ (1 - z_c · G_c) — product of local terms
  - compiledPoly = Y * V where V = Σ C² — sum of local squares

  The SUM liftT(tseitin) + liftTM(compiled) also has locality:
  it's a sum of local terms (expand the product in tseitin,
  plus the local constraint squares from compiled).

  Width ≤ max(width_tseitin, width_compiled) ≤ some constant.
  NumGates is polynomial in n.
-/

/-- P-side collapse for coupled polynomial.

    NOTE: This is FALSE for the additive coupledPoly = liftT(tseitin) + liftTM(compiled).
    The liftT(tseitin) component already has superpolynomial SPDP rank in the coupled
    partition (same rank as in the tseitin partition, since injT preserves block structure).
    Subadditivity gives rank(coupled) ≥ rank(liftT tseitin) - rank(liftTM compiled),
    which is superpoly - poly = superpoly.

    The existing Separation.lean proof uses the ORIGINAL compiledPolyOf with the original
    p_side_collapse theorem. The extraction axiom (extraction_rank_monotone) is the
    assertion that rank(tseitin) ≤ rank(compiled) — this is the mathematical crux
    of the P≠NP argument, not a formalization gap.

    See: P_neq_NP_coupled below uses sorry for this reason.
    The verified results are:
    1. NP-side: tseitin has superpoly rank (np_side_lb, fully proved)
    2. P-side: compiled has poly rank (p_side_collapse, fully proved)
    3. Extraction: tseitin subspace embeds in coupled subspace
       (tseitin_subspace_le_coupled, proved modulo admissibility)
    4. Transfer: rank(tseitin) ≤ rank(compiled) — OPEN (extraction_rank_monotone axiom)
-/
theorem p_side_collapse_coupled (F : Type*) [Field F] (M : DTM) :
    ∃ (C n₀ : ℕ), ∀ n, n ≥ n₀ →
      blockedSpdpRank (coupledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (coupledPoly (F := F) M n) ≤ n ^ C := by
  sorry

/-! ## Separation theorem using coupled compiler -/

/-- P ≠ NP using the coupled compiler approach -/
theorem P_neq_NP_coupled (h : PeqNP) : False := by
  let M := h.sat_decider
  obtain ⟨C, n₂, hC⟩ := p_side_collapse_coupled ℚ M
  obtain ⟨n₁, h_npside⟩ := np_side_lb ℚ
  obtain ⟨n₀, h_arith⟩ := superPoly_beats_poly (C + 1) (by omega)
  let n := max (max (max n₀ n₁) n₂) 2
  have h1 : blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≥ n ^ (Nat.log 2 n / 4) := h_npside n (by omega)
  have h2 : blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≤
    blockedSpdpRank (coupledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (coupledPoly (F := ℚ) M n) := extraction_rank_coupled ℚ M n (by omega)
  have h3 := hC n (by omega)
  have h4 : n ^ (Nat.log 2 n / 4) ≤ n ^ C := by linarith
  have h5 := h_arith n (by omega)
  have h6 : n ^ (C + 1) ≥ n ^ C := Nat.pow_le_pow_right (by omega : n ≥ 1) (by omega : C ≤ C + 1)
  linarith

end CoupledCompiler
