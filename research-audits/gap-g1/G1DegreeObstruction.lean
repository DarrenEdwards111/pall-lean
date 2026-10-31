import PallLean.TuringMachine
import PallLean.MultilinearSPDP
import PallLean.PiStarConcrete
import PallLean.PaperFaithfulCompilation
import PallLean.GodMoveReal
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Gap G1 (research/gap-g1): degree obstruction and the always-accept product horn

Kernel-checked facts about the P-side object of Gap G1 (paper v5 Lemmas 27/31, Thm 92/218)
and its interaction with Item 3 (God-Move extraction `T_Φ(P_{M',n}) = Q×_Φ`, Def. 6 / Lemma 7 /
Thm 223 / Lemma 123):

1. `totalDegree_aeval_le` : an algebra map sending every variable to a polynomial of degree ≤ 1
   (restriction to constants, affine relabelling, renaming, the repo's `piSubst`/`piZero`/`piPhi`)
   never increases total degree; neither does `mlProj` (`totalDegree_mlProj_le`).
2. `coupledSheet_totalDegree` : the coupled sheet `∏ (1 - z_C · g_C)` (repo `coupledSheetFromList`)
   has total degree `Σ (1 + deg g_C)` when all gadgets are nonzero, hence ≥ number of clauses.
3. `extraction_degree_obstruction` and the instances for `TuringMachine.compiledPoly` (= Y·ΣC², the
   κ-padded SoS tableau polynomial, degree ≤ κ+6) and for the paper's constant-degree SoS
   `1 - ΣC²` (degree ≤ 6): no degree-non-increasing extraction can map them onto a coupled
   sheet with more than κ+6 (resp. 6) clauses — for ANY machine.  So on the constant/low-degree
   compiled object the P-side bound (G1) is trivially true but Item 3 is impossible; a compiled
   object usable for Item 3 must have degree ≥ #clauses.
4. `alwaysAccept_product_rank_ge_NP_bound` : for the product compiler `∏(1 - C_i)`
   (`cook_levin_compilation`) the explicit 3-state always-accept machine already has
   SPDP rank ≥ C(n/3, log n) (the NP-side bound) — so G1 is false for the product encoding.
-/

namespace GapG1
open MvPolynomial

section Degree
variable {σ τ : Type*}

/-- An algebra map whose images of variables have degree ≤ 1 does not increase total degree. -/
theorem totalDegree_aeval_le (φ : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ)
    (h : ∀ i, (φ (X i)).totalDegree ≤ 1) (p : MvPolynomial σ ℚ) :
    (φ p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun s hs => ?_)
  have hC : φ (C (coeff s p)) = C (coeff s p) := by
    simpa [algebraMap_eq] using φ.commutes (coeff s p)
  rw [monomial_eq, map_mul, hC, map_finsuppProd]
  refine le_trans (totalDegree_mul _ _) ?_
  rw [totalDegree_C, zero_add]
  refine le_trans (totalDegree_finset_prod _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_totalDegree hs)
  show (φ (X i ^ s i)).totalDegree ≤ s i
  rw [map_pow]
  refine le_trans (totalDegree_pow _ _) ?_
  calc s i * (φ (X i)).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (h i)
    _ = s i := mul_one _

/-- `mlProj` (drop non-multilinear monomials) does not increase total degree. -/
theorem totalDegree_mlProj_le [DecidableEq σ] (p : MvPolynomial σ ℚ) :
    (MultilinearSPDP.mlProj p).totalDegree ≤ p.totalDegree := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  apply Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum fun _ e => e)
  have h1 : coeff s (MultilinearSPDP.mlProj p) ≠ 0 := mem_support_iff.mp hs
  apply mem_support_iff.mpr
  intro h0
  apply h1
  show (Finsupp.filter (fun α => MultilinearSPDP.Finsupp.IsMultilinear α) p) s = 0
  rw [Finsupp.filter_apply]
  split_ifs
  · exact h0
  · rfl

/-- A variable-renaming does not increase total degree (Mathlib). -/
theorem totalDegree_rename_le' (f : σ → τ) (p : MvPolynomial σ ℚ) :
    (rename f p).totalDegree ≤ p.totalDegree := totalDegree_rename_le f p

/-- The repo's restriction gauge `piSubst keep val` (keep or substitute a constant) does not increase degree. -/
theorem totalDegree_piSubst_le {N : ℕ} (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (p : MvPolynomial (Fin N) ℚ) :
    (PiStarConcrete.piSubst keep val p).totalDegree ≤ p.totalDegree := by
  unfold PiStarConcrete.piSubst
  rw [AlgHom.toLinearMap_apply]
  apply totalDegree_aeval_le
  intro i
  have := PiStarConcrete.piSubst_X keep val i
  unfold PiStarConcrete.piSubst at this
  rw [AlgHom.toLinearMap_apply] at this
  rw [this]
  split_ifs
  · simp
  · simp

/-- The paper's God-Move restriction `piPhi` (Lean form) does not increase degree. -/
theorem totalDegree_piPhi_le (σ' : PaperFaithfulCompilation.UVSplit)
    (p : PaperFaithfulCompilation.PMnPoly σ') :
    (PaperFaithfulCompilation.piPhi σ' p).totalDegree ≤ p.totalDegree := by
  unfold PaperFaithfulCompilation.piPhi PiStarConcrete.piZero
  exact totalDegree_piSubst_le _ _ p

/-- Degree-non-increasing maps: closed under composition. -/
def DegNonincr (T : MvPolynomial σ ℚ → MvPolynomial τ ℚ) : Prop :=
  ∀ p, (T p).totalDegree ≤ p.totalDegree

theorem DegNonincr.comp {υ : Type*} {T : MvPolynomial σ ℚ → MvPolynomial τ ℚ}
    {T' : MvPolynomial τ ℚ → MvPolynomial υ ℚ} (h : DegNonincr T) (h' : DegNonincr T') :
    DegNonincr (T' ∘ T) := fun p => le_trans (h' _) (h p)

/-- **Extraction degree obstruction.** A degree-non-increasing map cannot send `p` to `q`
when `deg p < deg q`. -/
theorem extraction_degree_obstruction {T : MvPolynomial σ ℚ → MvPolynomial τ ℚ}
    (hT : DegNonincr T) (p : MvPolynomial σ ℚ) (q : MvPolynomial τ ℚ)
    (h : p.totalDegree < q.totalDegree) : T p ≠ q := by
  intro hpq
  have := hT p
  rw [hpq] at this
  omega

end Degree

section CoupledSheet

/-- One coupled-sheet factor `1 - X s * g` with `g ≠ 0` has degree `1 + deg g`. -/
theorem totalDegree_one_sub_X_mul {τ : Type*} (s : τ) {g : MvPolynomial τ ℚ} (hg : g ≠ 0) :
    (1 - X s * g).totalDegree = 1 + g.totalDegree := by
  have hX : (X s : MvPolynomial τ ℚ) ≠ 0 := X_ne_zero s
  have hdeg : (X s * g).totalDegree = 1 + g.totalDegree := by
    rw [totalDegree_mul_of_isDomain hX hg, totalDegree_X]
  have hlt : (1 : MvPolynomial τ ℚ).totalDegree < (-(X s * g)).totalDegree := by
    rw [totalDegree_neg, hdeg, totalDegree_one]; omega
  rw [sub_eq_neg_add, totalDegree_add_eq_left_of_totalDegree_lt hlt, totalDegree_neg, hdeg]

theorem one_sub_X_mul_ne_zero {τ : Type*} (s : τ) {g : MvPolynomial τ ℚ} (hg : g ≠ 0) :
    (1 - X s * g) ≠ 0 := by
  intro h
  have := totalDegree_one_sub_X_mul s hg
  rw [h, totalDegree_zero] at this
  omega

/-- **Degree of the coupled sheet** `Q×_Φ = ∏ (1 - z_C · g_C)` (repo `coupledSheetFromList`). -/
theorem coupledSheet_totalDegree (σ' : PaperFaithfulCompilation.UVSplit)
    (clauses : List (Fin σ'.numU × MvPolynomial (Fin σ'.numU) ℚ))
    (h : ∀ c ∈ clauses, c.2 ≠ 0) :
    PaperFaithfulCompilation.coupledSheetFromList σ' clauses ≠ 0 ∧
    (PaperFaithfulCompilation.coupledSheetFromList σ' clauses).totalDegree =
      (clauses.map (fun c => 1 + c.2.totalDegree)).sum := by
  induction clauses with
  | nil =>
    rw [PaperFaithfulCompilation.coupledSheetFromList_nil]
    exact ⟨one_ne_zero, by simp⟩
  | cons c rest ih =>
    obtain ⟨s, g⟩ := c
    have hg : g ≠ 0 := h (s, g) (List.mem_cons_self ..)
    obtain ⟨hne, hdeg⟩ := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    rw [PaperFaithfulCompilation.coupledSheetFromList_cons]
    have hf := one_sub_X_mul_ne_zero s hg
    refine ⟨mul_ne_zero hf hne, ?_⟩
    rw [totalDegree_mul_of_isDomain hf hne, totalDegree_one_sub_X_mul s hg, hdeg]
    simp

theorem coupledSheet_totalDegree_ge_length (σ' : PaperFaithfulCompilation.UVSplit)
    (clauses : List (Fin σ'.numU × MvPolynomial (Fin σ'.numU) ℚ))
    (h : ∀ c ∈ clauses, c.2 ≠ 0) :
    clauses.length ≤ (PaperFaithfulCompilation.coupledSheetFromList σ' clauses).totalDegree := by
  rw [(coupledSheet_totalDegree σ' clauses h).2]
  clear h
  induction clauses with
  | nil => simp
  | cons c rest ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

end CoupledSheet

section CompiledTableau
open TuringMachine

/-- Degree of the κ-padded SoS tableau polynomial `TuringMachine.compiledPoly = Y · Σ C²`. -/
theorem compiledPoly_totalDegree_le (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ ℚ))
    (hc : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3) :
    (compiledPoly ℚ M n κ constraints).totalDegree ≤ κ + 6 := by
  unfold compiledPoly
  refine le_trans (totalDegree_mul _ _) ?_
  have h1 := paddingProduct_totalDegree ℚ M n κ
  have h2 := violation_deg_const ℚ M n κ constraints hc
  omega

/-- **No God-Move extraction from the padded SoS tableau.** For every machine `M`, every
degree-non-increasing extraction `T` (restriction / affine relabelling / `piPhi` / `mlProj` and
compositions), and every coupled sheet with more than `κ + 6` clauses (nonzero gadgets),
`T (compiledPoly M) ≠ Q×_Φ`. -/
theorem no_extraction_from_padded_SoS (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ ℚ))
    (hc : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3)
    (σ' : PaperFaithfulCompilation.UVSplit)
    (clauses : List (Fin σ'.numU × MvPolynomial (Fin σ'.numU) ℚ))
    (hg : ∀ c ∈ clauses, c.2 ≠ 0) (hm : κ + 6 < clauses.length)
    {T : MvPolynomial (Fin (numVars M n κ)) ℚ → MvPolynomial (Fin σ'.numU) ℚ}
    (hT : DegNonincr T) :
    T (compiledPoly ℚ M n κ constraints) ≠
      PaperFaithfulCompilation.coupledSheetFromList σ' clauses := by
  apply extraction_degree_obstruction hT
  have := compiledPoly_totalDegree_le M n κ constraints hc
  have := coupledSheet_totalDegree_ge_length σ' clauses hg
  omega

/-- Same for the paper's constant-degree SoS form `1 - Σ C²` (Thm 92 / Thm 218): more than 6
clauses already make extraction impossible. -/
theorem no_extraction_from_constant_degree_SoS (M : DTM) (n κ : ℕ)
    (constraints : List (LocalConstraint M n κ ℚ))
    (hc : ∀ c ∈ constraints, c.poly.totalDegree ≤ 3)
    (σ' : PaperFaithfulCompilation.UVSplit)
    (clauses : List (Fin σ'.numU × MvPolynomial (Fin σ'.numU) ℚ))
    (hg : ∀ c ∈ clauses, c.2 ≠ 0) (hm : 6 < clauses.length)
    {T : MvPolynomial (Fin (numVars M n κ)) ℚ → MvPolynomial (Fin σ'.numU) ℚ}
    (hT : DegNonincr T) :
    T (1 - violationPoly ℚ M n κ constraints) ≠
      PaperFaithfulCompilation.coupledSheetFromList σ' clauses := by
  apply extraction_degree_obstruction hT
  have h1 : (1 - violationPoly ℚ M n κ constraints).totalDegree ≤ 6 := by
    refine le_trans (totalDegree_sub _ _) ?_
    rw [totalDegree_one]
    have := violation_deg_const ℚ M n κ constraints hc
    omega
  have := coupledSheet_totalDegree_ge_length σ' clauses hg
  omega

end CompiledTableau

section ProductHorn
open TuringMachine PaperFaithfulSeparation MultilinearSPDP

/-- The 3-state machine that accepts on its first step (same as Phase-1 `alwaysAccept`). -/
def alwaysAccept : DTM where
  numStates := 3
  hStates := by decide
  transition := fun _ bit => (1, bit, true)
  timeBound := 1
  hTimeBound := by decide

theorem alwaysAccept_accepts_everything (n : ℕ) (hn : 1 ≤ n) (input : Fin n → Bool) :
    accepts alwaysAccept n hn input := by
  refine ⟨1, ?_, ?_⟩
  · simpa [timeSteps, alwaysAccept] using hn
  · rfl

/-- **Product horn of G1, explicit easy machine.** For the product compiler `∏ (1 - C_i)`
(`cook_levin_compilation`), the always-accept machine's compiled polynomial already has
SPDP rank (Lean measure, compiler partition, κ = ℓ = log₂ n) at least the NP-side bound
C(n/3, log₂ n). Hence the P-side bound `Γ ≤ n^200` fails for this trivial machine. -/
theorem alwaysAccept_product_rank_ge_NP_bound (n : ℕ) (hn : n ≥ 2 ^ 804) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation alwaysAccept n (by omega) (by decide)
          (by show 3 ≤ n; omega)).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (PaperFaithfulSeparation.compiledPoly
          (cook_levin_compilation alwaysAccept n (by omega) (by decide) (by show 3 ≤ n; omega))) :=
  GodMoveReal.compiled_np_lower_bound_any_dtm alwaysAccept n hn (by decide) (by show 3 ≤ n; omega)

theorem alwaysAccept_product_rank_gt_npow200 (n : ℕ) (hn : n ≥ 2 ^ 804) :
    n ^ 200 <
      mlBlockedSpdpRank
        (cook_levin_compilation alwaysAccept n (by omega) (by decide)
          (by show 3 ≤ n; omega)).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (PaperFaithfulSeparation.compiledPoly
          (cook_levin_compilation alwaysAccept n (by omega) (by decide) (by show 3 ≤ n; omega))) :=
  GodMoveReal.compiledPoly_rank_gt_npow200_at_large_n alwaysAccept n hn (by decide)
    (by show 3 ≤ n; omega)

end ProductHorn
end GapG1

#print axioms GapG1.totalDegree_aeval_le
#print axioms GapG1.totalDegree_mlProj_le
#print axioms GapG1.totalDegree_piPhi_le
#print axioms GapG1.coupledSheet_totalDegree_ge_length
#print axioms GapG1.no_extraction_from_padded_SoS
#print axioms GapG1.no_extraction_from_constant_degree_SoS
#print axioms GapG1.alwaysAccept_product_rank_ge_NP_bound
#print axioms GapG1.alwaysAccept_product_rank_gt_npow200
