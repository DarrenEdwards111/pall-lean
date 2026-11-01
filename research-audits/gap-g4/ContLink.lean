import SubsetMachine
import ContDef12

/-!
# G4.4 item 4 follow-up: Def. 12 lower bound for the in-model easy language `contLang`, and the
in-model SAT comparison

Against codex/godmove-gap-repairs @ 21921958 (trimmed G3.7 closure; `GodMoveSATSourceCanonicity`
verbatim), `Def12Measure`, `SubsetMachine` (`contLang`, `contLang_inP`) and `ContDef12`.

Layout of `contLang` at length `L`: `m = L / 3` triples `(c_k, x_k, y_k)` at positions `3k, 3k+1, 3k+2`;
the `L mod 3 ≤ 2` tail bits can never cause a rejection.

* `cont_subst`: the substitution `c_k ↦ 1`, `y_k ↦ [k ∈ T]`, tail ↦ 0, `x_k ↦ x_k` maps
  `languageCharacteristic contLang L` to the monomial `x^T` (proved via Boolean evaluation and multilinearity).
* `cont_def12_lower`: `C(m,κ)·Σ_{j≤ℓ}C(m,j) ≤ Γ^{Def12}_{κ,ℓ}(χ_contLang at L)` for all `κ ≤ m`, `ℓ`, both
  conventions, every partition.
* `lang_def12_le_cont`: for EVERY language `lang` and `2κ, 2ℓ ≤ L/3`:
  `Γ(χ_lang at L) ≤ 8^{κ+ℓ} · Γ(χ_contLang at L)`.
* `satChar_def12_le_cont_paper`: paper parameters (`n ≥ 128`, `L = unitSourceLength (n/3)`,
  `κ = ℓ = ⌊log₂ n⌋`): `Γ(SAT_L) ≤ n^6 · Γ(χ_contLang at L)`, where `contLang` is `InP` in the branch's own
  `ComposableMachine` model (`SubsetMachine.contLang_inP`).
-/

set_option autoImplicit false

namespace ContLink

open MvPolynomial
open GodMoveBooleanInterpolation GodMoveSATSourceCanonicity
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge (wordOfFin)
open PallLean.Paper93.DeepMath.PathB.SeparationTarget (SATLang)
open SubsetMachine (contLang contSteps)
open Def12Measure (Conv BlockPartition def12Rank setExp setExp_apply setExp_multilinear)
open ContDef12 (substFun)

/-! ### Semantics of `contLang` -/

theorem getD_cons3 (x y z : Bool) (rest : List Bool) (i : ℕ) :
    (x :: y :: z :: rest).getD (i + 3) false = rest.getD i false := by
  simp

/-- `contLang w` accepts iff no triple `k` that is reached (all `c_j = 1`, `j ≤ k`) has `y_k ∧ ¬x_k`. -/
theorem contLang_true_iff (w : List Bool) :
    contLang w = true ↔ ∀ k : ℕ, (∀ j ≤ k, w.getD (3 * j) false = true) →
      ¬ (w.getD (3 * k + 2) false = true ∧ w.getD (3 * k + 1) false = false) := by
  induction w using contSteps.induct with
  | case1 =>
    simp only [contLang, true_iff]; intro k h; exact absurd (h 0 (Nat.zero_le _)) (by simp)
  | case2 tail =>
    simp only [contLang, true_iff]; intro k h; exact absurd (h 0 (Nat.zero_le _)) (by simp)
  | case3 =>
    simp only [contLang, true_iff]; intro k _ h
    have : [true].getD (3 * k + 2) false = false := List.getD_eq_default _ _ (by simp)
    rw [this] at h; exact Bool.false_ne_true h.1
  | case4 b =>
    simp only [contLang, true_iff]; intro k _ h
    have : [true, b].getD (3 * k + 2) false = false := List.getD_eq_default _ _ (by simp)
    rw [this] at h; exact Bool.false_ne_true h.1
  | case5 x y rest hxy =>
    have e : contLang (true :: x :: y :: rest) = false := by simp [contLang, hxy]
    rw [e]
    simp only [Bool.false_eq_true, false_iff, not_forall]
    refine ⟨0, fun j hj => by obtain rfl : j = 0 := by omega
                              simp, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hxy
    simpa using hxy
  | case6 x y rest hxy ih =>
    rw [show contLang (true :: x :: y :: rest) = contLang rest by simp [contLang, hxy], ih]
    constructor
    · intro H k hk
      cases k with
      | zero =>
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and] at hxy
        simpa using hxy
      | succ k =>
        rw [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 by ring, show 3 * (k + 1) + 1 = (3 * k + 1) + 3 by ring,
          getD_cons3, getD_cons3]
        exact H k (fun j hj => by
          have := hk (j + 1) (by omega)
          rwa [show 3 * (j + 1) = 3 * j + 3 by ring, getD_cons3] at this)
    · intro H k hk
      have := H (k + 1) (fun j hj => by
        cases j with
        | zero => simp
        | succ j => rw [show 3 * (j + 1) = 3 * j + 3 by ring, getD_cons3]; exact hk j (by omega))
      rwa [show 3 * (k + 1) + 2 = (3 * k + 2) + 3 by ring, show 3 * (k + 1) + 1 = (3 * k + 1) + 3 by ring,
        getD_cons3, getD_cons3] at this

theorem wordOfFin_getD {n : ℕ} (a : Fin n → Bool) (i : ℕ) :
    (wordOfFin a).getD i false = if h : i < n then a ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dif_pos h, List.getD_eq_getElem _ _ (by simpa [wordOfFin] using h)]
    simp [wordOfFin]
  · rw [dif_neg h, List.getD_eq_default _ _ (by simpa [wordOfFin] using h)]

/-! ### The substitution -/

variable (L : ℕ)

/-- x-variables `x_k = position 3k+1`, `k < L/3`. -/
def xEmb : Fin (L / 3) ↪ Fin L :=
  ⟨fun k => ⟨3 * k.val + 1, by omega⟩, fun a b h => by
    have := congrArg Fin.val h; exact Fin.ext (by simp at this; omega)⟩

/-- Values of the non-x variables: `c_k = 1` (`k < L/3`), `y_k = [k ∈ T]`, tail = 0. -/
def nonX (T : Finset (Fin (L / 3))) (v : Fin L) : Bool :=
  if v.val % 3 = 0 then decide (v.val < 3 * (L / 3))
  else decide (∃ k ∈ T, 3 * k.val + 2 = v.val)

theorem mem_xRange (v : Fin L) : v ∈ Finset.univ.map (xEmb L) ↔ v.val % 3 = 1 ∧ v.val < 3 * (L / 3) := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩; simp only [xEmb, Function.Embedding.coeFn_mk]; omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨v.val / 3, by omega⟩, Fin.ext ?_⟩
    simp only [xEmb, Function.Embedding.coeFn_mk]; omega

theorem prod_bit (T : Finset (Fin (L / 3))) (g : Fin (L / 3) → Bool) :
    ∏ k ∈ T, bit (g k) = bit (decide (∀ k ∈ T, g k = true)) := by
  by_cases h : ∀ k ∈ T, g k = true
  · rw [decide_eq_true h]
    exact Finset.prod_eq_one (fun k hk => by rw [h k hk]; rfl)
  · rw [decide_eq_false h]
    push_neg at h
    obtain ⟨k, hk, hf⟩ := h
    exact Finset.prod_eq_zero hk (by simp [bit, hf])

/-- **The key identity.** Substituting `c_k ↦ 1`, `y_k ↦ [k ∈ T]`, tail ↦ 0 (keeping the `x_k`) into the
branch characteristic of `contLang` at length `L` gives exactly the monomial `x^T`. -/
theorem cont_subst (T : Finset (Fin (L / 3))) :
    aeval (substFun (Finset.univ.map (xEmb L)) (fun v => bit (nonX L T v)))
        (languageCharacteristic contLang L) =
      monomial (setExp (T.map (xEmb L))) 1 := by
  set R := Finset.univ.map (xEmb L)
  have hχ : Def12Measure.IsMultilinear (languageCharacteristic contLang L) :=
    fun α hα i => interpolate_isMultilinear _ α hα i
  apply GodMoveCircuitNormalization.multilinear_eq_of_boolean_eval
  · intro α hα i; exact ContDef12.isML_aeval_substFun (F := ℚ) R _ hχ α hα i
  · intro α hα i
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hα
    subst hα; exact setExp_multilinear _ i
  · intro a
    let a2 : Fin L → Bool := fun v => if v ∈ R then a v else nonX L T v
    have hcomp : (aeval (booleanPoint a)).comp (aeval (substFun R (fun v => bit (nonX L T v)))) =
        aeval (booleanPoint a2) := by
      rw [comp_aeval]; congr 1; funext v
      by_cases hv : v ∈ R
      · simp [substFun, hv, a2, booleanPoint]
      · simp [substFun, hv, a2, booleanPoint]
    have hl := congrArg (fun φ => φ (languageCharacteristic contLang L)) hcomp
    simp only [AlgHom.comp_apply] at hl
    have hl' : eval (booleanPoint a) (aeval (substFun R (fun v => bit (nonX L T v)))
        (languageCharacteristic contLang L)) = eval (booleanPoint a2) (languageCharacteristic contLang L) := hl
    rw [hl', languageCharacteristic, eval_interpolate, ContDef12.monomial_setExp_eq_prod, map_prod,
      Finset.prod_map]
    simp only [eval_X]
    change _ = ∏ k ∈ T, bit (a (xEmb L k))
    rw [prod_bit]
    congr 1
    -- semantics
    have hc : ∀ j, (wordOfFin a2).getD (3 * j) false = decide (j < L / 3) := by
      intro j
      rw [wordOfFin_getD]
      split_ifs with h
      · have hnR : (⟨3 * j, h⟩ : Fin L) ∉ R := by rw [mem_xRange]; simp only; omega
        simp only [a2, if_neg hnR, nonX]
        rw [if_pos (by simp)]
        simp only [decide_eq_decide]; omega
      · simp only [Bool.false_eq, decide_eq_false_iff_not, not_lt]; omega
    have hy : ∀ k (hk : k < L / 3), (wordOfFin a2).getD (3 * k + 2) false = decide (⟨k, hk⟩ ∈ T) := by
      intro k hk
      rw [wordOfFin_getD, dif_pos (by omega)]
      have hnR : (⟨3 * k + 2, by omega⟩ : Fin L) ∉ R := by rw [mem_xRange]; simp only; omega
      simp only [a2, if_neg hnR, nonX]
      rw [if_neg (by omega)]
      simp only [decide_eq_decide]
      constructor
      · rintro ⟨k', hk', e⟩
        have : k' = ⟨k, hk⟩ := Fin.ext (by simp at e; omega)
        rwa [← this]
      · intro h; exact ⟨⟨k, hk⟩, h, rfl⟩
    have hx : ∀ k (hk : k < L / 3), (wordOfFin a2).getD (3 * k + 1) false = a (xEmb L ⟨k, hk⟩) := by
      intro k hk
      rw [wordOfFin_getD, dif_pos (by omega)]
      have hR' : (⟨3 * k + 1, by omega⟩ : Fin L) ∈ R := by rw [mem_xRange]; simp only; omega
      simp only [a2, if_pos hR']
      rfl
    apply Bool.eq_iff_iff.mpr
    rw [contLang_true_iff, decide_eq_true_iff]
    constructor
    · intro H k hk
      have := H k.val (fun j hj => by rw [hc]; simp; omega)
      rw [hy k.val k.isLt, hx k.val k.isLt] at this
      by_contra hf
      exact this ⟨by simpa using hk, by simpa using hf⟩
    · intro H k hk ⟨h1, h2⟩
      have hkm : k < L / 3 := by have := hk k le_rfl; rw [hc] at this; simpa using this
      rw [hy k hkm] at h1
      rw [hx k hkm, H ⟨k, hkm⟩ (by simpa using h1)] at h2
      exact absurd h2 (by decide)

/-! ### Def. 12 lower bound for `χ_contLang` -/

/-- **Def. 12 lower bound for the in-model easy language** (both conventions, every partition):
for `κ ≤ L/3` and every `ℓ`, `C(L/3, κ)·Σ_{j≤ℓ} C(L/3, j) ≤ Γ^{Def12}_{κ,ℓ}(languageCharacteristic contLang L)`. -/
theorem cont_def12_lower (c : Conv) (B : BlockPartition L) (κ ℓ : ℕ) (hκ : κ ≤ L / 3) :
    (L / 3).choose κ * ∑ j ∈ Finset.range (ℓ + 1), (L / 3).choose j ≤
      def12Rank c B κ ℓ (languageCharacteristic contLang L) :=
  ContDef12.def12_lower_of_subst c B κ ℓ (L / 3) (xEmb L) hκ _
    (fun α hα i => interpolate_isMultilinear _ α hα i) (fun T v => bit (nonX L T v))
    (fun T _ => cont_subst L T)

/-! ### Comparison with every language (in particular SAT) -/

theorem choose_le_eight_pow (m : ℕ) (hL : L ≤ 3 * m + 2) :
    ∀ j, 2 * j ≤ m → L.choose j ≤ 8 ^ j * m.choose j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have e1 := Nat.choose_succ_right_eq L j
    have e2 := Nat.choose_succ_right_eq m j
    have hle : L - j ≤ 8 * (m - j) := by omega
    have key : L.choose (j + 1) * (j + 1) ≤ 8 ^ (j + 1) * m.choose (j + 1) * (j + 1) := by
      rw [e1, mul_assoc, e2]
      calc L.choose j * (L - j) ≤ (8 ^ j * m.choose j) * (8 * (m - j)) := Nat.mul_le_mul h1 hle
        _ = 8 ^ (j + 1) * (m.choose j * (m - j)) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.succ_pos j)

/-- **Every language's characteristic is within `8^{κ+ℓ}` of `χ_contLang` under Def. 12** (both
conventions, every partition), for `2κ ≤ L/3`, `2ℓ ≤ L/3`. -/
theorem lang_def12_le_cont (c : Conv) (B : BlockPartition L) (κ ℓ : ℕ)
    (hκ : 2 * κ ≤ L / 3) (hℓ : 2 * ℓ ≤ L / 3) (lang : List Bool → Bool) :
    def12Rank c B κ ℓ (languageCharacteristic lang L) ≤
      8 ^ (κ + ℓ) * def12Rank c B κ ℓ (languageCharacteristic contLang L) := by
  set m := L / 3 with hm
  have hL : L ≤ 3 * m + 2 := by omega
  have hup := Def12Measure.def12Rank_le_rowCeiling c B κ ℓ (languageCharacteristic lang L)
    (fun α hα i => interpolate_isMultilinear _ α hα i)
  have hlo := cont_def12_lower L c B κ ℓ (by omega)
  set A := m.choose κ * ∑ j ∈ Finset.range (ℓ + 1), m.choose j
  set G := def12Rank c B κ ℓ (languageCharacteristic contLang L)
  have hA : 0 < A := by
    have hs : 1 ≤ ∑ j ∈ Finset.range (ℓ + 1), m.choose j := by
      have := Finset.single_le_sum (f := fun j => m.choose j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.succ_pos ℓ))
      simpa using this
    exact Nat.mul_pos (Nat.choose_pos (by omega)) hs
  have hsum : ∑ j ∈ Finset.range (ℓ + 1), L.choose j ≤ 8 ^ ℓ * ∑ j ∈ Finset.range (ℓ + 1), m.choose j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ ℓ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (choose_le_eight_pow L m hL j (by omega)).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hj'))
  have hB : L.choose κ * ∑ j ∈ Finset.range (ℓ + 1), L.choose j ≤ 8 ^ (κ + ℓ) * A := by
    calc _ ≤ (8 ^ κ * m.choose κ) * (8 ^ ℓ * ∑ j ∈ Finset.range (ℓ + 1), m.choose j) :=
          Nat.mul_le_mul (choose_le_eight_pow L m hL κ hκ) hsum
      _ = 8 ^ (κ + ℓ) * A := by simp only [A]; ring
  have h2 : def12Rank c B κ ℓ (languageCharacteristic lang L) * A ≤ 8 ^ (κ + ℓ) * G * A := by
    calc def12Rank c B κ ℓ (languageCharacteristic lang L) * A
        ≤ (L.choose κ * ∑ j ∈ Finset.range (ℓ + 1), L.choose j) * G := Nat.mul_le_mul hup hlo
      _ ≤ (8 ^ (κ + ℓ) * A) * G := Nat.mul_le_mul_right _ hB
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h2 hA

theorem eighteen_mul_le_two_pow (k : ℕ) (hk : 7 ≤ k) : 18 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 18 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    rw [pow_succ]; omega

theorem eighteen_log_le (n : ℕ) (hn : 128 ≤ n) : 18 * Nat.log 2 n ≤ n := by
  have hp : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h7 : 7 ≤ Nat.log 2 n := by
    exact (Nat.le_log_iff_pow_le (b := 2) (by norm_num) (by omega : n ≠ 0)).mpr (show 2 ^ 7 ≤ n by omega)
  exact (eighteen_mul_le_two_pow _ h7).trans hp

theorem eight_pow_log_le (n : ℕ) (hn : 1 ≤ n) : 8 ^ (Nat.log 2 n + Nat.log 2 n) ≤ n ^ 6 := by
  have hp : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h8 : (8 : ℕ) ^ (Nat.log 2 n + Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ 6 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
  rw [h8]; exact Nat.pow_le_pow_left hp 6

/-- **In-model corollary at the paper parameters** (`n ≥ 128`, which contains the paper window
`n ≥ 2^804`; `L = unitSourceLength (n/3)`; `κ = ℓ = ⌊log₂ n⌋`; every partition; both conventions):
`Γ^{Def12}(SAT_L) ≤ n^6 · Γ^{Def12}(χ_contLang at L)`, and `contLang` is in the branch's `InP`. -/
theorem satChar_def12_le_cont_paper (c : Conv) (n : ℕ) (hn : 128 ≤ n)
    (B : BlockPartition (unitSourceLength (n / 3))) :
    def12Rank c B (Nat.log 2 n) (Nat.log 2 n) (languageCharacteristic SATLang (unitSourceLength (n / 3))) ≤
      n ^ 6 * def12Rank c B (Nat.log 2 n) (Nat.log 2 n)
        (languageCharacteristic contLang (unitSourceLength (n / 3))) ∧
    PallLean.Paper93.DeepMath.PathB.ComposableMachine.InP contLang := by
  refine ⟨?_, SubsetMachine.contLang_inP⟩
  have hL : n / 3 ≤ unitSourceLength (n / 3) := n_le_unitSourceLength (n / 3)
  have hlog := eighteen_log_le n hn
  have hk : 2 * Nat.log 2 n ≤ unitSourceLength (n / 3) / 3 := by omega
  exact (lang_def12_le_cont _ c B _ _ hk hk SATLang).trans
    (Nat.mul_le_mul_right _ (eight_pow_log_le n (by omega)))

end ContLink

#print axioms ContLink.contLang_true_iff
#print axioms ContLink.wordOfFin_getD
#print axioms ContLink.cont_subst
#print axioms ContLink.cont_def12_lower
#print axioms ContLink.choose_le_eight_pow
#print axioms ContLink.lang_def12_le_cont
#print axioms ContLink.satChar_def12_le_cont_paper
set_option pp.fullNames true in
#check @ContLink.cont_subst
set_option pp.fullNames true in
#check @ContLink.cont_def12_lower
set_option pp.fullNames true in
#check @ContLink.lang_def12_le_cont
set_option pp.fullNames true in
#check @ContLink.satChar_def12_le_cont_paper
