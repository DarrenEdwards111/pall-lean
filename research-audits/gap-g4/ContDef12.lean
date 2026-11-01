import Def12Measure

/-!
# A generic Def. 12 lower bound via "keep m variables, fix the rest" substitutions

Mathlib + `Def12Measure` only. Used by `ContLink.lean` for `languageCharacteristic contLang L`.

**Theorem `def12_lower_of_subst`.** Let `E : Fin m ↪ Fin N` single out `m` "x-variables" and let `p` be
multilinear. Suppose that for every `T ⊆ [m]` with `|T| = κ` some substitution `ψ_T` that keeps the
x-variables and sends every other variable to a constant maps `p` to the monomial `x^T`. Then, under both
conventions and every block partition,
  `C(m, κ) · Σ_{j ≤ ℓ} C(m, j) ≤ Γ^{Def12}_{κ,ℓ}(p)`.

Proof. Rows `(τ, u) = (x_S, x^A)`, `|S| = κ`, `|A| ≤ ℓ`. With `P_S = ∂_{x_S} p` (multilinear):
`conv(x^A · P_S) = x^A · σ_A(P_S)` where `σ_A` sets `x_A := 0` (drop) or `:= 1` (reduce)
(`conv_monomial_setExp_mul`). `ψ_T` fixes `x^A`, commutes with `σ_A` and with `∂_{x_i}`, so
`ψ_T(row_{S,A}) = x^A · σ_A(∂_{x_S} x^T) = [S = T] · x^A`. Hence `(ψ_T)_T` maps the rows to
`Pi.single S x^A`, which are linearly independent.
-/

set_option autoImplicit false

namespace ContDef12

open MvPolynomial Def12Measure

attribute [local instance] Classical.dec

variable {N : ℕ} {F : Type*} [Field F]

/-! ### Substitutions -/

/-- Keep the variables in `R`; send every other variable `v` to the constant `β v`. -/
noncomputable def substFun (R : Finset (Fin N)) (β : Fin N → F) : Fin N → MvPolynomial (Fin N) F :=
  fun v => if v ∈ R then X v else C (β v)

/-- Set the variables in `U` to the constant `b`; keep the others. -/
noncomputable def setFun (U : Finset (Fin N)) (b : F) : Fin N → MvPolynomial (Fin N) F :=
  fun v => if v ∈ U then C b else X v

theorem pderiv_aeval_comm (f : Fin N → MvPolynomial (Fin N) F) (i : Fin N)
    (hf : ∀ v, pderiv i (f v) = aeval f (pderiv i (X v : MvPolynomial (Fin N) F))) (p : MvPolynomial (Fin N) F) :
    pderiv i (aeval f p) = aeval f (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v ih =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul, aeval_X, hf, ih]

theorem iterDerivList_aeval_comm (f : Fin N → MvPolynomial (Fin N) F) (L : List (Fin N))
    (hf : ∀ i ∈ L, ∀ v, pderiv i (f v) = aeval f (pderiv i (X v : MvPolynomial (Fin N) F))) (p : MvPolynomial (Fin N) F) :
    iterDerivList L (aeval f p) = aeval f (iterDerivList L p) := by
  induction L generalizing p with
  | nil => rfl
  | cons i L ih =>
    rw [iterDerivList_cons, iterDerivList_cons, pderiv_aeval_comm f i (hf i (List.mem_cons_self ..)),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))]

theorem substFun_hf (R : Finset (Fin N)) (β : Fin N → F) (i : Fin N) (hi : i ∈ R) (v : Fin N) :
    pderiv i (substFun R β v) = aeval (substFun R β) (pderiv i (X v : MvPolynomial (Fin N) F)) := by
  by_cases hv : v ∈ R
  · simp only [substFun, hv, if_true, pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  · have hne : v ≠ i := fun h => hv (h ▸ hi)
    simp [substFun, hv, pderiv_X, hne]

/-! ### Multilinearity -/

theorem isML_pderiv {p : MvPolynomial (Fin N) F} (hp : IsMultilinear p) (i : Fin N) :
    IsMultilinear (pderiv i p) := by
  intro s hs j
  have hc := Finsupp.mem_support_iff.mp hs
  change coeff s (pderiv i p) ≠ 0 at hc
  rw [coeff_pderiv] at hc
  have h := hp _ (Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hc)) j
  rw [Finsupp.add_apply] at h; omega

theorem isML_iterDerivList {p : MvPolynomial (Fin N) F} (hp : IsMultilinear p) (L : List (Fin N)) :
    IsMultilinear (iterDerivList L p) := by
  induction L generalizing p with
  | nil => exact hp
  | cons i L ih => rw [iterDerivList_cons]; exact ih (isML_pderiv hp i)

theorem MLSupp_C (a : F) : MLSupp (C a : MvPolynomial (Fin N) F) := by
  intro s hs
  rw [C_apply] at hs
  have := Finset.mem_singleton.mp (support_monomial_subset hs)
  subst this; intro i; simp

theorem MLSupp_C_mul (a : F) {q : MvPolynomial (Fin N) F} (h : MLSupp q) : MLSupp (C a * q) := by
  intro s hs; rw [C_mul'] at hs; exact h s (support_smul hs)

theorem MLSupp_prod_substFun (R : Finset (Fin N)) (β : Fin N → F) (s : Finset (Fin N)) :
    MLSupp (∏ v ∈ s, substFun R β v) ∧ (∏ v ∈ s, substFun R β v).vars ⊆ s := by
  induction s using Finset.induction_on with
  | empty => refine ⟨?_, by simp [vars_one]⟩; rw [Finset.prod_empty, ← C_1]; exact MLSupp_C 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : MLSupp (substFun R β a) ∧ (substFun R β a).vars ⊆ {a} := by
      unfold substFun; split_ifs
      · exact ⟨MLSupp_X a, by rw [vars_X]⟩
      · exact ⟨MLSupp_C _, by rw [vars_C]; exact Finset.empty_subset _⟩
    refine ⟨MLSupp_mul h1.1 ih.1 ?_, (vars_mul _ _).trans ?_⟩
    · refine Finset.disjoint_left.mpr (fun v hv1 hv2 => ha ?_)
      have := Finset.mem_singleton.mp (h1.2 hv1); subst this; exact ih.2 hv2
    · intro v hv; rcases Finset.mem_union.mp hv with h | h
      · rw [Finset.mem_singleton.mp (h1.2 h)]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (ih.2 h)

theorem aeval_monomial_ML (f : Fin N → MvPolynomial (Fin N) F) (d : Fin N →₀ ℕ)
    (hd : Finsupp.IsMultilinear d) (a : F) :
    aeval f (monomial d a) = C a * ∏ v ∈ d.support, f v := by
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  have : d v = 1 := by have := hd v; have := Finsupp.mem_support_iff.mp hv; omega
  rw [this, pow_one]

/-- Substituting constants for some variables preserves multilinearity. -/
theorem isML_aeval_substFun (R : Finset (Fin N)) (β : Fin N → F) {p : MvPolynomial (Fin N) F}
    (hp : IsMultilinear p) : IsMultilinear (aeval (substFun R β) p) := by
  have hsum : MLSupp (aeval (substFun R β) p) := by
    rw [p.as_sum, map_sum]
    intro s hs
    obtain ⟨d, hd, hs'⟩ := Finset.mem_biUnion.mp (support_sum hs)
    rw [aeval_monomial_ML _ d (fun i => hp d hd i)] at hs'
    exact MLSupp_C_mul _ (MLSupp_prod_substFun R β d.support).1 s hs'
  exact fun s hs i => hsum s hs i

/-! ### Monomials of sets -/

theorem setExp_support (E : Finset (Fin N)) : (setExp E).support = E := by
  ext v; rw [Finsupp.mem_support_iff, setExp_apply]; split_ifs with h <;> simp [h]

theorem monomial_setExp_eq_prod (E : Finset (Fin N)) :
    (monomial (setExp E) (1 : F)) = ∏ v ∈ E, X v := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, setExp_support]
  apply Finset.prod_congr rfl; intro v hv; rw [setExp_apply, if_pos hv, pow_one]

theorem aeval_substFun_setExp (R : Finset (Fin N)) (β : Fin N → F) (U : Finset (Fin N)) (hU : U ⊆ R) :
    aeval (substFun R β) (monomial (setExp U) (1 : F)) = monomial (setExp U) 1 := by
  rw [aeval_monomial_ML _ _ (setExp_multilinear U), C_1, one_mul, setExp_support,
    monomial_setExp_eq_prod]
  apply Finset.prod_congr rfl; intro v hv
  rw [substFun, if_pos (hU hv)]

/-! ### The two conventions applied to `x^U · P` -/

/-- The constant that `x_i² − x_i` reduction assigns to a repeated shift variable:
`drop` kills the monomial (`0`), `reduce` keeps it (`1`). -/
def convB : Conv → F
  | .drop => 0
  | .reduce => 1

theorem dropML_monomial (s : Fin N →₀ ℕ) (a : F) :
    dropML (monomial s a) = if Finsupp.IsMultilinear s then monomial s a else 0 := by
  change Finsupp.filter _ (Finsupp.single s a) = _
  split_ifs with h
  · exact Finsupp.filter_single_of_pos _ h
  · exact Finsupp.filter_single_of_neg _ h

theorem conv_term (c : Conv) (U D : Finset (Fin N)) (a : F) :
    convML c (monomial (setExp U) 1 * monomial (setExp D) a) =
      monomial (setExp U) 1 * aeval (setFun U (convB c)) (monomial (setExp D) a) := by
  rw [aeval_monomial_ML _ _ (setExp_multilinear D), setExp_support, monomial_mul, one_mul]
  have hprod : ∏ v ∈ D, setFun U (convB c) v =
      C ((convB c : F) ^ (D.filter (· ∈ U)).card) * monomial (setExp (D.filter (· ∉ U))) 1 := by
    unfold setFun
    rw [Finset.prod_ite, Finset.prod_const, monomial_setExp_eq_prod, map_pow]
  rw [hprod, ← mul_assoc (C a), ← C_mul, C_mul_monomial, monomial_mul, one_mul, mul_one]
  cases c with
  | drop =>
    change dropML _ = _
    rw [dropML_monomial]
    by_cases hdis : Disjoint U D
    · have hf : D.filter (· ∈ U) = ∅ := by
        ext v; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hv hu; exact Finset.disjoint_left.mp hdis hu hv
      have hf2 : D.filter (· ∉ U) = D := by
        ext v; simp only [Finset.mem_filter, and_iff_left_iff_imp]
        intro hv hu; exact Finset.disjoint_left.mp hdis hu hv
      have hml : Finsupp.IsMultilinear (setExp U + setExp D) := by
        intro v; rw [Finsupp.add_apply, setExp_apply, setExp_apply]
        split_ifs with h1 h2
        · exact absurd h2 (Finset.disjoint_left.mp hdis h1)
        all_goals omega
      rw [if_pos hml, hf, hf2, Finset.card_empty, pow_zero, mul_one]
    · obtain ⟨v, hvU, hvD⟩ := Finset.not_disjoint_iff.mp hdis
      have hml : ¬ Finsupp.IsMultilinear (setExp U + setExp D) := by
        intro h; have := h v
        rw [Finsupp.add_apply, setExp_apply, setExp_apply, if_pos hvU, if_pos hvD] at this; omega
      have hpos : (D.filter (· ∈ U)).card ≠ 0 := by
        rw [Finset.card_ne_zero]; exact ⟨v, Finset.mem_filter.mpr ⟨hvD, hvU⟩⟩
      rw [if_neg hml, show (convB Conv.drop : F) = 0 from rfl, zero_pow hpos, mul_zero, monomial_zero]
  | reduce =>
    change Finsupp.mapDomain redExp (Finsupp.single _ a) = _
    rw [Finsupp.mapDomain_single, show (convB Conv.reduce : F) = 1 from rfl, one_pow, mul_one]
    have : redExp (setExp U + setExp D) = setExp U + setExp (D.filter (· ∉ U)) := by
      ext v
      simp only [redExp, Finsupp.mapRange_apply, Finsupp.add_apply, setExp_apply, Finset.mem_filter]
      by_cases h1 : v ∈ U <;> by_cases h2 : v ∈ D <;> simp [h1, h2]
    rw [this]; rfl

/-- **Both conventions on a shifted multilinear polynomial:** `conv(x^U · P) = x^U · σ_U(P)`, where
`σ_U` sets the variables of `U` to `0` (drop) or `1` (reduce). -/
theorem conv_monomial_setExp_mul (c : Conv) (U : Finset (Fin N)) {P : MvPolynomial (Fin N) F}
    (hP : MLSupp P) :
    convML c (monomial (setExp U) 1 * P) = monomial (setExp U) 1 * aeval (setFun U (convB c)) P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdml : Finsupp.IsMultilinear d := hP d hd
  generalize coeff d P = a
  have e := eq_setExp_support hdml
  rw [e]
  exact conv_term c U d.support a

theorem subst_set_comm (R U : Finset (Fin N)) (β : Fin N → F) (b : F) (hU : U ⊆ R)
    (q : MvPolynomial (Fin N) F) :
    aeval (substFun R β) (aeval (setFun U b) q) = aeval (setFun U b) (aeval (substFun R β) q) := by
  have h : (aeval (substFun R β)).comp (aeval (setFun U b)) =
      (aeval (setFun U b)).comp (aeval (substFun R β)) := by
    rw [comp_aeval, comp_aeval]
    congr 1; funext v
    by_cases hv : v ∈ U
    · simp [setFun, substFun, hv, hU hv]
    · by_cases hr : v ∈ R <;> simp [setFun, substFun, hv, hr]
  exact congrArg (fun φ => φ q) h

/-! ### Derivative lists of sets -/

noncomputable def sList (s : Finset (Fin N)) : List (Fin N) := (Finsupp.toMultiset (setExp s)).toList

theorem sList_coe (s : Finset (Fin N)) : ((sList s : List (Fin N)) : Multiset (Fin N)) = s.val := by
  rw [sList, Multiset.coe_toList, setExp, Multiset.toFinsupp_toMultiset]

theorem sList_nodup (s : Finset (Fin N)) : (sList s).Nodup :=
  Multiset.coe_nodup.mp (by rw [sList_coe]; exact s.nodup)

theorem mem_sList (s : Finset (Fin N)) (v : Fin N) : v ∈ sList s ↔ v ∈ s := by
  rw [← Multiset.mem_coe, sList_coe]; rfl

theorem setExp_eq_ofList (s : Finset (Fin N)) :
    setExp s = Multiset.toFinsupp ((sList s : List (Fin N)) : Multiset (Fin N)) := by
  rw [sList_coe]; rfl

theorem iterDerivList_setExp (s t : Finset (Fin N)) (hcard : t.card = s.card) :
    iterDerivList (sList s) (monomial (setExp t) (1 : F)) = if t = s then 1 else 0 := by
  split_ifs with h
  · subst h
    have := iterDerivList_monomial_nodup (F := F) (sList t) (sList_nodup t) 0 (fun _ _ => rfl) 1
    rw [add_zero, ← setExp_eq_ofList] at this
    rw [this]; rfl
  · have hns : ¬ s ⊆ t := fun hs => h (Finset.eq_of_subset_of_card_le hs (by omega)).symm
    obtain ⟨i, his, hit⟩ := Finset.not_subset.mp hns
    have hmem : i ∈ sList s := (mem_sList s i).mpr his
    rw [iterDerivList_perm (List.perm_cons_erase hmem), iterDerivList_cons, pderiv_monomial,
      setExp_apply, if_neg hit, Nat.cast_zero, mul_zero, monomial_zero, iterDerivList_zero]

/-! ### The generic lower bound -/

/-- **Generic Def. 12 lower bound (both conventions, every partition).** If for each `κ`-set `T` of
x-variables (`E : Fin m ↪ Fin N`) a substitution keeping the x-variables and fixing all other
variables to constants maps the multilinear `p` to `x^T`, then
`C(m,κ) · Σ_{j≤ℓ} C(m,j) ≤ Γ^{Def12}_{κ,ℓ}(p)`. -/
theorem def12_lower_of_subst (c : Conv) (B : BlockPartition N) (κ ℓ m : ℕ) (E : Fin m ↪ Fin N)
    (hκ : κ ≤ m) (p : MvPolynomial (Fin N) F) (hp : IsMultilinear p)
    (β : Finset (Fin m) → Fin N → F)
    (hsub : ∀ T : Finset (Fin m), T.card = κ →
      aeval (substFun (Finset.univ.map E) (β T)) p = monomial (setExp (T.map E)) 1) :
    m.choose κ * ∑ j ∈ Finset.range (ℓ + 1), m.choose j ≤ def12Rank c B κ ℓ p := by
  set R := Finset.univ.map E with hRdef
  have hR : ∀ A : Finset (Fin m), A.map E ⊆ R := fun A v hv => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hv; exact Finset.mem_map_of_mem _ (Finset.mem_univ a)
  have hder : ∀ S T : Finset (Fin m), S.card = κ → T.card = κ →
      aeval (substFun R (β T)) (pderivMulti (setExp (S.map E)) p) = if S = T then 1 else 0 := by
    intro S T hS hT
    change aeval _ (iterDerivList (sList (S.map E)) p) = _
    rw [← iterDerivList_aeval_comm _ _
        (fun i hi v => substFun_hf R (β T) i (hR S ((mem_sList _ _).mp hi)) v), hsub T hT,
      iterDerivList_setExp _ _ (by rw [Finset.card_map, Finset.card_map, hS, hT])]
    by_cases h : S = T
    · subst h; simp
    · rw [if_neg (fun h' => h (Finset.map_injective E h').symm), if_neg h]
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset (Fin m), S0.card = κ :=
    (Finset.exists_subset_card_eq (s := Finset.univ) (by simpa using hκ)).imp fun _ h => h.2
  have hguard : ¬ p.totalDegree + ℓ < κ := by
    intro hlt
    have h0 := iterDerivList_eq_zero_of_lt (sList (S0.map E)) p (by
      rw [sList, length_toList_toMultiset, setExp_weight, Finset.card_map, hS0]; omega)
    have h1 := hder S0 S0 hS0 hS0
    change aeval _ (iterDerivList (sList (S0.map E)) p) = _ at h1
    rw [h0, map_zero, if_pos rfl] at h1
    exact zero_ne_one h1
  unfold def12Rank
  rw [if_neg hguard]
  let η := {S : Finset (Fin m) // S.card = κ}
  let ι : η → Type := fun _ => {A : Finset (Fin m) // A.card ≤ ℓ}
  let row : (Σ S : η, ι S) → MvPolynomial (Fin N) F := fun a =>
    convML c (monomial (setExp (a.2.1.map E)) 1 * pderivMulti (setExp (a.1.1.map E)) p)
  let Ψ : MvPolynomial (Fin N) F →ₗ[F] (η → MvPolynomial (Fin N) F) :=
    LinearMap.pi (fun T : η => (aeval (substFun R (β T.1))).toLinearMap)
  have hxli : ∀ S : η, LinearIndependent F
      (fun A : ι S => (monomial (setExp (A.1.map E)) (1 : F))) := by
    intro S
    have := (MvPolynomial.basisMonomials (Fin N) F).linearIndependent.comp
      (fun A : ι S => setExp (A.1.map E))
      (fun a b hab => Subtype.ext (Finset.map_injective E (setExp_injective hab)))
    convert this using 1
  have hP : ∀ S : Finset (Fin m), MLSupp (pderivMulti (setExp (S.map E)) p) :=
    fun S s hs i => isML_iterDerivList hp _ s hs i
  have hli : LinearIndependent F row := by
    apply LinearIndependent.of_comp Ψ
    have hc : Ψ ∘ row = fun a => Pi.single (M := fun _ : η => MvPolynomial (Fin N) F) a.1 (monomial (setExp (a.2.1.map E)) (1 : F)) := by
      funext a; funext T
      simp only [Function.comp_apply, Ψ, row, LinearMap.pi_apply, AlgHom.toLinearMap_apply]
      rw [conv_monomial_setExp_mul c _ (hP _), map_mul, aeval_substFun_setExp _ _ _ (hR _),
        subst_set_comm _ _ _ _ (hR _), hder a.1.1 T.1 a.1.2 T.2, Pi.single_apply]
      by_cases h : a.1 = T
      · subst h; simp
      · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg (Ne.symm h), map_zero, mul_zero]
    rw [hc]
    exact Pi.linearIndependent_single (fun S (A : ι S) => monomial (setExp (A.1.map E)) (1 : F)) hxli
  have hsub' : Submodule.span F (Set.range row) ≤ def12Span c B κ ℓ p := by
    apply Submodule.span_le.mpr
    rintro q ⟨⟨S, A⟩, rfl⟩
    apply Submodule.subset_span
    have hτ : weight (setExp (S.1.map E)) = κ := by rw [setExp_weight, Finset.card_map, S.2]
    have hu : weight (setExp (A.1.map E)) ≤ ℓ := by rw [setExp_weight, Finset.card_map]; exact A.2
    exact ⟨_, _, hτ, blockCondition_vacuous B _ hτ, hu, (row_colRestrict_eq c _ _ _ hτ hu).symm⟩
  have h1 := Submodule.finrank_mono hsub'
  rw [finrank_span_eq_card hli] at h1
  refine le_trans (le_of_eq ?_) h1
  have e1 : Fintype.card {A : Finset (Fin m) // A.card ≤ ℓ} =
      ∑ j ∈ Finset.range (ℓ + 1), m.choose j := by
    rw [Fintype.card_subtype, card_small_finsets]
  have e2 : Fintype.card η = m.choose κ := by
    change Fintype.card {S : Finset (Fin m) // S.card = κ} = _
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [Fintype.card_sigma]
  change _ = ∑ _S : η, Fintype.card {A : Finset (Fin m) // A.card ≤ ℓ}
  rw [Finset.sum_const, Finset.card_univ, e1, e2, smul_eq_mul]

end ContDef12

#print axioms ContDef12.pderiv_aeval_comm
#print axioms ContDef12.iterDerivList_aeval_comm
#print axioms ContDef12.isML_iterDerivList
#print axioms ContDef12.isML_aeval_substFun
#print axioms ContDef12.aeval_substFun_setExp
#print axioms ContDef12.conv_term
#print axioms ContDef12.conv_monomial_setExp_mul
#print axioms ContDef12.subst_set_comm
#print axioms ContDef12.iterDerivList_setExp
#print axioms ContDef12.def12_lower_of_subst
set_option pp.fullNames true in
#check @ContDef12.def12_lower_of_subst
set_option pp.fullNames true in
#check @ContDef12.conv_monomial_setExp_mul
