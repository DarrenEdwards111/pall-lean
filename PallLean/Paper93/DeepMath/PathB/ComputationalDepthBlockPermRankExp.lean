import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBlockPermRankLB

/-!
# Exponential A3 rank lower bound: `spdpRank κ 0 (Permₖ) ≥ C(k,κ)²`

Upgrades the `κ=1` bound `k²` (`ComputationalDepthBlockPermRankLB.lean`) to the full exponential order-`κ` bound.
The permanent's order-`κ` shifted partial derivatives, taken along a partial permutation matching a `κ`-row-set `R`
to a `κ`-col-set `C`, are the **complementary sub-permanents** on `(Rᶜ, Cᶜ)`.  There are `C(k,κ)²` choices of `(R,C)`,
and the resulting derivatives have pairwise-disjoint monomial supports (row-set `Rᶜ`, col-set `Cᶜ`), hence are linearly
independent:

  `spdpRank_renamePerm_choose_ge` — `spdpRank κ 0 (rename ψ Permₖ) ≥ C(k,κ)²` for any injective `ψ`.
  `spdpRank_subPermPoly_flat_choose_ge` — the uniform-over-the-block-family form: `≥ C(k,κ)²` for every embedding `e`.

At `κ = k/2`, `C(k,κ)² ≈ 4^k/k` — **exponential**.  As with the `κ=1` case this is the *easy* side of SPDP (a large
lower bound on a *hard* polynomial's rank); the separation needs the matching *upper* bound (small circuits ⟹ small
rank), the barriered wall.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial Finset

variable {k : ℕ} {F : Type*} [Field F]

/-! ### Iterated partial derivative over the product variable index -/

/-- Iterated partial derivative over an arbitrary variable type (foldl of `pderiv`). -/
noncomputable def iterPD {σ : Type*} (L : List σ) (p : MvPolynomial σ F) : MvPolynomial σ F :=
  L.foldl (fun q c => pderiv c q) p

theorem iterPD_cons {σ : Type*} (c : σ) (L : List σ) (p : MvPolynomial σ F) :
    iterPD (c :: L) p = iterPD L (pderiv c p) := rfl

theorem iterPD_zero {σ : Type*} (L : List σ) : iterPD L (0 : MvPolynomial σ F) = 0 := by
  induction L with
  | nil => rfl
  | cons c L' ih => rw [iterPD_cons, map_zero, ih]

theorem iterPD_add {σ : Type*} (L : List σ) (a b : MvPolynomial σ F) :
    iterPD L (a + b) = iterPD L a + iterPD L b := by
  induction L generalizing a b with
  | nil => rfl
  | cons c L' ih => rw [iterPD_cons, iterPD_cons, iterPD_cons, map_add, ih]

theorem iterPD_sum {σ ι : Type*} (L : List σ) (s : Finset ι) (f : ι → MvPolynomial σ F) :
    iterPD L (∑ x ∈ s, f x) = ∑ x ∈ s, iterPD L (f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp [iterPD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iterPD_add, ih]

/-- Iterated derivative under an injective rename transfers: `iterDerivList (L.map ψ) (rename ψ p) = rename ψ (iterPD L p)`. -/
theorem iterPD_rename {N : ℕ} {σ : Type*} (ψ : σ → Fin N) (hψ : Function.Injective ψ)
    (L : List σ) (p : MvPolynomial σ F) :
    SPDP.iterDerivList (L.map ψ) (rename ψ p) = rename ψ (iterPD L p) := by
  induction L generalizing p with
  | nil => rfl
  | cons c L' ih =>
    show SPDP.iterDerivList (L'.map ψ) (pderiv (ψ c) (rename ψ p)) = _
    rw [pderiv_rename hψ, ih, iterPD_cons]

/-- Iterated derivative of a squarefree unit monomial: removes the differentiated cells, or vanishes. -/
theorem iterPD_monomial {σ : Type*} [DecidableEq σ] (L : List σ) (hnd : L.Nodup) (d : σ →₀ ℕ)
    (hsq : ∀ x, d x ≤ 1) :
    iterPD L (monomial d (1:F))
      = if (∀ c ∈ L, d c = 1) then monomial (d - ∑ c ∈ L.toFinset, Finsupp.single c (1:ℕ)) 1 else 0 := by
  classical
  induction L generalizing d with
  | nil => simp [iterPD]
  | cons c L' ih =>
    rw [iterPD_cons, pderiv_monomial]
    have hnd' : L'.Nodup := (List.nodup_cons.mp hnd).2
    have hcL' : c ∉ L' := (List.nodup_cons.mp hnd).1
    by_cases hdc : d c = 1
    · rw [hdc]
      simp only [Nat.cast_one, mul_one]
      have hsq' : ∀ x, (d - Finsupp.single c (1:ℕ)) x ≤ 1 := fun x =>
        le_trans (by rw [Finsupp.tsub_apply]; exact tsub_le_self) (hsq x)
      rw [ih hnd' (d - Finsupp.single c (1:ℕ)) hsq']
      have hcond : (∀ x ∈ L', (d - Finsupp.single c (1:ℕ)) x = 1) ↔ (∀ x ∈ (c :: L'), d x = 1) := by
        constructor
        · intro h x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hdc
          · have hxc : x ≠ c := fun h => hcL' (h ▸ hx')
            have := h x hx'
            rwa [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (fun h => hxc h.symm), Nat.sub_zero] at this
        · intro h x hx
          have hxc : x ≠ c := fun h => hcL' (h ▸ hx)
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (fun h => hxc h.symm), Nat.sub_zero]
          exact h x (List.mem_cons_of_mem _ hx)
      by_cases hall : ∀ x ∈ (c :: L'), d x = 1
      · rw [if_pos (hcond.mpr hall), if_pos hall]
        congr 1
        rw [List.toFinset_cons, Finset.sum_insert (by simpa using hcL'), tsub_add_eq_tsub_tsub]
      · rw [if_neg (fun h => hall (hcond.mp h)), if_neg hall]
    · have hdc0 : d c = 0 := by have := hsq c; omega
      rw [hdc0]
      simp only [Nat.cast_zero, mul_zero, map_zero, iterPD_zero]
      rw [if_neg]
      intro h; exact hdc (h c (by simp))

/-! ### The matching permutation (nonzero witness) -/

/-- Order-matching bijection `R ≃ C` (i-th element to i-th element). -/
noncomputable def matchEqR (R C : Finset (Fin k)) {κ : ℕ} (hR : R.card = κ) (hC : C.card = κ) :
    {x // x ∈ R} ≃ {x // x ∈ C} :=
  ((R.orderIsoOfFin hR).symm.trans (C.orderIsoOfFin hC)).toEquiv

/-- An arbitrary bijection `Rᶜ ≃ Cᶜ` (equal cardinality). -/
noncomputable def matchEqRc (R C : Finset (Fin k)) {κ : ℕ} (hR : R.card = κ) (hC : C.card = κ) :
    {x // ¬ x ∈ R} ≃ {x // ¬ x ∈ C} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_coe, hR, hC])

/-- A permutation of `Fin k` mapping the sorted `R` onto the sorted `C` (extends the matching). -/
noncomputable def matchPerm (R C : Finset (Fin k)) {κ : ℕ} (hR : R.card = κ) (hC : C.card = κ) :
    Equiv.Perm (Fin k) :=
  (Equiv.sumCompl (· ∈ R)).symm.trans
    ((Equiv.sumCongr (matchEqR R C hR hC) (matchEqRc R C hR hC)).trans (Equiv.sumCompl (· ∈ C)))

theorem matchPerm_apply (R C : Finset (Fin k)) {κ : ℕ} (hR : R.card = κ) (hC : C.card = κ) (i : Fin κ) :
    matchPerm R C hR hC (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i := by
  have hmem : R.orderEmbOfFin hR i ∈ R := R.orderEmbOfFin_mem hR i
  have h1 : (⟨R.orderEmbOfFin hR i, hmem⟩ : {x // x ∈ R}) = (R.orderIsoOfFin hR) i :=
    Subtype.ext (coe_orderIsoOfFin_apply R hR i).symm
  unfold matchPerm
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hmem, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.sumCompl_apply_inl]
  show (↑(matchEqR R C hR hC ⟨R.orderEmbOfFin hR i, hmem⟩) : Fin k) = C.orderEmbOfFin hC i
  unfold matchEqR
  rw [OrderIso.coe_toEquiv, OrderIso.trans_apply, h1, OrderIso.symm_apply_apply]
  exact coe_orderIsoOfFin_apply C hC i

/-! ### The order-`κ` derivative family and the exponential bound -/

/-- The matching cell-list for `(R,C)`: pair the `i`-th element of `R` with the `i`-th element of `C`. -/
noncomputable def matchList (R C : Finset (Fin k)) {κ : ℕ} (hR : R.card = κ) (hC : C.card = κ) :
    List (Fin k × Fin k) :=
  (List.finRange κ).map (fun i => (R.orderEmbOfFin hR i, C.orderEmbOfFin hC i))

variable {κ : ℕ}

theorem matchList_length (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ) :
    (matchList R C hR hC).length = κ := by
  rw [matchList, List.length_map, List.length_finRange]

theorem matchList_nodup (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ) :
    (matchList R C hR hC).Nodup := by
  rw [matchList]
  apply List.Nodup.map _ (List.nodup_finRange κ)
  intro i j h
  exact (R.orderEmbOfFin hR).injective (congrArg Prod.fst h)

/-- Image of `univ` under the order-embedding is the finset. -/
theorem image_orderEmbOfFin (R : Finset (Fin k)) (hR : R.card = κ) :
    Finset.univ.image (R.orderEmbOfFin hR) = R := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact R.orderEmbOfFin_mem hR i
  · rw [hR, Finset.card_image_of_injective _ (R.orderEmbOfFin hR).injective, Finset.card_univ,
      Fintype.card_fin]

/-- Value of the permutation-degree Finsupp at a cell. -/
theorem sumSingle_apply (τ : Equiv.Perm (Fin k)) (a b : Fin k) :
    (∑ j, Finsupp.single (j, τ j) (1:ℕ)) (a, b) = if τ a = b then 1 else 0 := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single a]
  · simp [Finsupp.single_apply, Prod.ext_iff]
  · intro x _ hx; simp [Prod.ext_iff, hx]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The permutation degree is squarefree. -/
theorem hsq_sumSingle (τ : Equiv.Perm (Fin k)) :
    ∀ x, (∑ j, Finsupp.single (j, τ j) (1:ℕ)) x ≤ 1 := by
  intro x; obtain ⟨a, b⟩ := x; rw [sumSingle_apply]; split <;> simp

/-- The matching cells are exactly present in `M_τ` iff `τ` extends the matching. -/
theorem matchList_mem_iff (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ)
    (τ : Equiv.Perm (Fin k)) :
    (∀ c ∈ matchList R C hR hC, (∑ j, Finsupp.single (j, τ j) (1:ℕ)) c = 1) ↔
    (∀ i, τ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i) := by
  constructor
  · intro h i
    have hc : (R.orderEmbOfFin hR i, C.orderEmbOfFin hC i) ∈ matchList R C hR hC :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have hval := h _ hc
    rw [sumSingle_apply] at hval
    by_contra hne; rw [if_neg hne] at hval; exact one_ne_zero hval.symm
  · intro h c hc
    rw [matchList, List.mem_map] at hc
    obtain ⟨i, _, rfl⟩ := hc
    rw [sumSingle_apply, if_pos (h i)]

/-- The removed degree equals the row-`R` part; the derivative degree is the row-`Rᶜ` part. -/
theorem dtau_sub_oneL (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ)
    (τ : Equiv.Perm (Fin k)) (hext : ∀ i, τ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i) :
    (∑ j, Finsupp.single (j, τ j) (1:ℕ)) - (∑ c ∈ (matchList R C hR hC).toFinset, Finsupp.single c 1)
      = ∑ j ∈ Rᶜ, Finsupp.single (j, τ j) 1 := by
  classical
  have honeL : (∑ c ∈ (matchList R C hR hC).toFinset, Finsupp.single c (1:ℕ))
      = ∑ j ∈ R, Finsupp.single (j, τ j) 1 := by
    have h1 : (matchList R C hR hC).toFinset
        = Finset.univ.image (fun i => (R.orderEmbOfFin hR i, C.orderEmbOfFin hC i)) := by
      ext c
      rw [matchList, List.mem_toFinset, List.mem_map, Finset.mem_image]
      simp only [List.mem_finRange, Finset.mem_univ, true_and]
    rw [h1, Finset.sum_image (fun i _ j _ h => (R.orderEmbOfFin hR).injective (congrArg Prod.fst h))]
    conv_rhs => rw [← image_orderEmbOfFin R hR]
    rw [Finset.sum_image (fun i _ j _ h => (R.orderEmbOfFin hR).injective h)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hext i])
  rw [honeL, ← Finset.sum_add_sum_compl R (fun j => Finsupp.single (j, τ j) (1:ℕ)), add_tsub_cancel_left]

/-- The order-`κ` derivative of the permanent along the `(R,C)` matching. -/
noncomputable def blockDeriv (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ) :
    MvPolynomial (Fin k × Fin k) F :=
  iterPD (matchList R C hR hC) (permPoly k F)

/-- The clean per-permutation form of the block derivative term. -/
theorem iterPD_matchList_perm (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ)
    (τ : Equiv.Perm (Fin k)) :
    iterPD (matchList R C hR hC) (monomial (∑ j, Finsupp.single (j, τ j) 1) (1:F))
      = if (∀ i, τ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i)
        then monomial (∑ j ∈ Rᶜ, Finsupp.single (j, τ j) 1) 1 else 0 := by
  rw [iterPD_monomial (matchList R C hR hC) (matchList_nodup R C hR hC) _ (hsq_sumSingle τ)]
  by_cases hext : ∀ i, τ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i
  · rw [if_pos ((matchList_mem_iff R C hR hC τ).mpr hext), if_pos hext, dtau_sub_oneL R C hR hC τ hext]
  · rw [if_neg (fun h => hext ((matchList_mem_iff R C hR hC τ).mp h)), if_neg hext]

theorem blockDeriv_eq_sum (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ) :
    blockDeriv R C hR hC (F := F)
      = ∑ τ : Equiv.Perm (Fin k),
        (if (∀ i, τ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i)
          then monomial (∑ j ∈ Rᶜ, Finsupp.single (j, τ j) 1) (1:F) else 0) := by
  unfold blockDeriv permPoly
  rw [iterPD_sum]
  exact Finset.sum_congr rfl (fun τ _ => by rw [permMono_eq univ τ, iterPD_matchList_perm])

/-- **Support of the block derivative**: every monomial uses row-set `Rᶜ` and col-set `Cᶜ`. -/
theorem blockDeriv_support_key (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ)
    (m : (Fin k × Fin k) →₀ ℕ) (hm : m ∈ (blockDeriv R C hR hC (F := F)).support) :
    (m.support.image Prod.fst = Rᶜ) ∧ (m.support.image Prod.snd = Cᶜ) := by
  classical
  rw [blockDeriv_eq_sum] at hm
  obtain ⟨τ, _, hmτ⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hm)
  by_cases hext : ∀ i, τ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i
  · rw [if_pos hext] at hmτ
    have hcne : MvPolynomial.coeff m (monomial (∑ j ∈ Rᶜ, Finsupp.single (j, τ j) 1) (1:F)) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hmτ
    rw [MvPolynomial.coeff_monomial] at hcne
    have hmd : (∑ j ∈ Rᶜ, Finsupp.single (j, τ j) 1) = m := by
      by_contra hmd; rw [if_neg hmd] at hcne; exact hcne rfl
    subst hmd
    have hinj : Set.InjOn (fun j => (j, τ j)) ↑(Rᶜ : Finset (Fin k)) := fun x _ y _ h => congrArg Prod.fst h
    rw [support_sum_single_one Rᶜ (fun j => (j, τ j)) hinj]
    have himτR : R.image τ = C := by
      rw [← image_orderEmbOfFin R hR, Finset.image_image]
      rw [show ((⇑τ ∘ ⇑(R.orderEmbOfFin hR)) : Fin κ → Fin k) = ⇑(C.orderEmbOfFin hC) from funext hext]
      exact image_orderEmbOfFin C hC
    have huniv : (Finset.univ : Finset (Fin k)).image τ = Finset.univ :=
      Finset.eq_univ_of_forall (fun x => Finset.mem_image.mpr ⟨τ.symm x, Finset.mem_univ _, τ.apply_symm_apply x⟩)
    refine ⟨?_, ?_⟩
    · ext j
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨p, ⟨i, hi, rfl⟩, rfl⟩; exact hi
      · intro hj; exact ⟨(j, τ j), ⟨j, hj, rfl⟩, rfl⟩
    · rw [Finset.image_image]
      show (Rᶜ).image (fun j => τ j) = Cᶜ
      rw [Finset.compl_eq_univ_sdiff, Finset.image_sdiff_of_injOn τ.injective.injOn (Finset.subset_univ R),
        huniv, himτR, ← Finset.compl_eq_univ_sdiff]
  · rw [if_neg hext] at hmτ; simp at hmτ

/-- **The block derivative is nonzero** (the matching permutation `matchPerm` yields a witness monomial). -/
theorem blockDeriv_ne_zero (R C : Finset (Fin k)) (hR : R.card = κ) (hC : C.card = κ) :
    blockDeriv R C hR hC (F := F) ≠ 0 := by
  classical
  set τ₀ := matchPerm R C hR hC with hτ₀
  have hext₀ : ∀ i, τ₀ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i := matchPerm_apply R C hR hC
  intro hzero
  have hcoeff : MvPolynomial.coeff (∑ j ∈ Rᶜ, Finsupp.single (j, τ₀ j) 1) (blockDeriv R C hR hC (F := F)) = 0 := by
    rw [hzero]; simp
  rw [blockDeriv_eq_sum, MvPolynomial.coeff_sum, Finset.sum_eq_single τ₀] at hcoeff
  · rw [if_pos hext₀, MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact one_ne_zero hcoeff
  · intro τ _ hτne
    by_cases hext : ∀ i, τ (R.orderEmbOfFin hR i) = C.orderEmbOfFin hC i
    · rw [if_pos hext, MvPolynomial.coeff_monomial, if_neg]
      intro heq
      apply hτne
      -- equal derivative monomials ⇒ τ = τ₀ (agree off R via heq, on R via extending)
      apply Equiv.ext
      intro x
      by_cases hxR : x ∈ R
      · obtain ⟨i, rfl⟩ : ∃ i, R.orderEmbOfFin hR i = x := by
          have : x ∈ Finset.univ.image (R.orderEmbOfFin hR) := by rw [image_orderEmbOfFin R hR]; exact hxR
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this; exact ⟨i, hi⟩
        rw [hext i, hext₀ i]
      · have hxRc : x ∈ (Rᶜ : Finset (Fin k)) := Finset.mem_compl.mpr hxR
        have hinj0 : Set.InjOn (fun j => (j, τ₀ j)) ↑(Rᶜ : Finset (Fin k)) := fun a _ b _ h => congrArg Prod.fst h
        have hinj : Set.InjOn (fun j => (j, τ j)) ↑(Rᶜ : Finset (Fin k)) := fun a _ b _ h => congrArg Prod.fst h
        have hsupp := congrArg Finsupp.support heq
        rw [support_sum_single_one _ _ hinj, support_sum_single_one _ _ hinj0] at hsupp
        have hxmem : (x, τ x) ∈ (Rᶜ).image (fun j => (j, τ₀ j)) := by
          rw [← hsupp]; exact Finset.mem_image_of_mem _ hxRc
        obtain ⟨y, _, hyeq⟩ := Finset.mem_image.mp hxmem
        rw [Prod.mk.injEq] at hyeq
        rw [← hyeq.2, hyeq.1]
    · rw [if_neg hext, MvPolynomial.coeff_zero]
  · intro h; exact absurd (Finset.mem_univ τ₀) h

/-- **The exponential A3 rank lower bound (proved).**  `spdpRank κ 0 (rename ψ Permₖ) ≥ C(k,κ)²` for any injective
relabelling `ψ`: the `C(k,κ)²` order-`κ` derivatives along `(R,C)` matchings are linearly independent (disjoint
supports, row-set `Rᶜ` and col-set `Cᶜ`). -/
theorem spdpRank_renamePerm_choose_ge {N : ℕ} (ψ : Fin k × Fin k → Fin N) (hψ : Function.Injective ψ) :
    (k.choose κ) ^ 2 ≤ SPDP.spdpRank κ 0 (rename ψ (permPoly k F)) := by
  classical
  set Idx := {R : Finset (Fin k) // R.card = κ} × {C : Finset (Fin k) // C.card = κ}
  set w : Idx → MvPolynomial (Fin N) F :=
    fun RC => rename ψ (blockDeriv RC.1.1 RC.2.1 RC.1.2 RC.2.2) with hw
  have hmem : ∀ RC, w RC ∈ SPDP.spdpSubspace κ 0 (rename ψ (permPoly k F)) := by
    intro RC
    apply Submodule.subset_span
    refine ⟨(matchList RC.1.1 RC.2.1 RC.1.2 RC.2.2).map ψ, 1, ?_, totalDegree_one.le, ?_⟩
    · rw [List.length_map, matchList_length]
    · rw [one_mul, hw]; unfold blockDeriv; rw [iterPD_rename ψ hψ]
  have hLIv : LinearIndependent F (fun RC : Idx => blockDeriv RC.1.1 RC.2.1 RC.1.2 RC.2.2 (F := F)) := by
    refine linearIndependent_of_key _
      (fun m => (m.support.image Prod.fst, m.support.image Prod.snd))
      (fun RC => (RC.1.1ᶜ, RC.2.1ᶜ))
      (fun RC => blockDeriv_ne_zero RC.1.1 RC.2.1 RC.1.2 RC.2.2) ?_ ?_
    · intro RC m hm
      obtain ⟨h1, h2⟩ := blockDeriv_support_key RC.1.1 RC.2.1 RC.1.2 RC.2.2 m hm
      simp only [h1, h2]
    · intro RC RC' h
      rw [Prod.mk.injEq] at h
      have e1 : RC.1 = RC'.1 := Subtype.ext (compl_injective h.1)
      have e2 : RC.2 = RC'.2 := Subtype.ext (compl_injective h.2)
      exact Prod.ext e1 e2
  have hLI : LinearIndependent F w := by
    rw [hw]
    exact hLIv.map' (rename ψ).toLinearMap (LinearMap.ker_eq_bot.mpr (rename_injective ψ hψ))
  have hsub : Submodule.span F (Set.range w) ≤ SPDP.spdpSubspace κ 0 (rename ψ (permPoly k F)) := by
    rw [Submodule.span_le]; rintro _ ⟨RC, rfl⟩; exact hmem RC
  have hfin : Module.finrank F (Submodule.span F (Set.range w)) = (k.choose κ) ^ 2 := by
    rw [finrank_span_eq_card hLI, Fintype.card_prod, Fintype.card_finset_len, Fintype.card_fin, sq]
  haveI : FiniteDimensional F (SPDP.spdpSubspace κ 0 (rename ψ (permPoly k F))) :=
    Submodule.finiteDimensional_of_le
      (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree κ 0 (rename ψ (permPoly k F)))
  calc (k.choose κ) ^ 2 = _ := hfin.symm
    _ ≤ Module.finrank F (SPDP.spdpSubspace κ 0 (rename ψ (permPoly k F))) := Submodule.finrank_mono hsub
    _ = SPDP.spdpRank κ 0 (rename ψ (permPoly k F)) := rfl

/-- **The exponential A3 rank lower bound over the admissible block family (proved).**  For every embedding
`e : Fin k ↪ Fin n`, the flattened block permanent has `spdpRank κ 0 ≥ C(k,κ)²` — exponential (`≈ 4^k/k`) at
`κ = k/2`, uniform over the whole family. -/
theorem spdpRank_subPermPoly_flat_choose_ge {n : ℕ} (e : Fin k ↪ Fin n) :
    (k.choose κ) ^ 2 ≤ SPDP.spdpRank κ 0 (rename (finProdFinEquiv ∘ Prod.map e e) (permPoly k F)) := by
  have hmapinj : Function.Injective (Prod.map e e : Fin k × Fin k → Fin n × Fin n) := fun x y h =>
    Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))
  exact spdpRank_renamePerm_choose_ge _ (finProdFinEquiv.injective.comp hmapinj)

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_renamePerm_choose_ge
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_subPermPoly_flat_choose_ge
