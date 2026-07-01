import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAdmissibleBoundary
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSPDPBridge

/-!
# The A3 rank lower bound over the admissible block family: `spdpRank 1 0 (Permₖ) ≥ k²`

`ComputationalDepthAdmissibleBoundary.lean` proved the permanent *survives* every admissible `k×k`-block boundary,
reducing `Permₙ ↦ Permₖ` (`permPoly_blockBoundary_eq`).  This file supplies the missing quantitative half — a genuine
**SPDP-rank lower bound** for the restricted permanent, **uniform over the whole block family**:

  `spdpRank_subPermPoly_flat_ge` — for every embedding `e : Fin k ↪ Fin n`, the (flattened) block permanent
        `subPermPoly e` has `spdpRank 1 0 ≥ k²`.

The mechanism (the honest, *easy* side of SPDP): the permanent's `k²` first-order partial derivatives
`∂_{(a,b)} Permₖ = minorₐᵦ` (the `(a,b)`-minor sub-permanent) are **linearly independent** — every monomial of `minorₐᵦ`
uses row-set `{0..k-1}\{a}` and column-set `{0..k-1}\{b}`, so distinct `(a,b)` give pairwise-disjoint supports.  Hence
the order-`1` SPDP subspace has dimension `≥ k²`.  This is uniform over `e` because `subPermPoly e = rename ψₑ Permₖ`
for an injective `ψₑ`, and injective renaming preserves the derivative structure (`pderiv_rename`) and independence.

## Honest status

This is the `A3` *lower-bound* half done for real: a `Permₖ`-flavoured SPDP-rank lower bound that holds uniformly over
the admissible block family — the hardest object we have (the `VNP`-complete permanent) stays SPDP-rich under every
admissible boundary.  It is **polynomial** (`k²`, from `κ = 1`); the exponential `κ = k/2` bound `C(k,κ)²` is the natural
extension (iterated derivatives → complementary sub-permanents, same disjoint-support argument).  Crucially this is the
*easy* side: a large lower bound on a *hard* polynomial's rank does **not** separate classes — the separation needs the
matching *upper* bound (small circuits ⟹ small rank), which is the barriered wall.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial Finset

variable {k : ℕ} {F : Type*} [Field F]

/-- A reusable independence criterion: nonzero polynomials whose monomials all share a `key` that is injective in the
index are linearly independent (pairwise-disjoint supports, established via the invariant `keyOf`). -/
theorem linearIndependent_of_key {ι σ G K : Type*} [Field G] [Fintype ι] [DecidableEq σ]
    (v : ι → MvPolynomial σ G) (keyOf : (σ →₀ ℕ) → K) (key : ι → K)
    (hne : ∀ i, v i ≠ 0)
    (hsupp : ∀ i, ∀ m ∈ (v i).support, keyOf m = key i)
    (hkey : Function.Injective key) : LinearIndependent G v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr (hne i)
  have hcoeff := congrArg (MvPolynomial.coeff m) hg
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hcoeff
  have hzero : ∀ j ∈ Finset.univ, j ≠ i → MvPolynomial.coeff m (g j • v j) = 0 := by
    intro j _ hji
    rw [MvPolynomial.coeff_smul]
    have hns : m ∉ (v j).support := by
      intro hmj
      exact hji (hkey ((hsupp j m hmj).symm.trans (hsupp i m hm)))
    have hc0 : MvPolynomial.coeff m (v j) = 0 := by
      by_contra hcc; exact hns (MvPolynomial.mem_support_iff.mpr hcc)
    rw [hc0, smul_zero]
  rw [Finset.sum_eq_single i hzero (fun h => absurd (Finset.mem_univ i) h)] at hcoeff
  rw [MvPolynomial.coeff_smul, smul_eq_mul] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right (MvPolynomial.mem_support_iff.mp hm)

/-- Support of a sum of unit-`single`s over an injective family is the image of the index set. -/
theorem support_sum_single_one {ι σ : Type*} [DecidableEq σ] (s : Finset ι) (g : ι → σ)
    (hg : Set.InjOn g s) : (∑ i ∈ s, Finsupp.single (g i) (1 : ℕ)).support = s.image g := by
  classical
  ext c
  simp only [Finsupp.mem_support_iff, Finset.mem_image, Finsupp.finset_sum_apply,
    Finsupp.single_apply]
  constructor
  · intro hc
    by_contra hcon
    push_neg at hcon
    apply hc
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    intro h; exact hcon i hi h
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.sum_eq_single i (fun j hj hji => if_neg (fun h => hji (hg hj hi h)))
      (fun h => absurd hi h)]
    simp

/-- The permanent monomial: `∏ᵢ X_{i,τi} = monomial (∑ᵢ single (i,τi) 1) 1`. -/
theorem permMono_eq (s : Finset (Fin k)) (τ : Equiv.Perm (Fin k)) :
    (∏ i ∈ s, X (i, τ i) : MvPolynomial (Fin k × Fin k) F)
      = monomial (∑ i ∈ s, Finsupp.single (i, τ i) 1) 1 := by
  rw [monomial_sum_one]
  exact Finset.prod_congr rfl (fun i _ => by rw [← X_pow_eq_monomial, pow_one])

/-- The `(a,b)`-minor sub-permanent: the permanent of the matrix with row `a` and column `b` deleted. -/
noncomputable def minorPoly (a b : Fin k) : MvPolynomial (Fin k × Fin k) F :=
  ∑ τ ∈ univ.filter (fun τ : Equiv.Perm (Fin k) => τ a = b), ∏ i ∈ univ.erase a, X (i, τ i)

/-- **The permanent's first partial derivative is the minor (proved).**
`∂_{(a,b)} Permₖ = minorₐᵦ`. -/
theorem pderiv_permPoly (a b : Fin k) :
    pderiv (a, b) (permPoly k F) = minorPoly a b := by
  classical
  unfold permPoly minorPoly
  rw [map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [permMono_eq univ τ, pderiv_monomial]
  have hval : (∑ i, Finsupp.single (i, τ i) 1) (a, b) = if τ a = b then 1 else 0 := by
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single a]
    · simp [Finsupp.single_apply, Prod.ext_iff]
    · intro x _ hx; simp [Prod.ext_iff, hx]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [hval]
  by_cases h : τ a = b
  · rw [if_pos h, if_pos h, Nat.cast_one, mul_one]
    have hsplit : (∑ i, Finsupp.single (i, τ i) 1) - Finsupp.single (a, b) 1
        = ∑ i ∈ univ.erase a, Finsupp.single (i, τ i) 1 := by
      rw [← Finset.add_sum_erase univ (fun i => Finsupp.single (i, τ i) 1) (Finset.mem_univ a)]
      rw [h, add_tsub_cancel_left]
    rw [hsplit]; exact (permMono_eq (univ.erase a) τ).symm
  · rw [if_neg h, if_neg h]; simp

/-- Every monomial of `minorₐᵦ` uses exactly the rows `univ.erase a` and columns `univ.erase b`. -/
theorem minorPoly_support_key (a b : Fin k) (m : (Fin k × Fin k) →₀ ℕ)
    (hm : m ∈ (minorPoly (F := F) a b).support) :
    (m.support.image Prod.fst = univ.erase a) ∧ (m.support.image Prod.snd = univ.erase b) := by
  classical
  unfold minorPoly at hm
  -- the support of the sum lies in the union of the term supports
  obtain ⟨τ, hτf, hmτ⟩ := by
    have := Finsupp.support_finset_sum
      (s := univ.filter (fun τ : Equiv.Perm (Fin k) => τ a = b))
      (f := fun τ => (∏ i ∈ univ.erase a, X (i, τ i) : MvPolynomial (Fin k × Fin k) F))
    have hmem := this hm
    rw [Finset.mem_biUnion] at hmem
    exact hmem
  rw [Finset.mem_filter] at hτf
  have hτ : τ a = b := hτf.2
  rw [permMono_eq (univ.erase a) τ] at hmτ
  -- the monomial's exponent is exactly the erase-a sum
  have hcne : MvPolynomial.coeff m
      (monomial (∑ i ∈ univ.erase a, Finsupp.single (i, τ i) 1) (1 : F)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmτ
  rw [MvPolynomial.coeff_monomial] at hcne
  have hmd : (∑ i ∈ univ.erase a, Finsupp.single (i, τ i) 1) = m := by
    by_contra hmd; rw [if_neg hmd] at hcne; exact hcne rfl
  subst hmd
  have hinj : Set.InjOn (fun i => (i, τ i)) (univ.erase a) :=
    fun x _ y _ h => congrArg Prod.fst h
  rw [support_sum_single_one (univ.erase a) (fun i => (i, τ i)) hinj]
  have huniv : (Finset.univ : Finset (Fin k)).image τ = Finset.univ :=
    Finset.eq_univ_of_forall (fun x => Finset.mem_image.mpr ⟨τ.symm x, Finset.mem_univ _, τ.apply_symm_apply x⟩)
  constructor
  · ext j
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, ⟨i, hi, rfl⟩, rfl⟩; exact hi
    · intro hj; exact ⟨(j, τ j), ⟨j, hj, rfl⟩, rfl⟩
  · rw [Finset.image_image]
    show (univ.erase a).image (fun i => τ i) = univ.erase b
    rw [Finset.image_erase τ.injective, huniv, hτ]

/-- `minorₐᵦ ≠ 0` — the identity-like extension `swap a b` gives a monomial with coefficient `1`. -/
theorem minorPoly_ne_zero (a b : Fin k) : minorPoly (F := F) a b ≠ 0 := by
  classical
  set τ₀ : Equiv.Perm (Fin k) := Equiv.swap a b with hτ₀
  have hτ₀ab : τ₀ a = b := Equiv.swap_apply_left a b
  intro hzero
  have hcoeff : MvPolynomial.coeff (∑ i ∈ univ.erase a, Finsupp.single (i, τ₀ i) 1)
      (minorPoly (F := F) a b) = 0 := by rw [hzero]; simp
  unfold minorPoly at hcoeff
  rw [MvPolynomial.coeff_sum] at hcoeff
  rw [Finset.sum_eq_single τ₀] at hcoeff
  · rw [permMono_eq (univ.erase a) τ₀, MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact one_ne_zero hcoeff
  · intro τ hτf hτne
    rw [Finset.mem_filter] at hτf
    rw [permMono_eq (univ.erase a) τ, MvPolynomial.coeff_monomial, if_neg]
    intro heq
    -- exponents equal ⇒ τ agrees with τ₀ off a, and both send a↦b ⇒ τ = τ₀
    apply hτne
    have hinj0 : Set.InjOn (fun i => (i, τ₀ i)) (univ.erase a) := fun x _ y _ h => congrArg Prod.fst h
    have hinj : Set.InjOn (fun i => (i, τ i)) (univ.erase a) := fun x _ y _ h => congrArg Prod.fst h
    have hsupp := congrArg Finsupp.support heq
    rw [support_sum_single_one _ _ hinj, support_sum_single_one _ _ hinj0] at hsupp
    apply Equiv.ext
    intro x
    by_cases hxa : x = a
    · rw [hxa, hτf.2, hτ₀ab]
    · have hxe : x ∈ univ.erase a := Finset.mem_erase.mpr ⟨hxa, Finset.mem_univ x⟩
      have : (x, τ x) ∈ (univ.erase a).image (fun i => (i, τ₀ i)) := by
        rw [← hsupp]; exact Finset.mem_image_of_mem _ hxe
      rw [Finset.mem_image] at this
      obtain ⟨y, hy, hyeq⟩ := this
      rw [Prod.mk.injEq] at hyeq
      rw [← hyeq.2, hyeq.1]
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ τ₀, hτ₀ab⟩) h

/-- **The abstract `A3` rank lower bound (proved).**  For any injective relabelling `ψ` of the `k²` matrix cells into a
single index type, the renamed permanent `rename ψ Permₖ` has order-`1` SPDP rank `≥ k²`: its `k²` first partials
(the minors) are linearly independent. -/
theorem spdpRank_renamePerm_ge {N : ℕ} (ψ : Fin k × Fin k → Fin N) (hψ : Function.Injective ψ) :
    k ^ 2 ≤ SPDP.spdpRank 1 0 (rename ψ (permPoly k F)) := by
  classical
  set w : Fin k × Fin k → MvPolynomial (Fin N) F :=
    fun ab => rename ψ (minorPoly ab.1 ab.2) with hw
  -- each `w ab` is the order-1 derivative `∂_{ψ ab} (rename ψ Permₖ)`, hence a generator
  have hgen : ∀ ab : Fin k × Fin k, w ab = pderiv (ψ ab) (rename ψ (permPoly k F)) := by
    intro ab
    rw [hw, pderiv_rename hψ, pderiv_permPoly]
  have hmem : ∀ ab, w ab ∈ SPDP.spdpSubspace 1 0 (rename ψ (permPoly k F)) := by
    intro ab
    apply Submodule.subset_span
    refine ⟨[ψ ab], 1, rfl, totalDegree_one.le, ?_⟩
    rw [one_mul, hgen]; rfl
  -- linear independence via the (row-set, col-set) invariant
  have hLIminor : LinearIndependent F (fun ab : Fin k × Fin k => minorPoly (F := F) ab.1 ab.2) := by
    refine linearIndependent_of_key _
      (fun m => (m.support.image Prod.fst, m.support.image Prod.snd))
      (fun ab => (univ.erase ab.1, univ.erase ab.2))
      (fun ab => minorPoly_ne_zero ab.1 ab.2) ?_ ?_
    · intro ab m hm
      obtain ⟨h1, h2⟩ := minorPoly_support_key ab.1 ab.2 m hm
      simp only [h1, h2]
    · intro ab ab' h
      rw [Prod.mk.injEq] at h
      have e1 : ab.1 = ab'.1 := by
        by_contra hne
        have hmem : ab.1 ∈ univ.erase ab'.1 := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
        rw [← h.1] at hmem
        exact (Finset.mem_erase.mp hmem).1 rfl
      have e2 : ab.2 = ab'.2 := by
        by_contra hne
        have hmem : ab.2 ∈ univ.erase ab'.2 := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
        rw [← h.2] at hmem
        exact (Finset.mem_erase.mp hmem).1 rfl
      exact Prod.ext e1 e2
  have hLI : LinearIndependent F w := by
    rw [hw]
    exact hLIminor.map' (rename ψ).toLinearMap
      (LinearMap.ker_eq_bot.mpr (rename_injective ψ hψ))
  -- assemble: k² independent elements inside the finite-dimensional SPDP subspace
  have hsub : Submodule.span F (Set.range w) ≤ SPDP.spdpSubspace 1 0 (rename ψ (permPoly k F)) := by
    rw [Submodule.span_le]; rintro _ ⟨ab, rfl⟩; exact hmem ab
  have hfin : Module.finrank F (Submodule.span F (Set.range w)) = k ^ 2 := by
    rw [finrank_span_eq_card hLI, Fintype.card_prod, Fintype.card_fin, sq]
  haveI : FiniteDimensional F (SPDP.spdpSubspace 1 0 (rename ψ (permPoly k F))) :=
    Submodule.finiteDimensional_of_le
      (NFrameSPDPBridge.spdpSubspace_le_restrictTotalDegree 1 0 (rename ψ (permPoly k F)))
  calc k ^ 2 = _ := hfin.symm
    _ ≤ Module.finrank F (SPDP.spdpSubspace 1 0 (rename ψ (permPoly k F))) := Submodule.finrank_mono hsub
    _ = SPDP.spdpRank 1 0 (rename ψ (permPoly k F)) := rfl

/-- **The `A3` rank lower bound over the admissible block family (proved).**  For every embedding `e : Fin k ↪ Fin n`,
the block permanent `subPermPoly e` — the reduction of `Permₙ` under the admissible `k×k`-block boundary
(`permPoly_blockBoundary_eq`) — has order-`1` SPDP rank `≥ k²` once flattened to a single index.  Uniform over the whole
family `e`. -/
theorem spdpRank_subPermPoly_flat_ge {n : ℕ} (e : Fin k ↪ Fin n) :
    k ^ 2 ≤ SPDP.spdpRank 1 0 (rename (finProdFinEquiv ∘ Prod.map e e) (permPoly k F)) := by
  have hmapinj : Function.Injective (Prod.map e e : Fin k × Fin k → Fin n × Fin n) := by
    intro x y h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))
  have hψ : Function.Injective (finProdFinEquiv ∘ (Prod.map e e : Fin k × Fin k → Fin n × Fin n)) :=
    finProdFinEquiv.injective.comp hmapinj
  exact spdpRank_renamePerm_ge _ hψ

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_renamePerm_ge
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.spdpRank_subPermPoly_flat_ge
