import Mathlib

/-!
# G4-a: the paper's Definition 12 SPDP measure, formalised (Mathlib only)

Primary source: arXiv v5 ("P vs NP Paper.pdf", sha256 c39b7045…26240), p. 31–32,
`/workspace/pvsnp/paper.txt` lines 1509–1525. Verbatim (pdftotext, layout repaired):

> Definition 12 (SPDP Matrix). Let p ∈ F[x1,...,xN] and let B = {B1,...,Bm} be a partition of
> {1,...,N} into blocks of size ≤ b = O(1). Fix κ, ℓ ∈ N and let rows be indexed by pairs (τ, u)
> with multi-index τ ∈ N^N of weight |τ| = κ whose block support satisfies
> |{j : ∃ i ∈ Bj, τi > 0}| ≤ κ, and u a monomial of degree ≤ ℓ. Columns are monomials x^β with
> deg x^β ≤ deg(p) − κ + ℓ (empty set if negative). Define
>   M^B_{κ,ℓ}(p)[(τ,u), x^β] := coeff_{x^β}(u · ∂^τ p),   Γ^B_{κ,ℓ}(p) := rank_F M^B_{κ,ℓ}(p).
> All basis choices for rows/columns are by default the standard monomial bases; rank is
> basis–invariant by Lemma 37. We take the ambient coefficient space to be the multilinear
> (Boolean) monomial basis modulo ⟨x_i² − x_i⟩, with columns indexed by multilinear monomials
> of degree at most D := max{0, deg(p) − κ + ℓ} (i.e. the basis B_{κ,ℓ} of the codimension note).
> Degree guard. If deg(p) − κ + ℓ < 0 then M_{κ,ℓ}(p) = 0, hence Γ_{κ,ℓ}(p) = 0.
(Notation, line 1503: for τ ∈ N^N, |τ| = Σ_i τ_i and ∂^τ = Π_i ∂_{x_i}^{τ_i}.)

## Our reading (recorded, see NOTES_G4.md G4.0)
* Rows: every pair (τ, u), τ : Fin N →₀ ℕ with Σ τ_i = κ (repeated variables allowed), the block
  condition kept literally (`blockSupport`), and u = x^a ANY monomial with Σ a_i ≤ ℓ in all N
  variables (no `vars ⊆ S` restriction).
* "modulo ⟨x_i² − x_i⟩" is read in two conventions (`Conv`):
  `reduce` (x^a ↦ x^{min(a,1)}, the actual quotient map) and `drop` (delete non-multilinear
  monomials, = the Lean repository's `mlProj`).
* Columns: multilinear monomials x^β with Σ β_i ≤ D = deg p + ℓ − κ (ℕ-subtraction = max{0,·});
  `colRestrict` keeps exactly those coefficients. `row_colRestrict_eq` proves that this restriction
  never changes a row, so the column condition does not matter.
* Rank of the matrix = dimension of the span of its row vectors = `Module.finrank` of the span of
  the (column-restricted, reduced) row polynomials. `def12Span_finiteDimensional` shows the span is
  finite-dimensional, so `finrank` is the true rank (not the junk value 0).
* The degree guard is implemented literally (`if p.totalDegree + ℓ < κ then 0`).
* The block condition is vacuous: `blockSupport_card_le` (any τ of weight κ satisfies it).
* For multilinear p, τ with a repeated variable gives ∂^τ p = 0 (not needed below; noted only).

## Lean measure, restated locally VERBATIM
`PallLean/MultilinearSPDP.lean` imports NPWitness/Compiler/IdentityMinor/LowDegAnnihilation
(heavy, non-Mathlib). We therefore copy, verbatim, the definitions it uses:
`SPDP.BlockPartition`, `SPDP.isBlockAdmissible`, `SPDP.iterDerivList`
(PallLean/SPDPDefs.lean lines 24–29, 104–107, at research/gap-g3 45ab9a05 = main 7f53946 content),
and `Finsupp.IsMultilinear`, `mlProjHom`, `mlProj`, `mlProjLinearMap`, `mlBlockedSpdpSubspace`,
`mlBlockedSpdpRank` (PallLean/MultilinearSPDP.lean lines 30–31, 81–88, 110–131), including the
file's `attribute [local instance] Classical.dec` (line 20).
-/

open MvPolynomial

namespace Def12Measure

attribute [local instance] Classical.dec

/-! ### Verbatim copies (see header) -/

structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

def isBlockAdmissible {n : ℕ} (B : BlockPartition n) (S : List (Fin n)) : Prop :=
  S.Nodup ∧ ∀ b : Fin B.numBlocks, (S.filter (fun i => B.assign i = b)).length ≤ 1

noncomputable def iterDerivList {n : ℕ} {F : Type*} [CommRing F]
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  indices.foldl (fun q i => MvPolynomial.pderiv i q) p

def Finsupp.IsMultilinear {σ : Type*} (α : σ →₀ ℕ) : Prop :=
  ∀ i, α i ≤ 1

noncomputable def mlProjHom {σ : Type*} [DecidableEq σ] (F : Type*) [CommRing F] :
    ((σ →₀ ℕ) →₀ F) →+ ((σ →₀ ℕ) →₀ F) :=
  Finsupp.filterAddHom (fun α => Finsupp.IsMultilinear α)

noncomputable def mlProj {σ : Type*} [DecidableEq σ] {F : Type*} [CommRing F]
    (p : MvPolynomial σ F) : MvPolynomial σ F :=
  mlProjHom F p

noncomputable def mlBlockedSpdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) F),
        S.length = κ ∧ m.totalDegree ≤ ℓ ∧
        m.vars ⊆ S.toFinset ∧  -- Lemma 18: shift support ⊆ derivative variables
        isBlockAdmissible B S ∧
        q = mlProj (m * iterDerivList S p) }

noncomputable def mlBlockedSpdpRank {n : ℕ} {F : Type*} [CommRing F] [Nontrivial F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (mlBlockedSpdpSubspace B κ ℓ p)

/-! ### Definition 12 -/

variable {N : ℕ} {F : Type*} [Field F]

/-- `|τ| = Σ_i τ_i` (paper line 1503). For exponent vectors this is also `deg x^τ`. -/
def weight (τ : Fin N →₀ ℕ) : ℕ := τ.sum (fun _ k => k)

/-- `∂^τ p = Π_i ∂_{x_i}^{τ_i} p`, computed along a list enumerating the multiset of `τ`
(partial derivatives commute, `iterDerivList_perm`, so the order is irrelevant). -/
noncomputable def pderivMulti (τ : Fin N →₀ ℕ) (p : MvPolynomial (Fin N) F) :
    MvPolynomial (Fin N) F :=
  iterDerivList (Finsupp.toMultiset τ).toList p

/-- Block support `{j : ∃ i ∈ B_j, τ_i > 0}`. -/
noncomputable def blockSupport (B : BlockPartition N) (τ : Fin N →₀ ℕ) : Finset (Fin B.numBlocks) :=
  Finset.univ.filter (fun j => ∃ i, B.assign i = j ∧ 0 < τ i)

/-- The two readings of "modulo ⟨x_i² − x_i⟩". -/
inductive Conv | drop | reduce

/-- `x^a ↦ x^{min(a,1)}`. -/
noncomputable def redExp (a : Fin N →₀ ℕ) : Fin N →₀ ℕ :=
  a.mapRange (fun k => min k 1) (by simp)

/-- The quotient map `F[x] → F[x]/⟨x_i² − x_i⟩` written in the multilinear basis. -/
noncomputable def reduceML : MvPolynomial (Fin N) F →ₗ[F] MvPolynomial (Fin N) F :=
  Finsupp.lmapDomain F F redExp

/-- `drop` = the repository's `mlProj` as a linear map. -/
noncomputable def dropML : MvPolynomial (Fin N) F →ₗ[F] MvPolynomial (Fin N) F where
  toFun := mlProj
  map_add' p q := map_add (mlProjHom F) p q
  map_smul' c p := by
    change Finsupp.filter _ (c • p) = c • Finsupp.filter _ p
    ext α
    simp only [Finsupp.filter_apply, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split
    · rfl
    · exact (mul_zero c).symm

noncomputable def convML : Conv → MvPolynomial (Fin N) F →ₗ[F] MvPolynomial (Fin N) F
  | .drop => dropML
  | .reduce => reduceML

/-- Column index set: multilinear monomials of degree `≤ D`. -/
def colSet (N D : ℕ) : Set (Fin N →₀ ℕ) := {β | Finsupp.IsMultilinear β ∧ weight β ≤ D}

/-- Keep exactly the coefficients on the Def. 12 columns. -/
noncomputable def colRestrict (D : ℕ) : MvPolynomial (Fin N) F →ₗ[F] MvPolynomial (Fin N) F where
  toFun q := Finsupp.filter (fun β => β ∈ colSet N D) q
  map_add' p q := Finsupp.filter_add
  map_smul' c p := by
    change Finsupp.filter _ (c • p) = c • Finsupp.filter _ p
    ext α
    simp only [Finsupp.filter_apply, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split
    · rfl
    · exact (mul_zero c).symm

/-- The Def. 12 row vectors (as polynomials in the column basis). -/
def def12Rows (c : Conv) (B : BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) F) :
    Set (MvPolynomial (Fin N) F) :=
  { q | ∃ τ u : Fin N →₀ ℕ, weight τ = κ ∧ (blockSupport B τ).card ≤ κ ∧ weight u ≤ ℓ ∧
      q = colRestrict (p.totalDegree + ℓ - κ) (convML c (monomial u 1 * pderivMulti τ p)) }

noncomputable def def12Span (c : Conv) (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) F) : Submodule F (MvPolynomial (Fin N) F) :=
  Submodule.span F (def12Rows c B κ ℓ p)

/-- `Γ^B_{κ,ℓ}(p)` of Def. 12 (with the degree guard). -/
noncomputable def def12Rank (c : Conv) (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) F) : ℕ :=
  if p.totalDegree + ℓ < κ then 0 else Module.finrank F (def12Span c B κ ℓ p)

/-! ### Basic facts -/

theorem weight_add (a b : Fin N →₀ ℕ) : weight (a + b) = weight a + weight b := by
  unfold weight; exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem weight_single (i : Fin N) (k : ℕ) : weight (Finsupp.single i k) = k := by
  unfold weight; simp

theorem weight_le_of_le {a b : Fin N →₀ ℕ} (h : a ≤ b) : weight a ≤ weight b := by
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  rw [weight_add]; omega

/-- The block condition of Def. 12 is implied by `|τ| = κ`. -/
theorem blockSupport_card_le (B : BlockPartition N) (τ : Fin N →₀ ℕ) :
    (blockSupport B τ).card ≤ weight τ := by
  have h1 : blockSupport B τ ⊆ τ.support.image B.assign := by
    intro j hj
    simp only [blockSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨i, rfl, hi⟩ := hj
    exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr (by omega), rfl⟩
  have h2 : τ.support.card ≤ weight τ := by
    unfold weight Finsupp.sum
    calc τ.support.card = ∑ _i ∈ τ.support, 1 := by simp
      _ ≤ ∑ i ∈ τ.support, τ i := Finset.sum_le_sum (fun i hi => by
          have := Finsupp.mem_support_iff.mp hi; omega)
  exact (Finset.card_le_card h1).trans (Finset.card_image_le.trans h2)

theorem blockCondition_vacuous (B : BlockPartition N) {κ : ℕ} (τ : Fin N →₀ ℕ)
    (h : weight τ = κ) : (blockSupport B τ).card ≤ κ :=
  h ▸ blockSupport_card_le B τ

/-! ### Coefficients of partial derivatives -/

theorem coeff_pderiv (i : Fin N) (q : MvPolynomial (Fin N) F) (s : Fin N →₀ ℕ) :
    coeff s (pderiv i q) = coeff (s + Finsupp.single i 1) q * ((s i : F) + 1) := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hu : u = s + Finsupp.single i 1
    · subst hu
      simp
    · rw [if_neg hu, zero_mul]
      split_ifs with h
      · by_cases hui : u i = 0
        · simp [hui]
        · exfalso; apply hu
          rw [← h]
          exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))).symm
      · rfl
  | add p q hp hq => simp [hp, hq, add_mul]

theorem pderiv_comm (i j : Fin N) (q : MvPolynomial (Fin N) F) :
    pderiv i (pderiv j q) = pderiv j (pderiv i q) := by
  ext s
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases hij : i = j
  · subst hij; rfl
  · have e1 : s + Finsupp.single i 1 + Finsupp.single j 1
        = s + Finsupp.single j 1 + Finsupp.single i 1 := by abel
    rw [e1]
    simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg hij, if_neg (Ne.symm hij),
      add_zero]
    ring

theorem iterDerivList_cons (i : Fin N) (L : List (Fin N)) (p : MvPolynomial (Fin N) F) :
    iterDerivList (i :: L) p = iterDerivList L (pderiv i p) := rfl

theorem iterDerivList_perm {L L' : List (Fin N)} (h : L.Perm L') (p : MvPolynomial (Fin N) F) :
    iterDerivList L p = iterDerivList L' p := by
  unfold iterDerivList
  exact h.foldl_eq' (fun x _ y _ z => pderiv_comm y x z) p

/-- `∂^τ` for the multi-index of a list is the iterated derivative along that list. -/
theorem pderivMulti_ofList (L : List (Fin N)) (p : MvPolynomial (Fin N) F) :
    pderivMulti (Multiset.toFinsupp (L : Multiset (Fin N))) p = iterDerivList L p := by
  unfold pderivMulti
  rw [Multiset.toFinsupp_toMultiset]
  apply iterDerivList_perm
  exact Multiset.coe_eq_coe.mp (Multiset.coe_toList _)

theorem weight_ofList (L : List (Fin N)) :
    weight (Multiset.toFinsupp (L : Multiset (Fin N))) = L.length := by
  have := Finsupp.card_toMultiset (Multiset.toFinsupp (L : Multiset (Fin N)))
  rw [Multiset.toFinsupp_toMultiset] at this
  exact this.symm.trans (Multiset.coe_card L)

theorem iterDerivList_zero (L : List (Fin N)) :
    iterDerivList L (0 : MvPolynomial (Fin N) F) = 0 := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [iterDerivList_cons, map_zero, ih]

/-- Every monomial of `∂_L p` has degree `≤ deg p − |L|`. -/
theorem support_iterDerivList (L : List (Fin N)) (p : MvPolynomial (Fin N) F) :
    ∀ s ∈ (iterDerivList L p).support, weight s + L.length ≤ p.totalDegree := by
  induction L generalizing p with
  | nil => intro s hs; simpa [weight] using le_totalDegree hs
  | cons i L ih =>
    intro s hs
    rw [iterDerivList_cons] at hs
    have h1 := ih (pderiv i p) s hs
    have h2 : ∀ t ∈ (pderiv i p).support, weight t + 1 ≤ p.totalDegree := by
      intro t ht
      have hc := Finsupp.mem_support_iff.mp ht
      change coeff t (pderiv i p) ≠ 0 at hc
      rw [coeff_pderiv] at hc
      have hc' : coeff (t + Finsupp.single i 1) p ≠ 0 := left_ne_zero_of_mul hc
      have := le_totalDegree (Finsupp.mem_support_iff.mpr hc')
      have hw : weight (t + Finsupp.single i 1) = weight t + 1 := by
        rw [weight_add, weight_single]
      change weight (t + Finsupp.single i 1) ≤ _ at this
      omega
    have h3 : (pderiv i p).totalDegree + 1 ≤ p.totalDegree ∨ pderiv i p = 0 := by
      by_cases h0 : pderiv i p = 0
      · exact Or.inr h0
      · left
        obtain ⟨t, ht, hdeg⟩ := Finset.exists_max_image (pderiv i p).support
          (fun t => t.sum fun _ e => e) (Finsupp.support_nonempty_iff.mpr h0)
        have : (pderiv i p).totalDegree = t.sum fun _ e => e :=
          le_antisymm (Finset.sup_le hdeg) (le_totalDegree ht)
        have h4 := h2 t ht
        change (t.sum fun _ e => e) + 1 ≤ _ at h4
        omega
    rcases h3 with h3 | h3
    · simp only [List.length_cons]; omega
    · rw [h3, iterDerivList_zero, MvPolynomial.support_zero] at hs
      exact absurd hs (Finset.notMem_empty s)

theorem iterDerivList_eq_zero_of_lt (L : List (Fin N)) (p : MvPolynomial (Fin N) F)
    (h : p.totalDegree < L.length) : iterDerivList L p = 0 := by
  by_contra hne
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  have := support_iterDerivList L p s hs
  omega

theorem length_toList_toMultiset (τ : Fin N →₀ ℕ) :
    (Finsupp.toMultiset τ).toList.length = weight τ := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]; rfl

theorem support_pderivMulti (τ : Fin N →₀ ℕ) (p : MvPolynomial (Fin N) F) :
    ∀ s ∈ (pderivMulti τ p).support, weight s + weight τ ≤ p.totalDegree := by
  intro s hs
  have := support_iterDerivList _ p s hs
  rwa [length_toList_toMultiset] at this

/-! ### The conventions only produce multilinear monomials of no larger degree -/

theorem redExp_le (t : Fin N →₀ ℕ) : redExp t ≤ t := by
  intro i; simp [redExp]

theorem redExp_multilinear (t : Fin N →₀ ℕ) : Finsupp.IsMultilinear (redExp t) := by
  intro i; simp [redExp]

theorem redExp_of_multilinear {t : Fin N →₀ ℕ} (h : Finsupp.IsMultilinear t) : redExp t = t := by
  ext i; simp only [redExp, Finsupp.mapRange_apply]; have := h i; omega

theorem support_convML (c : Conv) (q : MvPolynomial (Fin N) F) :
    ∀ s ∈ (convML c q).support, Finsupp.IsMultilinear s ∧ ∃ t ∈ q.support, weight s ≤ weight t := by
  intro s hs
  cases c with
  | drop =>
    change s ∈ (Finsupp.filter _ q).support at hs
    rw [Finsupp.support_filter, Finset.mem_filter] at hs
    exact ⟨hs.2, s, hs.1, le_rfl⟩
  | reduce =>
    change s ∈ (Finsupp.mapDomain redExp q).support at hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hs)
    exact ⟨redExp_multilinear t, t, ht, weight_le_of_le (redExp_le t)⟩

/-- **Column condition is harmless**: restricting a Def. 12 row to the columns (multilinear,
degree `≤ deg p − κ + ℓ`) does not change it. -/
theorem row_colRestrict_eq (c : Conv) {κ ℓ : ℕ} (p : MvPolynomial (Fin N) F)
    (τ u : Fin N →₀ ℕ) (hτ : weight τ = κ) (hu : weight u ≤ ℓ) :
    colRestrict (p.totalDegree + ℓ - κ) (convML c (monomial u 1 * pderivMulti τ p))
      = convML c (monomial u 1 * pderivMulti τ p) := by
  change Finsupp.filter _ _ = _
  rw [Finsupp.filter_eq_self_iff]
  intro s hs
  obtain ⟨hml, t, ht, hst⟩ := support_convML c _ s (Finsupp.mem_support_iff.mpr hs)
  have hc := Finsupp.mem_support_iff.mp ht
  change coeff t (monomial u 1 * pderivMulti τ p) ≠ 0 at hc
  rw [coeff_monomial_mul'] at hc
  split_ifs at hc with hut
  · have h2 := support_pderivMulti τ p (t - u) (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hc))
    have h3 : weight t = weight u + weight (t - u) := by
      rw [← weight_add, add_tsub_cancel_of_le hut]
    refine ⟨hml, ?_⟩
    omega
  · exact absurd rfl hc

/-! ### Finite-dimensionality: `finrank` is the genuine rank -/

theorem colSet_finite (D : ℕ) : (colSet N D).Finite := by
  apply (Set.finite_Icc (0 : Fin N →₀ ℕ) (Finsupp.equivFunOnFinite.symm (fun _ => 1))).subset
  intro β hβ
  refine ⟨zero_le _, fun i => ?_⟩
  simpa using hβ.1 i

/-- The span of the Def. 12 column monomials (finite). -/
noncomputable def colSpan (N D : ℕ) : Submodule F (MvPolynomial (Fin N) F) :=
  Finsupp.supported F F (colSet N D)

instance colSpan_finiteDimensional (D : ℕ) : FiniteDimensional F (colSpan (F := F) N D) := by
  haveI : Finite (colSet N D) := (colSet_finite D).to_subtype
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := F) (R := F) (colSet N D)).symm

theorem finrank_colSpan (D : ℕ) :
    Module.finrank F (colSpan (F := F) N D) = (colSet_finite (N := N) D).toFinset.card := by
  haveI : Finite (colSet N D) := (colSet_finite D).to_subtype
  have e := (Finsupp.supportedEquivFinsupp (M := F) (R := F) (colSet N D)).finrank_eq
  rw [Module.finrank_finsupp_self] at e
  refine e.trans ?_
  simp

theorem def12Span_le_colSpan (c : Conv) (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) F) :
    def12Span c B κ ℓ p ≤ colSpan N (p.totalDegree + ℓ - κ) := by
  apply Submodule.span_le.mpr
  rintro q ⟨τ, u, -, -, -, rfl⟩
  rw [SetLike.mem_coe]
  change _ ∈ Finsupp.supported F F _
  rw [Finsupp.mem_supported]
  intro s hs
  change s ∈ (Finsupp.filter _ _).support at hs
  rw [Finsupp.support_filter, Finset.mem_filter] at hs
  exact hs.2

instance def12Span_finiteDimensional (c : Conv) (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) F) : FiniteDimensional F (def12Span c B κ ℓ p) :=
  Submodule.finiteDimensional_of_le (def12Span_le_colSpan c B κ ℓ p)

/-- Every Def. 12 rank is at most the number of columns `#{β multilinear, |β| ≤ D}`. -/
theorem def12Rank_le_columns (c : Conv) (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) F) :
    def12Rank c B κ ℓ p ≤ (colSet_finite (N := N) (p.totalDegree + ℓ - κ)).toFinset.card := by
  unfold def12Rank
  split_ifs
  · exact Nat.zero_le _
  · rw [← finrank_colSpan (F := F)]
    exact Submodule.finrank_mono (def12Span_le_colSpan c B κ ℓ p)

/-! ### G4-a (1): the Lean strict measure is ≤ the Def. 12 (drop) measure, for every p -/

theorem lean_le_def12_drop (B : BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) F) :
    mlBlockedSpdpRank B κ ℓ p ≤ def12Rank .drop B κ ℓ p := by
  unfold def12Rank mlBlockedSpdpRank
  split_ifs with hg
  · have hbot : mlBlockedSpdpSubspace B κ ℓ p = ⊥ := by
      unfold mlBlockedSpdpSubspace
      rw [Submodule.span_eq_bot]
      rintro q ⟨S, m, hS, -, -, -, rfl⟩
      rw [iterDerivList_eq_zero_of_lt S p (by omega), mul_zero]
      exact map_zero (mlProjHom F)
    rw [hbot]; simp
  · apply Submodule.finrank_mono
    unfold mlBlockedSpdpSubspace
    apply Submodule.span_le.mpr
    rintro q ⟨S, m, hS, hm, -, -, rfl⟩
    rw [SetLike.mem_coe]
    have hD : iterDerivList S p = pderivMulti (Multiset.toFinsupp (S : Multiset (Fin N))) p :=
      (pderivMulti_ofList S p).symm
    rw [hD]
    set τ := Multiset.toFinsupp (S : Multiset (Fin N))
    have hτ : weight τ = κ := by rw [weight_ofList, hS]
    have key : ∀ u ∈ m.support,
        dropML (monomial u 1 * pderivMulti τ p) ∈ def12Span .drop B κ ℓ p := by
      intro u hu
      apply Submodule.subset_span
      refine ⟨τ, u, hτ, blockCondition_vacuous B τ hτ, ?_, ?_⟩
      · exact (le_totalDegree hu).trans hm
      · exact (row_colRestrict_eq .drop p τ u hτ ((le_totalDegree hu).trans hm)).symm
    have hm_sum : m * pderivMulti τ p
        = ∑ u ∈ m.support, coeff u m • (monomial u 1 * pderivMulti τ p) := by
      conv_lhs => rw [m.as_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
    change dropML (m * pderivMulti τ p) ∈ _
    rw [hm_sum, map_sum]
    exact Submodule.sum_mem _ (fun u hu => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (key u hu))

/-! ### G4-a (2): `p = x₁⋯x_κ`, `κ = ℓ`: Def. 12 rank ≥ Σ_{j≤κ} C(N,j) (both conventions) -/

theorem iterDerivList_monomial_nodup (L : List (Fin N)) (hL : L.Nodup) (t : Fin N →₀ ℕ)
    (ht : ∀ i ∈ L, t i = 0) (a : F) :
    iterDerivList L (monomial (Multiset.toFinsupp (L : Multiset (Fin N)) + t) a) = monomial t a := by
  induction L generalizing t with
  | nil => simp [iterDerivList]
  | cons i L ih =>
    rw [iterDerivList_cons]
    have hiL : i ∉ L := (List.nodup_cons.mp hL).1
    have e : Multiset.toFinsupp ((i :: L : List (Fin N)) : Multiset (Fin N))
        = Finsupp.single i 1 + Multiset.toFinsupp (L : Multiset (Fin N)) := by
      rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]
    rw [e, pderiv_monomial]
    have hcnt : Multiset.toFinsupp (L : Multiset (Fin N)) i = 0 := by
      rw [Multiset.toFinsupp_apply, Multiset.count_eq_zero]; exact_mod_cast hiL
    have hti : t i = 0 := ht i (List.mem_cons_self ..)
    have e2 : Finsupp.single i 1 + Multiset.toFinsupp (L : Multiset (Fin N)) + t
        - Finsupp.single i 1 = Multiset.toFinsupp (L : Multiset (Fin N)) + t := by
      rw [add_assoc, add_tsub_cancel_left]
    rw [e2]
    have e3 : ((Finsupp.single i 1 + Multiset.toFinsupp (L : Multiset (Fin N)) + t :
        Fin N →₀ ℕ) i) = 1 := by
      simp [hcnt, hti]
    rw [e3, Nat.cast_one, mul_one]
    exact ih (List.nodup_cons.mp hL).2 t (fun j hj => ht j (List.mem_cons_of_mem _ hj))

/-- The list `[x_1, …, x_κ]` (0-based: `Fin.castLE h 0, …`). -/
def andList (κ : ℕ) (h : κ ≤ N) : List (Fin N) := (List.finRange κ).map (Fin.castLE h)

theorem andList_nodup (κ : ℕ) (h : κ ≤ N) : (andList κ h).Nodup :=
  (List.nodup_finRange κ).map (Fin.castLE_injective h)

theorem andList_length (κ : ℕ) (h : κ ≤ N) : (andList κ h).length = κ := by simp [andList]

/-- `x_1 ⋯ x_κ` as a monomial. -/
noncomputable def andPoly (κ : ℕ) (h : κ ≤ N) : MvPolynomial (Fin N) F :=
  monomial (Multiset.toFinsupp ((andList κ h : List (Fin N)) : Multiset (Fin N))) 1

theorem monomial_ofList_eq_prod (L : List (Fin N)) :
    (monomial (Multiset.toFinsupp (L : Multiset (Fin N))) (1 : F)) = (L.map X).prod := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton]
    have e : monomial (Finsupp.single i 1 + Multiset.toFinsupp (L : Multiset (Fin N))) (1 : F)
        = monomial (Finsupp.single i 1) 1 * monomial (Multiset.toFinsupp (L : Multiset (Fin N))) 1 := by
      rw [monomial_mul, one_mul]
    rw [e, ih, List.map_cons, List.prod_cons]; rfl

theorem andPoly_eq_prod (κ : ℕ) (h : κ ≤ N) :
    (andPoly κ h : MvPolynomial (Fin N) F) = ∏ i : Fin κ, X (Fin.castLE h i) := by
  rw [andPoly, monomial_ofList_eq_prod, Fin.prod_univ_def, andList, List.map_map]; rfl

theorem andPoly_totalDegree (κ : ℕ) (h : κ ≤ N) :
    (andPoly κ h : MvPolynomial (Fin N) F).totalDegree = κ := by
  rw [andPoly, totalDegree_monomial _ one_ne_zero]
  have := weight_ofList (andList κ h); rw [andList_length] at this; exact this

theorem pderivMulti_andPoly (κ : ℕ) (h : κ ≤ N) :
    pderivMulti (Multiset.toFinsupp ((andList κ h : List (Fin N)) : Multiset (Fin N)))
      (andPoly κ h : MvPolynomial (Fin N) F) = 1 := by
  rw [pderivMulti_ofList, andPoly]
  have := iterDerivList_monomial_nodup (F := F) (andList κ h) (andList_nodup κ h) 0
    (fun _ _ => rfl) 1
  rw [add_zero] at this
  rw [this]; rfl

theorem convML_monomial_multilinear (c : Conv) {β : Fin N →₀ ℕ} (hβ : Finsupp.IsMultilinear β) :
    convML c (monomial β (1 : F)) = monomial β 1 := by
  cases c with
  | drop =>
    change Finsupp.filter _ (Finsupp.single β (1 : F)) = Finsupp.single β 1
    rw [Finsupp.filter_eq_self_iff]
    intro x hx
    by_cases hxb : x = β
    · subst hxb; exact hβ
    · rw [Finsupp.single_apply, if_neg (Ne.symm hxb)] at hx; exact absurd rfl hx
  | reduce =>
    change Finsupp.mapDomain redExp (Finsupp.single β (1 : F)) = Finsupp.single β 1
    rw [Finsupp.mapDomain_single, redExp_of_multilinear hβ]

/-- Exponent vector of a set (multilinear). -/
noncomputable def setExp (s : Finset (Fin N)) : Fin N →₀ ℕ := Multiset.toFinsupp s.val

theorem setExp_multilinear (s : Finset (Fin N)) : Finsupp.IsMultilinear (setExp s) := by
  intro i; rw [setExp, Multiset.toFinsupp_apply]; exact Multiset.nodup_iff_count_le_one.mp s.nodup i

theorem setExp_weight (s : Finset (Fin N)) : weight (setExp s) = s.card := by
  have := Finsupp.card_toMultiset (setExp s)
  rw [setExp, Multiset.toFinsupp_toMultiset] at this
  exact this.symm

theorem setExp_injective : Function.Injective (setExp (N := N)) := by
  intro s t h
  exact Finset.val_injective (Multiset.toFinsupp.injective h)

theorem card_small_finsets (N κ : ℕ) :
    (Finset.univ.filter (fun s : Finset (Fin N) => s.card ≤ κ)).card
      = ∑ j ∈ Finset.range (κ + 1), N.choose j := by
  have e : Finset.univ.filter (fun s : Finset (Fin N) => s.card ≤ κ)
      = (Finset.range (κ + 1)).biUnion (fun j => Finset.powersetCard j Finset.univ) := by
    ext s; simp [Finset.mem_powersetCard]
  rw [e, Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr (fun s hs ht =>
      hij ((Finset.mem_powersetCard.mp hs).2.symm.trans (Finset.mem_powersetCard.mp ht).2))

/-- **G4-a (2).** For `p = x_1 ⋯ x_κ` and `κ = ℓ`, under BOTH conventions and for every block
partition: `Γ^B_{κ,κ}(p) ≥ Σ_{j ≤ κ} C(N, j)`. -/
theorem and_def12_lower (c : Conv) (B : BlockPartition N) (κ : ℕ) (h : κ ≤ N) :
    ∑ j ∈ Finset.range (κ + 1), N.choose j ≤ def12Rank c B κ κ (andPoly κ h : MvPolynomial (Fin N) F) := by
  rw [← card_small_finsets]
  unfold def12Rank
  rw [andPoly_totalDegree, if_neg (by omega)]
  let ι := {s : Finset (Fin N) // s.card ≤ κ}
  let v : ι → MvPolynomial (Fin N) F := fun s => monomial (setExp s.1) 1
  have hli : LinearIndependent F v := by
    have := (MvPolynomial.basisMonomials (Fin N) F).linearIndependent.comp
      (fun s : ι => setExp s.1) (fun a b hab => Subtype.ext (setExp_injective hab))
    convert this using 1
  have hsub : Submodule.span F (Set.range v) ≤ def12Span c B κ κ (andPoly κ h) := by
    apply Submodule.span_le.mpr
    rintro q ⟨s, rfl⟩
    apply Submodule.subset_span
    set τ := Multiset.toFinsupp ((andList κ h : List (Fin N)) : Multiset (Fin N))
    have hτ : weight τ = κ := by rw [weight_ofList, andList_length]
    have hu : weight (setExp s.1) ≤ κ := by rw [setExp_weight]; exact s.2
    refine ⟨τ, setExp s.1, hτ, blockCondition_vacuous B τ hτ, hu, ?_⟩
    rw [row_colRestrict_eq c _ τ _ hτ hu, pderivMulti_andPoly, mul_one,
      convML_monomial_multilinear c (setExp_multilinear _)]
  have h1 := Submodule.finrank_mono hsub
  rw [finrank_span_eq_card hli] at h1
  simpa [ι, Fintype.card_subtype] using h1


/-! ## G4-b: an easy (linear-time) Boolean function reaching the Def. 12 row ceiling up to
`≈ 2^{κ+ℓ}`. Variables: `N = m + m`, `x_i = Fin.castAdd m i`, `y_j = Fin.natAdd m j`.
`f(x,y) = [ |y| = κ ∧ y ≤ x ]`; its characteristic polynomial (Def. 13) is
`subsetPoly m κ = Σ_{|S|=κ} x^S · δ_S(y)`, `δ_S(y) = Π_{j∈S} y_j Π_{j∉S} (1 − y_j)`. -/

section Subset

variable {m : ℕ}

/-- `x^A` for `A ⊆ [m]` (exponent vector). -/
noncomputable def xExp (A : Finset (Fin m)) : Fin (m + m) →₀ ℕ :=
  Multiset.toFinsupp (A.val.map (Fin.castAdd m))

noncomputable def xMon (A : Finset (Fin m)) : MvPolynomial (Fin (m + m)) F := monomial (xExp A) 1

noncomputable def yFactor (S : Finset (Fin m)) (j : Fin m) : MvPolynomial (Fin (m + m)) F :=
  if j ∈ S then X (Fin.natAdd m j) else 1 - X (Fin.natAdd m j)

noncomputable def delta (S : Finset (Fin m)) : MvPolynomial (Fin (m + m)) F :=
  ∏ j : Fin m, yFactor S j

noncomputable def subsetPoly (m κ : ℕ) : MvPolynomial (Fin (m + m)) F :=
  ∑ S ∈ Finset.powersetCard κ (Finset.univ : Finset (Fin m)), xMon S * delta S

theorem castAdd_ne_natAdd (i j : Fin m) : (Fin.castAdd m i : Fin (m + m)) ≠ Fin.natAdd m j := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem xExp_apply_castAdd (A : Finset (Fin m)) (i : Fin m) :
    xExp A (Fin.castAdd m i) = if i ∈ A then 1 else 0 := by
  rw [xExp, Multiset.toFinsupp_apply,
    Multiset.count_map_eq_count' _ _ (Fin.castAdd_injective m m)]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem A.nodup h
  · exact Multiset.count_eq_zero.mpr h

theorem xExp_apply_natAdd (A : Finset (Fin m)) (j : Fin m) : xExp A (Fin.natAdd m j) = 0 := by
  rw [xExp, Multiset.toFinsupp_apply, Multiset.count_eq_zero]
  simp only [Multiset.mem_map, Finset.mem_val, not_exists, not_and]
  intro i _ h; exact castAdd_ne_natAdd i j h

theorem xExp_multilinear (A : Finset (Fin m)) : Finsupp.IsMultilinear (xExp A) := by
  intro v
  refine Fin.addCases (fun i => ?_) (fun j => ?_) v
  · rw [xExp_apply_castAdd]; split_ifs <;> omega
  · rw [xExp_apply_natAdd]; omega

theorem xExp_weight (A : Finset (Fin m)) : weight (xExp A) = A.card := by
  have := Finsupp.card_toMultiset (xExp A)
  rw [xExp, Multiset.toFinsupp_toMultiset, Multiset.card_map] at this
  exact this.symm

theorem xExp_injective : Function.Injective (xExp (m := m)) := by
  intro A B h
  ext i
  have := congrArg (fun e => e (Fin.castAdd m i)) h
  simp only [xExp_apply_castAdd] at this
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp_all

/-- Multilinear support. -/
def MLSupp (q : MvPolynomial (Fin N) F) : Prop := ∀ s ∈ q.support, Finsupp.IsMultilinear s

theorem MLSupp_mul {q₁ q₂ : MvPolynomial (Fin N) F} (h₁ : MLSupp q₁) (h₂ : MLSupp q₂)
    (hd : Disjoint q₁.vars q₂.vars) : MLSupp (q₁ * q₂) := by
  intro s hs i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul q₁ q₂ hs)
  rw [Finsupp.add_apply]
  by_cases hai : a i = 0
  · rw [hai, zero_add]; exact h₂ b hb i
  · by_cases hbi : b i = 0
    · rw [hbi, add_zero]; exact h₁ a ha i
    · exfalso
      have m1 : i ∈ q₁.vars := (mem_vars i).mpr ⟨a, ha, Finsupp.mem_support_iff.mpr hai⟩
      have m2 : i ∈ q₂.vars := (mem_vars i).mpr ⟨b, hb, Finsupp.mem_support_iff.mpr hbi⟩
      exact Finset.disjoint_left.mp hd m1 m2

theorem MLSupp_X (v : Fin N) : MLSupp (X v : MvPolynomial (Fin N) F) := by
  intro s hs i
  rw [X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hs
  subst hs; rw [Finsupp.single_apply]; split_ifs <;> omega

theorem MLSupp_one_sub_X (v : Fin N) : MLSupp (1 - X v : MvPolynomial (Fin N) F) := by
  intro s hs i
  have := support_sub (Fin N) (1 : MvPolynomial (Fin N) F) (X v) hs
  rcases Finset.mem_union.mp this with h | h
  · rw [← C_1, C_apply, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at h
    subst h; simp
  · exact MLSupp_X v s h i

theorem yFactor_props (S : Finset (Fin m)) (j : Fin m) :
    MLSupp (yFactor (F := F) S j) ∧ (yFactor (F := F) S j).vars ⊆ {Fin.natAdd m j} := by
  unfold yFactor
  split_ifs
  · exact ⟨MLSupp_X _, by rw [vars_X]⟩
  · refine ⟨MLSupp_one_sub_X _, (vars_sub_subset _).trans ?_⟩
    rw [vars_one, vars_X]; simp

theorem prod_yFactor_props (S : Finset (Fin m)) (s : Finset (Fin m)) :
    MLSupp (∏ j ∈ s, yFactor (F := F) S j) ∧
      (∏ j ∈ s, yFactor (F := F) S j).vars ⊆ s.image (Fin.natAdd m) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [vars_one]⟩
    intro t ht
    rw [Finset.prod_empty, ← C_1, C_apply, support_monomial, if_neg one_ne_zero,
      Finset.mem_singleton] at ht
    subst ht
    intro i; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    obtain ⟨h1, h2⟩ := yFactor_props (F := F) S a
    refine ⟨MLSupp_mul h1 ih.1 ?_, (vars_mul _ _).trans ?_⟩
    · refine Finset.disjoint_left.mpr (fun v hv1 hv2 => ?_)
      have e1 := Finset.mem_singleton.mp (h2 hv1)
      obtain ⟨b, hb, e2⟩ := Finset.mem_image.mp (ih.2 hv2)
      subst e1
      exact ha ((Fin.natAdd_injective m m e2) ▸ hb)
    · intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · rw [Finset.mem_singleton.mp (h2 h)]; exact Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ih.2 h)
        exact Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hb)

theorem row_MLSupp (A S : Finset (Fin m)) : MLSupp (xMon (F := F) A * delta S) := by
  obtain ⟨h1, h2⟩ := prod_yFactor_props (F := F) S Finset.univ
  refine MLSupp_mul ?_ h1 ?_
  · intro s hs; rw [xMon, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hs
    subst hs; exact xExp_multilinear A
  · refine Finset.disjoint_left.mpr (fun v hv1 hv2 => ?_)
    rw [xMon, vars_monomial one_ne_zero] at hv1
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (h2 hv2)
    exact (Finsupp.mem_support_iff.mp hv1) (xExp_apply_natAdd A j)

theorem convML_of_MLSupp (c : Conv) {q : MvPolynomial (Fin N) F} (h : MLSupp q) :
    convML c q = q := by
  cases c with
  | drop =>
    change Finsupp.filter _ q = q
    rw [Finsupp.filter_eq_self_iff]
    intro s hs; exact h s (Finsupp.mem_support_iff.mpr hs)
  | reduce =>
    change Finsupp.mapDomain redExp q = q
    rw [show Finsupp.mapDomain redExp q = Finsupp.mapDomain id q from
      Finsupp.mapDomain_congr (fun s hs => redExp_of_multilinear (h s hs)), Finsupp.mapDomain_id]

/-! ### derivatives -/

theorem iterDerivList_add (L : List (Fin N)) (p q : MvPolynomial (Fin N) F) :
    iterDerivList L (p + q) = iterDerivList L p + iterDerivList L q := by
  induction L generalizing p q with
  | nil => rfl
  | cons i L ih => rw [iterDerivList_cons, iterDerivList_cons, iterDerivList_cons, map_add, ih]

theorem iterDerivList_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin N) F)
    (L : List (Fin N)) : iterDerivList L (∑ i ∈ s, f i) = ∑ i ∈ s, iterDerivList L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]; exact iterDerivList_zero L
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iterDerivList_add, ih]

theorem pderiv_castAdd_delta (S : Finset (Fin m)) (i : Fin m) :
    pderiv (Fin.castAdd m i) (delta (F := F) S) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨j, -, h⟩ := Finset.mem_image.mp ((prod_yFactor_props (F := F) S Finset.univ).2 hv)
  exact castAdd_ne_natAdd i j h.symm

theorem iterDerivList_mul_delta (S : Finset (Fin m)) (L : List (Fin (m + m)))
    (hL : ∀ v ∈ L, ∃ i, v = Fin.castAdd m i) (g : MvPolynomial (Fin (m + m)) F) :
    iterDerivList L (g * delta S) = iterDerivList L g * delta S := by
  induction L generalizing g with
  | nil => rfl
  | cons v L ih =>
    rw [iterDerivList_cons, iterDerivList_cons]
    obtain ⟨i, rfl⟩ := hL v (List.mem_cons_self ..)
    rw [Derivation.leibniz, pderiv_castAdd_delta, smul_zero, zero_add, smul_eq_mul, mul_comm]
    exact ih (fun w hw => hL w (List.mem_cons_of_mem _ hw)) _

/-- The derivative list for `τ = 1_S` on the x-block. -/
noncomputable def xList (S : Finset (Fin m)) : List (Fin (m + m)) :=
  (Finsupp.toMultiset (xExp S)).toList

theorem xList_coe (S : Finset (Fin m)) :
    ((xList S : List (Fin (m + m))) : Multiset (Fin (m + m))) = S.val.map (Fin.castAdd m) := by
  rw [xList, Multiset.coe_toList, xExp, Multiset.toFinsupp_toMultiset]

theorem xList_mem (S : Finset (Fin m)) : ∀ v ∈ xList S, ∃ i, v = Fin.castAdd m i := by
  intro v hv
  have : v ∈ ((xList S : List (Fin (m + m))) : Multiset (Fin (m + m))) := Multiset.mem_coe.mpr hv
  rw [xList_coe] at this
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp this
  exact ⟨i, rfl⟩

theorem xList_nodup (S : Finset (Fin m)) : (xList S).Nodup := by
  have : ((xList S : List (Fin (m + m))) : Multiset (Fin (m + m))).Nodup := by
    rw [xList_coe]; exact S.nodup.map (Fin.castAdd_injective m m)
  exact Multiset.coe_nodup.mp this

theorem xExp_eq_ofList (S : Finset (Fin m)) :
    xExp S = Multiset.toFinsupp ((xList S : List (Fin (m + m))) : Multiset (Fin (m + m))) := by
  rw [xList_coe]; rfl

theorem iterDerivList_xMon (S S' : Finset (Fin m)) (hcard : S'.card = S.card) :
    iterDerivList (xList S) (xMon (F := F) S') = if S' = S then 1 else 0 := by
  split_ifs with h
  · subst h
    have := iterDerivList_monomial_nodup (F := F) (xList S') (xList_nodup S') 0 (fun _ _ => rfl) 1
    rw [add_zero, ← xExp_eq_ofList] at this
    rw [xMon, this]; rfl
  · have hns : ¬ S ⊆ S' := fun hs => h (Finset.eq_of_subset_of_card_le hs (by omega)).symm
    obtain ⟨i, hiS, hiS'⟩ := Finset.not_subset.mp hns
    have hmem : Fin.castAdd m i ∈ xList S := by
      rw [← Multiset.mem_coe, xList_coe]; exact Multiset.mem_map_of_mem _ hiS
    rw [iterDerivList_perm (List.perm_cons_erase hmem), iterDerivList_cons, xMon, pderiv_monomial,
      xExp_apply_castAdd, if_neg hiS', Nat.cast_zero, mul_zero, monomial_zero, iterDerivList_zero]

theorem pderivMulti_subsetPoly (κ : ℕ) (S : Finset (Fin m)) (hS : S.card = κ) :
    pderivMulti (xExp S) (subsetPoly (F := F) m κ) = delta S := by
  unfold pderivMulti subsetPoly
  change iterDerivList (xList S) _ = _
  rw [iterDerivList_sum]
  rw [Finset.sum_congr rfl (fun S' hS' => by
    rw [iterDerivList_mul_delta S' (xList S) (xList_mem S),
      iterDerivList_xMon S S' (by rw [(Finset.mem_powersetCard.mp hS').2, hS])])]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩)]

/-! ### evaluation maps `y := 1_T` -/

noncomputable def yEval (T : Finset (Fin m)) :
    MvPolynomial (Fin (m + m)) F →ₐ[F] MvPolynomial (Fin (m + m)) F :=
  aeval (Fin.addCases (fun i => X (Fin.castAdd m i)) (fun j => if j ∈ T then 1 else 0))

theorem yEval_delta (S T : Finset (Fin m)) :
    yEval (F := F) T (delta S) = if S = T then 1 else 0 := by
  rw [delta, map_prod]
  have hf : ∀ j, yEval (F := F) T (yFactor S j) =
      if j ∈ S then (if j ∈ T then 1 else 0) else 1 - (if j ∈ T then 1 else 0) := by
    intro j
    unfold yFactor yEval
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
      simp only [hS, hT, if_true, if_false, map_sub, map_one, aeval_X, Fin.addCases_right]
  simp only [hf]
  split_ifs with hST
  · subst hST
    exact Finset.prod_eq_one (fun j _ => by split_ifs <;> simp)
  · obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ S ↔ j ∈ T) := by
      by_contra hc; push_neg at hc; exact hST (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by
      by_cases a : j ∈ S <;> by_cases b : j ∈ T <;> simp_all)

theorem yEval_xMon (T A : Finset (Fin m)) : yEval (F := F) T (xMon A) = xMon A := by
  rw [xMon, yEval, aeval_monomial, map_one, one_mul, monomial_eq, map_one, one_mul]
  apply Finsupp.prod_congr
  intro v hv
  congr 1
  revert hv
  refine Fin.addCases (fun i _ => ?_) (fun j hj => ?_) v
  · simp
  · exact absurd (xExp_apply_natAdd A j) (Finsupp.mem_support_iff.mp hj)

/-- **G4-b, kernel-checked.** For the linear-time function `f(x,y) = [|y| = κ ∧ y ≤ x]` on
`N = 2m` variables (characteristic polynomial `subsetPoly m κ`), under BOTH conventions and
every block partition, with `κ ≤ m` and any `ℓ`:
`C(m, κ) · Σ_{j ≤ ℓ} C(m, j) ≤ Γ^B_{κ,ℓ}(subsetPoly m κ)` (Def. 12). -/
theorem subset_def12_lower (c : Conv) (B : BlockPartition (m + m)) (κ ℓ : ℕ) (hκ : κ ≤ m) :
    m.choose κ * ∑ j ∈ Finset.range (ℓ + 1), m.choose j
      ≤ def12Rank c B κ ℓ (subsetPoly (F := F) m κ) := by
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset (Fin m), S0.card = κ :=
    Finset.exists_subset_card_eq (s := Finset.univ) (by simpa using hκ) |>.imp fun _ h => h.2
  -- the degree guard does not fire
  have hguard : ¬ (subsetPoly (F := F) m κ).totalDegree + ℓ < κ := by
    intro hlt
    have h0 := iterDerivList_eq_zero_of_lt (xList S0) (subsetPoly (F := F) m κ) (by
      rw [xList, length_toList_toMultiset, xExp_weight, hS0]; omega)
    have h1 := pderivMulti_subsetPoly (F := F) κ S0 hS0
    unfold pderivMulti at h1
    change iterDerivList (xList S0) _ = _ at h1
    rw [h0] at h1
    have := congrArg (yEval (F := F) S0) h1
    rw [map_zero, yEval_delta, if_pos rfl] at this
    exact zero_ne_one this
  unfold def12Rank
  rw [if_neg hguard]
  let η := {S : Finset (Fin m) // S.card = κ}
  let ι : η → Type := fun _ => {A : Finset (Fin m) // A.card ≤ ℓ}
  let v : (Σ S : η, ι S) → MvPolynomial (Fin (m + m)) F := fun a => xMon a.2.1 * delta a.1.1
  -- linear independence via Ψ q = (yEval T q)_T
  let Ψ : MvPolynomial (Fin (m + m)) F →ₗ[F] (η → MvPolynomial (Fin (m + m)) F) :=
    LinearMap.pi (fun T : η => (yEval (F := F) T.1).toLinearMap)
  have hxli : ∀ S : η, LinearIndependent F (fun A : ι S => (xMon (F := F) A.1)) := by
    intro S
    have := (MvPolynomial.basisMonomials (Fin (m + m)) F).linearIndependent.comp
      (fun A : ι S => xExp A.1) (fun a b hab => Subtype.ext (xExp_injective hab))
    convert this using 1
  have hli : LinearIndependent F v := by
    apply LinearIndependent.of_comp Ψ
    have hc : Ψ ∘ v = fun a => Pi.single a.1 (xMon (F := F) a.2.1) := by
      funext a; funext T
      simp only [Function.comp_apply, Ψ, v, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
        map_mul, yEval_xMon, yEval_delta, Pi.single_apply]
      by_cases h : a.1 = T
      · subst h; simp
      · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg (Ne.symm h), mul_zero]
    rw [hc]
    exact Pi.linearIndependent_single (fun S (A : ι S) => xMon (F := F) A.1) hxli
  have hsub : Submodule.span F (Set.range v) ≤ def12Span c B κ ℓ (subsetPoly (F := F) m κ) := by
    apply Submodule.span_le.mpr
    rintro q ⟨⟨S, A⟩, rfl⟩
    apply Submodule.subset_span
    have hτ : weight (xExp S.1) = κ := by rw [xExp_weight, S.2]
    have hu : weight (xExp A.1) ≤ ℓ := by rw [xExp_weight]; exact A.2
    refine ⟨xExp S.1, xExp A.1, hτ, blockCondition_vacuous B _ hτ, hu, ?_⟩
    rw [row_colRestrict_eq c _ _ _ hτ hu, pderivMulti_subsetPoly κ S.1 S.2]
    change xMon A.1 * delta S.1 = _
    exact (convML_of_MLSupp c (row_MLSupp A.1 S.1)).symm
  have h1 := Submodule.finrank_mono hsub
  rw [finrank_span_eq_card hli] at h1
  refine le_trans (le_of_eq ?_) h1
  have e1 : Fintype.card {A : Finset (Fin m) // A.card ≤ ℓ} = ∑ j ∈ Finset.range (ℓ + 1), m.choose j := by
    rw [Fintype.card_subtype, card_small_finsets]
  have e2 : Fintype.card η = m.choose κ := by
    change Fintype.card {S : Finset (Fin m) // S.card = κ} = _
    rw [Fintype.card_finset_len, Fintype.card_fin]
  rw [Fintype.card_sigma]
  change _ = ∑ _S : η, Fintype.card {A : Finset (Fin m) // A.card ≤ ℓ}
  rw [Finset.sum_const, Finset.card_univ, e1, e2, smul_eq_mul]

/-- **Lemma 18 fails for an infinite family of Boolean (characteristic) polynomials**, under
both conventions: for `N = 2m`, `m ≥ 4`, `κ = ℓ = 1`, Lemma 18's bound `C(N,ℓ)·2^ℓ` is exceeded. -/
theorem lemma18_fails_subset_family (c : Conv) (B : BlockPartition (m + m)) (hm : 4 ≤ m) :
    (m + m).choose 1 * 2 ^ 1 < def12Rank c B 1 1 (subsetPoly (F := F) m 1) := by
  have h := subset_def12_lower (F := F) c B 1 1 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, zero_add] at h
  rw [Nat.choose_one_right]
  refine lt_of_lt_of_le ?_ h
  nlinarith

end Subset

end Def12Measure

#print axioms Def12Measure.blockCondition_vacuous
#print axioms Def12Measure.pderiv_comm
#print axioms Def12Measure.iterDerivList_perm
#print axioms Def12Measure.pderivMulti_ofList
#print axioms Def12Measure.row_colRestrict_eq
#print axioms Def12Measure.def12Span_finiteDimensional
#print axioms Def12Measure.def12Rank_le_columns
#print axioms Def12Measure.lean_le_def12_drop
#print axioms Def12Measure.andPoly_eq_prod
#print axioms Def12Measure.card_small_finsets
#print axioms Def12Measure.and_def12_lower
#print axioms Def12Measure.pderivMulti_subsetPoly
#print axioms Def12Measure.subset_def12_lower
#print axioms Def12Measure.lemma18_fails_subset_family
