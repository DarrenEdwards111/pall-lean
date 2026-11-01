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
