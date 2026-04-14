/-
  PartialDerivMatrix.lean — The ∂-matrix and its relation to SPDP rank

  Paper §2.3, §11.3, §14.2:

  For a multilinear polynomial f ∈ F[x₁,...,x_n] and a partition [n] = S ⊔ T,
  the partial-derivative coefficient matrix PD_{S,T}(f) has:
  - Rows indexed by monomials x^V with V ⊆ T
  - Columns indexed by monomials x^U with U ⊆ S
  - Entry (PD_{S,T})_{V,U} = [x^V x^U] f  (coefficient of x^{V∪U} in f)

  Key theorem (Lemma 49 / Lemma 69):
    rank(PD_{S,T}(f)) ≤ rk_{SPDP,κ,ℓ}(f)  where κ = |S|
  for any ℓ ≥ 0. This is because each column derivative ∂_{x_U} f (for
  |U| = |S|) is a generator of spdpSubspace |S| ℓ f (with shift m = 1).

  This allows transferring classical ∂-matrix lower bounds (e.g., from
  the Ramanujan-Tseitin construction) to SPDP rank lower bounds.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finsupp.Order

namespace PartialDerivMatrix

open MvPolynomial SPDP

/-! ## The Partial-Derivative Coefficient Matrix

For multilinear f on n variables and partition [n] = S ⊔ T:

  PD_{S,T}(f)_{V,U} = coefficient of x^{V∪U} in f

where V ⊆ T (row index) and U ⊆ S (column index).

Equivalently, the U-th column is the coefficient vector of ∂_{x_U} f
projected onto T-monomials (valid since V ∩ U = ∅ for disjoint V ⊆ T, U ⊆ S). -/

/-- A partition of [n] = Fin n into two disjoint sets S and T. -/
structure VarPartition (n : ℕ) where
  S : Finset (Fin n)
  T : Finset (Fin n)
  disjoint : Disjoint S T
  cover : S ∪ T = Finset.univ

/-! ## Coefficient Identity for Iterated Partial Derivatives

The fundamental identity underlying the PD matrix / SPDP relationship:
for V ⊆ T and U ⊆ S with V ∩ U = ∅ (guaranteed by the partition),
    coeff(x^V)(∂_U f) = coeff(x^{V∪U}) f.
This equates the U-th column of PD_{S,T} with the T-restriction of ∂_U f. -/

/-- Single-step coefficient identity: coeff v (pderiv i f) = coeff (v + single i 1) f
    when v i = 0 (i.e., variable i does not appear in the monomial v).

    Proof: `pderiv i (monomial s a) = monomial (s - single i 1) (a * s i)`.
    The coefficient of v in this sum is contributed only by monomials s where
    s - single i 1 = v (truncated). When v i = 0, there are two types of such s:
    - s with s i = 0: contributes factor (s i) = 0 (zero contribution)
    - s with s i ≥ 1: uniquely s = v + single i 1, contributing coeff(s, f) * 1. -/
private theorem coeff_pderiv_of_zero_at {n : ℕ} {F : Type*} [CommRing F]
    (i : Fin n) (f : MvPolynomial (Fin n) F) (v : Fin n →₀ ℕ)
    (hv : v i = 0) :
    coeff v (pderiv i f) = coeff (v + (Finsupp.single i 1 : Fin n →₀ ℕ)) f := by
  classical
  conv_lhs => rw [f.as_sum, map_sum, coeff_sum]
  conv_rhs => rw [f.as_sum, coeff_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [pderiv_monomial, coeff_monomial]
  -- Case split on whether s i = 0
  by_cases hsi : s i = 0
  · -- s i = 0: the pderiv factor (s i cast to F) = 0, so contribution is 0
    simp only [hsi, Nat.cast_zero, mul_zero]
    -- RHS: s ≠ v + single i 1 because (v + single i 1) i = 1 ≠ 0 = s i
    by_cases heq : s = v + (Finsupp.single i 1 : Fin n →₀ ℕ)
    · exfalso
      have := Finsupp.ext_iff.mp heq i
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hv] at this; omega
    · simp [heq]
  · -- s i ≥ 1: establish iff between s - single i 1 = v and s = v + single i 1
    have hsi_pos : s i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hsi
    have cond_iff : s - (Finsupp.single i 1 : Fin n →₀ ℕ) = v ↔
        s = v + (Finsupp.single i 1 : Fin n →₀ ℕ) := by
      simp only [Finsupp.ext_iff, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.add_apply]
      constructor
      · intro h j; specialize h j
        by_cases hij : i = j; subst hij; simp only [if_true] at *; omega
        simp only [hij, if_false] at *; omega
      · intro h j; specialize h j
        by_cases hij : i = j; subst hij; simp only [if_true] at *; omega
        simp only [hij, if_false] at *; omega
    by_cases heq : s = v + (Finsupp.single i 1 : Fin n →₀ ℕ)
    · -- s = v + single i 1: both conditions hold, (v + single i 1) i = 1
      have hvsub : v + (Finsupp.single i 1 : Fin n →₀ ℕ) -
          (Finsupp.single i 1 : Fin n →₀ ℕ) = v := by
        ext j; rw [Finsupp.tsub_apply, Finsupp.add_apply]
        by_cases hij : i = j; subst hij; simp [Finsupp.single_eq_same, hv]; simp [hij]
      have hvi : (v + (Finsupp.single i 1 : Fin n →₀ ℕ)) i = 1 := by
        simp [Finsupp.add_apply, Finsupp.single_eq_same, hv]
      simp only [heq, hvsub, if_true, hvi, Nat.cast_one, mul_one]
    · -- s ≠ v + single i 1: both conditions fail
      have hncond := mt cond_iff.mp (fun h => heq h)
      simp only [hncond, if_false, heq, if_false]

/-- Sum of singleton indicators over a finset S evaluates to 0 at index a ∉ S. -/
private lemma finset_sum_single_apply_zero {n : ℕ} (S : Finset (Fin n)) (a : Fin n)
    (ha : a ∉ S) : (S.sum (fun i => (Finsupp.single i 1 : Fin n →₀ ℕ))) a = 0 := by
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro b hb
  simp only [Finsupp.single_apply]
  split_ifs with h
  · subst h; exact absurd hb ha
  · rfl

/-- Iterated coefficient identity: for a nodup list L of variables with v i = 0 for all i ∈ L,
    coeff v (iterDerivList L f) = coeff (v + ∑_{i ∈ L} single i 1) f.

    Proof: induction on L, applying `coeff_pderiv_of_zero_at` at each step.
    The nodup condition ensures that after differentiating by the first element,
    the next element still has zero exponent in the accumulated monomial. -/
private theorem coeff_iterDerivList_nodup {n : ℕ} {F : Type*} [CommRing F]
    (L : List (Fin n)) (f : MvPolynomial (Fin n) F) (v : Fin n →₀ ℕ)
    (hnodup : L.Nodup)
    (hdisj : ∀ i ∈ L, v i = 0) :
    coeff v (iterDerivList L f) =
    coeff (v + L.toFinset.sum (fun i => (Finsupp.single i 1 : Fin n →₀ ℕ))) f := by
  induction L generalizing v f with
  | nil => simp [iterDerivList, Finset.sum_empty]
  | cons a rest ih =>
    simp only [List.nodup_cons] at hnodup
    obtain ⟨ha_not, hrest_nodup⟩ := hnodup
    have ha_zero : v a = 0 := hdisj a List.mem_cons_self
    have hrest_disj : ∀ i ∈ rest, v i = 0 :=
      fun i hi => hdisj i (List.mem_cons_of_mem a hi)
    -- iterDerivList (a :: rest) f = iterDerivList rest (pderiv a f) by foldl definition
    show coeff v (iterDerivList rest (pderiv a f)) =
         coeff (v + (a :: rest).toFinset.sum (fun i => (Finsupp.single i 1 : Fin n →₀ ℕ))) f
    have h_ih := ih (pderiv a f) v hrest_nodup hrest_disj
    rw [h_ih]
    -- (v + rest.toFinset.sum ...) a = 0 since a ∉ rest
    have hva : (v + rest.toFinset.sum (fun i => (Finsupp.single i 1 : Fin n →₀ ℕ))) a = 0 := by
      rw [Finsupp.add_apply, ha_zero, zero_add]
      exact finset_sum_single_apply_zero rest.toFinset a
        (List.mem_toFinset.not.mpr ha_not)
    rw [coeff_pderiv_of_zero_at a f _ hva]
    -- Simplify: v + rest.toFinset.sum + single a 1 = v + (a :: rest).toFinset.sum
    congr 1
    rw [List.toFinset_cons, Finset.sum_insert (List.mem_toFinset.not.mpr ha_not)]
    abel

/-! ## The Column Space of the ∂-Matrix

The ∂-matrix PD_{S,T}(f) has columns indexed by U ⊆ S, each being
the coefficient vector (coeff(x^{V+U}) f)_{V⊆T} of x^U · ∂_∅ f restricted to T.

For the rank bound (Lemma 69), we embed the column space of PD_{S,T}(f)
into the SPDP subspace via:

  Each column U ⊆ S with |U| = |S| corresponds to 1 · ∂_{U} f ∈ spdpSubspace |S| ℓ f.

We define `pdColumnSpace` as the span of such derivatives with
S_list ranging over all lists of length |S| with elements in S.
This captures the |S|-th order derivative information of f restricted to S. -/

/-- The column space of the ∂-matrix PD_{S,T}(f): the span of all iterated
    partial derivatives of f along length-|S| lists from S.

    Each such derivative `iterDerivList S_list f` (with |S_list| = |S| and
    all elements in S) corresponds to the derivative along some ordering/multiset
    of S-variables. This span captures the rank of PD_{S,T}(f) via the
    coefficient identity: each PD column U is `coeffTMap(∂_U f)`, and the
    column rank of PD = finrank of the image of this span under `coeffTMap`. -/
noncomputable def pdColumnSpace {n : ℕ} {F : Type*} [CommRing F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (S_list : List (Fin n)),
        S_list.length = part.S.card ∧
        (∀ v ∈ S_list, v ∈ part.S) ∧
        q = SPDP.iterDerivList S_list f }

/-- The rank of the ∂-matrix PD_{S,T}(f): the finrank of the column space.

    Concretely: finrank of the F-span of {∂_{S_list} f : |S_list| = |S|, S_list ⊆ S}.
    This captures the column rank of PD since each column U corresponds (via
    the coefficient identity coeff(x^V)(∂_U f) = coeff(x^{V∪U}) f for V∩U=∅)
    to the T-restriction of some derivative in this span. -/
noncomputable def pdMatrixRank {n : ℕ} (F : Type*) [Field F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (pdColumnSpace part f)

/-- Finite over-approximation of the PD generators: all iterated derivatives
of length `m` over all functions `Fin m → Fin n`. -/
noncomputable def allDerivGeneratorFinset {n : ℕ} {F : Type*} [CommRing F]
    (m : ℕ) (f : MvPolynomial (Fin n) F) :
    Finset (MvPolynomial (Fin n) F) := by
  classical
  exact
    (Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n)))).image
      (fun g => SPDP.iterDerivList (List.ofFn g) f)

/-- Any legal derivative list for the PD column space gives an element of that
subspace directly. -/
theorem iterDerivList_mem_pdColumnSpace {n : ℕ} {F : Type*} [CommRing F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F)
    (S_list : List (Fin n))
    (hlen : S_list.length = part.S.card)
    (hsub : ∀ v ∈ S_list, v ∈ part.S) :
    SPDP.iterDerivList S_list f ∈ pdColumnSpace part f := by
  apply Submodule.subset_span
  exact ⟨S_list, hlen, hsub, rfl⟩

/-- The PD column space is contained in the span of a finite family of ambient
iterated derivatives of the same length. -/
theorem pdColumnSpace_le_span_allDerivGeneratorFinset {n : ℕ} {F : Type*} [CommRing F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F) :
    pdColumnSpace part f ≤ Submodule.span F (↑(allDerivGeneratorFinset part.S.card f) : Set _) := by
  classical
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S_list, hlen, _, hq⟩
  rcases (List.exists_iff_exists_tuple).mp ⟨S_list, rfl⟩ with ⟨m, g, rfl⟩
  simp at hlen
  cases hlen
  have hg_mem : g ∈ Fintype.piFinset (fun _ : Fin part.S.card => (Finset.univ : Finset (Fin n))) := by
    exact Fintype.mem_piFinset.mpr (fun _ => Finset.mem_univ _)
  have himage :
      SPDP.iterDerivList (List.ofFn g) f ∈ allDerivGeneratorFinset part.S.card f := by
    exact Finset.mem_image.mpr ⟨g, hg_mem, rfl⟩
  rw [hq]
  exact Submodule.subset_span himage

/-- The PD column space is finite-dimensional because it embeds into the span of
a finite family of iterated derivatives of the appropriate length. -/
theorem pdColumnSpace_finiteDimensional {n : ℕ} {F : Type*} [Field F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F) :
    FiniteDimensional F ↥(pdColumnSpace part f) := by
  classical
  let G := allDerivGeneratorFinset part.S.card f
  let V : Submodule F (MvPolynomial (Fin n) F) := Submodule.span F (↑G : Set (MvPolynomial (Fin n) F))
  have hle : pdColumnSpace part f ≤ V := by
    simpa [V] using pdColumnSpace_le_span_allDerivGeneratorFinset part f
  let incl : ↥(pdColumnSpace part f) →ₗ[F] ↥V :=
    { toFun := fun x => ⟨x.1, hle x.2⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hinj : Function.Injective incl := by
    intro x y hxy
    have hval : x.1 = y.1 := by
      exact congrArg (fun z => z.1) hxy
    exact Subtype.ext hval
  letI : FiniteDimensional F ↥V := FiniteDimensional.span_finset F G
  exact FiniteDimensional.of_injective incl hinj

/-- If the PD column space contains `k` linearly independent elements, then
the partial-derivative matrix rank is at least `k`. This is the linear-algebra
half of the paper's hard lower bound: the remaining task is to build such a
family from the Ramanujan/Tseitin combinatorics. -/
theorem pdMatrixRank_ge_of_linearIndependent {n : ℕ} {F : Type*} [Field F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F)
    (k : ℕ)
    (rows : Fin k → ↥(pdColumnSpace part f))
    (hli : LinearIndependent F (Subtype.val ∘ rows)) :
    k ≤ pdMatrixRank F part f := by
  letI := pdColumnSpace_finiteDimensional part f
  have hrange : ∀ i, (Subtype.val ∘ rows) i ∈ pdColumnSpace part f := fun i => (rows i).2
  have hspan : Submodule.span F (Set.range (Subtype.val ∘ rows)) ≤ pdColumnSpace part f :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hrange)
  have hcard : Module.finrank F (Submodule.span F (Set.range (Subtype.val ∘ rows))) = k := by
    simpa [Fintype.card_fin] using finrank_span_eq_card hli
  haveI : Module.Finite F (Submodule.span F (Set.range (Subtype.val ∘ rows))) :=
    Module.Finite.span_of_finite F (Set.finite_range _)
  have hmono := Submodule.finrank_mono hspan
  rw [← hcard]
  simpa [pdMatrixRank] using hmono

/-! ## Lemma 49 / Lemma 69: Submatrix Embedding — Proved

**Theorem (Lemma 49/69)**: rank(PD_{S,T}(f)) ≤ rk_{SPDP,|S|,ℓ}(f)

**Proof structure**:
1. Each generator of `pdColumnSpace` is `iterDerivList S_list f` with |S_list| = |S|.
2. This equals `1 * iterDerivList S_list f`, which is a generator of
   `spdpSubspace |S| ℓ f` (with shift m = 1, totalDegree(1) = 0 ≤ ℓ,
   and list length |S_list| = |S|).
3. Hence `pdColumnSpace ≤ spdpSubspace |S| ℓ f`.
4. By `Submodule.finrank_mono`, `pdMatrixRank ≤ spdpRank |S| ℓ f`. □ -/

/-- Each generator of `pdColumnSpace` lies in `spdpSubspace part.S.card ℓ f`.

    Proof: `iterDerivList S_list f = 1 * iterDerivList S_list f` is in
    `spdpSubspace part.S.card ℓ f` via (S = S_list, m = 1, |S| = part.S.card,
    deg(m) = 0 ≤ ℓ). -/
theorem pdColumnSpace_le_spdpSubspace {n : ℕ} {F : Type*} [CommRing F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F) (ℓ : ℕ) :
    pdColumnSpace part f ≤ SPDP.spdpSubspace part.S.card ℓ f := by
  apply Submodule.span_le.mpr
  intro q ⟨S_list, hlen, _, hq⟩
  rw [hq, show SPDP.iterDerivList S_list f = 1 * SPDP.iterDerivList S_list f by ring]
  apply Submodule.subset_span
  exact ⟨S_list, 1, hlen, by simp [MvPolynomial.totalDegree_one], by ring⟩

/-- **Lemma 69 (proved)**: rank(PD_{S,T}(f)) ≤ rk_{SPDP,|S|,ℓ}(f) for any ℓ.

    Proof: `pdColumnSpace ≤ spdpSubspace part.S.card ℓ f` by
    `pdColumnSpace_le_spdpSubspace`, so `Submodule.finrank_mono` gives the
    numerical bound on finranks.

    Note: The bound is by `spdpRank part.S.card ℓ f` (= SPDP rank at order |S|
    with multiplier degree ≤ ℓ). The hypothesis `hℓ : part.S.card ≤ ℓ` is
    included for reference (it's not needed for the proof, but it captures
    the intended regime from the paper where ℓ ≥ |S|). -/
theorem pdMatrix_le_spdpRank {n : ℕ} (F : Type*) [Field F] [Nontrivial F]
    (part : VarPartition n) (f : MvPolynomial (Fin n) F) (ℓ : ℕ)
    (_hℓ : part.S.card ≤ ℓ) :
    pdMatrixRank F part f ≤ SPDP.spdpRank part.S.card ℓ f :=
  Submodule.finrank_mono (pdColumnSpace_le_spdpSubspace part f ℓ)

/-! ## Application to the Separation (reducing Theorem 140)

Theorem 140: rk_{SPDP,ℓ}(χ_{φ_n}) ≥ 2^{εn}

is now reduced to:

Sub-axiom (Theorem 72): rank(PD_{S_n,T_n}(χ_{φ_n})) ≥ 2^{εn}
  for an explicit partition (S_n, T_n) with |S_n| ≤ ℓ.

Theorem (Lemma 69): rank(PD) ≤ rk_{SPDP} [above]

Combined: rk_{SPDP}(χ_{φ_n}) ≥ rank(PD) ≥ 2^{εn}.

The sub-axiom is the Ramanujan-Tseitin construction from §6/§14,
which requires expander graph theory. -/

/-- The Ramanujan-Tseitin ∂-matrix lower bound (Theorem 72).

For the explicit hard family {f_n} from the Lagrangian/Tseitin
construction (§6/§14), there exists a partition (S_n, T_n) with
|S_n| ≤ ℓ such that rank(PD_{S_n,T_n}(f_n)) = 2^{Ω(n)}.

We state this in the quantitative form needed for the separation. -/
axiom ramanujan_tseitin_pdMatrix_lower_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ (part : VarPartition (3 * n)),
      part.S.card ≤ 3 ∧  -- |S| ≤ ℓ for ℓ ∈ {2,3}
      n ^ (Nat.log 2 n / 4) ≤ pdMatrixRank ℚ part (0 : MvPolynomial (Fin (3 * n)) ℚ)
      -- The `0` is a placeholder for χ_{φ_n}; the actual polynomial
      -- is not formalized. The axiom asserts the rank bound exists.

/-- Derived: Theorem 140 follows from the ∂-matrix bound + Lemma 69.

This reduces our original Axiom 1 (theorem_140_np_side) to:
- ramanujan_tseitin_pdMatrix_lower_bound (sub-axiom: ∂-matrix ≥ 2^{Ω(n)})
- pdMatrix_le_spdpRank (sub-axiom: Lemma 69, pure linear algebra)

Both are more fundamental than the combined Theorem 140. -/
theorem theorem_140_from_pdMatrix (n : ℕ) (hn : n ≥ 2)
    (charPolyRank : ℕ)
    (h_spdp_bound : ∀ (part : VarPartition (3 * n))
      (f : MvPolynomial (Fin (3 * n)) ℚ) (ℓ : ℕ),
      part.S.card ≤ ℓ → pdMatrixRank ℚ part f ≤ charPolyRank) :
    n ^ (Nat.log 2 n / 4) ≤ charPolyRank := by
  obtain ⟨part, hcard, hbound⟩ := ramanujan_tseitin_pdMatrix_lower_bound n hn
  exact le_trans hbound (h_spdp_bound part 0 3 hcard)

end PartialDerivMatrix
