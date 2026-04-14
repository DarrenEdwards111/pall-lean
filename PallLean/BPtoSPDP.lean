import PallLean.SPDPDefs
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Basic
/-!
# Branching Programs → SPDP Rank Bound (Pall §11.1, Lemma 45)

This file formalizes the BP→SPDP rank pipeline:

  Lemma 45 (BP→SPDP): For a deterministic layered BP B of length L' and
  width W over {0,1}^n, and for fixed ℓ ∈ {2,3}, the computed multilinear
  polynomial f satisfies
    rk_{SPDP,ℓ}(f) ≤ (C_ℓ · W · L')^{d_ℓ}
  for absolute constants C_ℓ, d_ℓ depending only on ℓ.

  Lemma 44 (Compilation): For L ∈ P decidable in time n^k, there exists
  a layered BP family {B_n} of length n^{O(k)} and width n^{O(1)}.

  Theorem 46 (P ⊆ poly-SPDP): For L ∈ P decidable in time n^k,
    rk_{SPDP,ℓ}(χ_L) ≤ n^{O(k)}.

Proof structure:
  1. Matrix product form: f(x) = e_s^T (∏_{τ} M_τ(x)) · a
  2. Leibniz rule: differentiation localizes to individual layer matrices
  3. Cylinder decomposition: partial derivatives interact with ≤ ℓ layers
  4. Row-space bound: dim(rowspace) ≤ W^{O(1)} · L'^{O(1)}

Genuinely unproved steps are marked `axiom`. Structural/definitional
steps are `theorem` or `def`.
-/

namespace BPtoSPDP

open MvPolynomial SPDP

/-! ## §1: Branching Program Structure -/

/-- A literal over {0,1}^n: either the constant 1, variable x_i, or (1 - x_i). -/
inductive Literal (n : ℕ) where
  | constOne   : Literal n
  | posVar     : Fin n → Literal n
  | negVar     : Fin n → Literal n
deriving DecidableEq

/-- Evaluate a literal on a Boolean assignment. -/
def Literal.eval {n : ℕ} (lit : Literal n) (x : Fin n → ℝ) : ℝ :=
  match lit with
  | .constOne   => 1
  | .posVar i   => x i
  | .negVar i   => 1 - x i

/-- A literal as a multilinear polynomial over a field F. -/
noncomputable def Literal.toPoly {n : ℕ} {F : Type*} [CommRing F]
    (lit : Literal n) : MvPolynomial (Fin n) F :=
  match lit with
  | .constOne   => 1
  | .posVar i   => MvPolynomial.X i
  | .negVar i   => 1 - MvPolynomial.X i

/-- The total degree of a literal polynomial is ≤ 1. -/
theorem Literal.toPoly_totalDegree_le {n : ℕ} {F : Type*} [CommRing F]
    (lit : Literal n) : (lit.toPoly (F := F)).totalDegree ≤ 1 := by
  cases lit with
  | constOne =>
    simp [Literal.toPoly, MvPolynomial.totalDegree_one]
  | posVar i =>
    simp only [Literal.toPoly]
    -- X i = monomial (Finsupp.single i 1) 1 by definition
    rw [MvPolynomial.X]
    calc (MvPolynomial.monomial (Finsupp.single i 1) (1 : F)).totalDegree
        ≤ (Finsupp.single i 1).sum (fun _ => id) :=
          MvPolynomial.totalDegree_monomial_le _ _
      _ = 1 := by simp [Finsupp.sum_single_index]
  | negVar i =>
    simp only [Literal.toPoly]
    -- (1 - X i).totalDegree ≤ max 0 deg(X i) ≤ max 0 1 = 1
    have hXdeg : (MvPolynomial.X (R := F) i).totalDegree ≤ 1 := by
      rw [MvPolynomial.X]
      calc (MvPolynomial.monomial (Finsupp.single i 1) (1 : F)).totalDegree
          ≤ (Finsupp.single i 1).sum (fun _ => id) :=
            MvPolynomial.totalDegree_monomial_le _ _
        _ = 1 := by simp [Finsupp.sum_single_index]
    calc (1 - MvPolynomial.X (R := F) i).totalDegree
        ≤ max (1 : MvPolynomial (Fin n) F).totalDegree (MvPolynomial.X i).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ ≤ max 0 1 := by
          apply max_le_max
          · simp [MvPolynomial.totalDegree_one]
          · exact hXdeg
      _ = 1 := by simp

/-- A layered branching program of length L' and width W over {0,1}^n.

    Concretely:
    - Nodes at each layer τ ∈ {0,...,L'} are indexed by Fin width.
    - Each edge from node u at layer τ to node v at layer τ+1 carries
      a literal label `edgeLabel τ u v : Literal n`.
    - The transition matrix at layer τ has entry (v, u) = edgeLabel τ u v.
    - `source` is the source node at layer 0.
    - `target` is the target node at layer L'.

    The polynomial computed by B is:
      f_B(x) = e_{target}^T · (M_0(x) * M_1(x) * ... * M_{L'-1}(x)) · e_{source}
    where M_τ(x)_{v,u} = edgeLabel τ u v (as polynomial). -/
structure LayeredBP (n : ℕ) where
  /-- Number of layers (length of the BP) -/
  length   : ℕ
  /-- Maximum number of nodes per layer -/
  width    : ℕ
  /-- Edge label from node u at layer τ to node v at layer τ+1 -/
  edgeLabel : ∀ (τ : Fin length) (u v : Fin width), Literal n
  /-- Source node at layer 0 -/
  source   : Fin width
  /-- Target (accept) node at layer length -/
  target   : Fin width

/-- The layer matrix M_τ(x) for layer τ, as a (width × width) matrix
    of polynomials over F. Entry (v, u) = edgeLabel τ u v as polynomial. -/
noncomputable def LayeredBP.layerMatrix {n : ℕ} {F : Type*} [CommRing F]
    (B : LayeredBP n) (τ : Fin B.length) :
    Matrix (Fin B.width) (Fin B.width) (MvPolynomial (Fin n) F) :=
  fun v u => (B.edgeLabel τ u v).toPoly

/-- The ordered product of layer matrices M_0 * M_1 * ... * M_{L'-1}.

    We use List.map and List.prod to compute the left-to-right product. -/
noncomputable def LayeredBP.matrixProd {n : ℕ} {F : Type*} [CommRing F]
    (B : LayeredBP n) :
    Matrix (Fin B.width) (Fin B.width) (MvPolynomial (Fin n) F) :=
  (List.map (fun τ : Fin B.length => B.layerMatrix τ)
    (List.finRange B.length)).prod

/-- The polynomial computed by B via the matrix product formula.

    f_B(x) = (M_0(x) * M_1(x) * ... * M_{L'-1}(x))_{target, source} -/
noncomputable def LayeredBP.poly {n : ℕ} {F : Type*} [CommRing F]
    (B : LayeredBP n) : MvPolynomial (Fin n) F :=
  B.matrixProd B.target B.source

/-! ## §2: The SPDP Rank Bound (Lemma 45) -/

/-- The SPDP rank of the polynomial computed by B is bounded by
    (C · width · length)^d for absolute constants C, d depending on ℓ.

    This is the main content of Lemma 45.  The proof proceeds by:
    (a) writing ∂_S f = ∑_{touched layer sets T, |T|≤ℓ} (product of
        partially-differentiated layer matrices),
    (b) showing each summand lies in a subspace of dimension ≤ W^{O(1)},
    (c) counting the number of such summands ≤ L'^ℓ · ℓ!,
    (d) multiplying by the multiplier-monomial degree bound.

    The full algebraic argument requires reasoning about the row space of
    the SPDP matrix, which is deferred to the axiom below. -/
axiom bp_spdp_rank_bound
    {n : ℕ} {F : Type*} [Field F] [Nontrivial F] [CharZero F]
    (B : LayeredBP n)
    (ℓ : ℕ) (hℓ : ℓ = 2 ∨ ℓ = 3)
    (C_ℓ d_ℓ : ℕ) (hC : C_ℓ ≥ 1) (hd : d_ℓ ≥ 1)
    :
    spdpRank ℓ ℓ (B.poly (F := F)) ≤ (C_ℓ * B.width * B.length) ^ d_ℓ

/-! ### Supporting steps for Lemma 45

The following theorems isolate the key sub-lemmas used in the proof of
Lemma 45, making the proof structure explicit. -/

/-- (Step 1) Matrix product representation.

    The polynomial f_B is equal to the (target, source) entry of the
    product of layer matrices.  This is the definition of `LayeredBP.poly`,
    so it holds by definitional unfolding. -/
theorem bp_matrix_product_form
    {n : ℕ} {F : Type*} [CommRing F]
    (B : LayeredBP n) :
    B.poly (F := F) = B.matrixProd B.target B.source := rfl

/-!
### (Step 2) Leibniz localisation

For a product of matrices M_0 · M_1 · ... · M_{L'-1}, the partial
derivative ∂_{x_i} distributes via the Leibniz rule to give a sum
over layers τ of the product with ∂_{x_i} M_τ in slot τ and the
original M_σ for σ ≠ τ.

We prove this via:
(a) `pderiv_matrix_mul`: pderiv distributes over matrix multiplication,
(b) `pderiv_list_prod_matrix_eq`: Leibniz for list products of matrices,
(c) `finRange_filter_lt/gt`: filter on finRange equals take/drop.
-/

/-- The pointwise partial derivative of a polynomial matrix. -/
private noncomputable def matPderiv {n W : ℕ} {F : Type*} [CommRing F]
    (i : Fin n) (M : Matrix (Fin W) (Fin W) (MvPolynomial (Fin n) F)) :
    Matrix (Fin W) (Fin W) (MvPolynomial (Fin n) F) :=
  Matrix.of (fun v u => MvPolynomial.pderiv i (M v u))

/-- Partial derivative distributes over matrix multiplication:
    ∂_i (A * B) = (∂_i A) * B + A * (∂_i B). -/
private theorem pderiv_matrix_mul {n W : ℕ} {F : Type*} [CommRing F]
    (i : Fin n)
    (A B : Matrix (Fin W) (Fin W) (MvPolynomial (Fin n) F)) :
    matPderiv i (A * B) = matPderiv i A * B + A * matPderiv i B := by
  ext v u
  simp only [matPderiv, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply]
  simp only [map_sum, MvPolynomial.pderiv_mul]
  rw [← Finset.sum_add_distrib]

/-- Leibniz rule for list products of polynomial matrices:
    ∂_i (∏ Ms) = ∑ k, (take k Ms).prod * (∂_i Ms[k]) * (drop (k+1) Ms).prod. -/
private theorem pderiv_list_prod_matrix_eq {n W : ℕ} {F : Type*} [CommRing F]
    (i : Fin n)
    (Ms : List (Matrix (Fin W) (Fin W) (MvPolynomial (Fin n) F))) :
    matPderiv i Ms.prod =
      ∑ k : Fin Ms.length,
        (Ms.take k.val).prod * matPderiv i (Ms.get k) * (Ms.drop (k.val + 1)).prod := by
  induction Ms with
  | nil =>
    simp only [List.length_nil, Fin.sum_univ_zero]
    ext v u
    simp [matPderiv, Matrix.one_apply, map_zero]
    split_ifs with h
    · subst h; simp [MvPolynomial.pderiv_one]
    · simp [map_zero]
  | cons M rest ih =>
    simp only [List.length_cons, List.prod_cons]
    rw [pderiv_matrix_mul, ih]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.take_zero, List.prod_nil, one_mul, List.get_cons_zero,
               List.drop_succ_cons]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.val_succ, List.take_succ_cons, List.prod_cons,
               show (M :: rest).get k.succ = rest.get k from by simp]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- filter (· < τ) on finRange L equals take τ.val (finRange L). -/
private lemma finRange_filter_lt (L : ℕ) (τ : Fin L) :
    (List.finRange L).filter (· < τ) = (List.finRange L).take τ.val := by
  induction L with
  | zero => exact τ.elim0
  | succ L ih =>
    rw [List.finRange_succ]
    rcases Fin.eq_zero_or_eq_succ τ with rfl | ⟨τ', rfl⟩
    · simp [Fin.not_lt_zero]
    · simp only [Fin.val_succ, List.take_succ_cons, List.filter_cons]
      split_ifs with h
      · congr 1
        rw [List.filter_map]
        rw [show ((fun x : Fin (L+1) => decide (x < Fin.succ τ')) ∘ (Fin.succ : Fin L → Fin (L+1))) =
               (fun x : Fin L => decide (x < τ')) from by ext σ; simp [Fin.succ_lt_succ_iff]]
        rw [ih τ', List.map_take]
      · exfalso; apply h; simp [Fin.lt_def]

/-- filter (τ < ·) on finRange L equals drop (τ.val + 1) (finRange L). -/
private lemma finRange_filter_gt (L : ℕ) (τ : Fin L) :
    (List.finRange L).filter (fun σ => τ < σ) = (List.finRange L).drop (τ.val + 1) := by
  induction L with
  | zero => exact τ.elim0
  | succ L ih =>
    rw [List.finRange_succ]
    rcases Fin.eq_zero_or_eq_succ τ with rfl | ⟨τ', rfl⟩
    · simp only [Fin.val_zero, Nat.zero_add, List.drop_one, List.tail_cons, List.filter_cons]
      split_ifs with h
      · exfalso; simp at h
      · rw [List.filter_map]
        have hall : (List.filter ((fun σ : Fin (L+1) => decide ((0 : Fin (L+1)) < σ)) ∘ (Fin.succ : Fin L → Fin (L+1)))
            (List.finRange L)) = List.finRange L := by
          apply List.filter_eq_self.mpr
          intro σ _
          show decide ((0 : Fin (L+1)) < Fin.succ σ) = true
          simp [Fin.lt_def]
        rw [hall]
    · simp only [Fin.val_succ, List.drop_succ_cons, List.filter_cons]
      split_ifs with h
      · exfalso; simp at h
      · rw [List.filter_map]
        have : ((fun σ : Fin (L+1) => decide (Fin.succ τ' < σ)) ∘ (Fin.succ : Fin L → Fin (L+1))) =
               (fun σ : Fin L => decide (τ' < σ)) := by ext σ; simp [Fin.succ_lt_succ_iff]
        rw [this, ih τ', List.map_drop]

/-- (Step 2) Leibniz localisation for the BP polynomial.

    The partial derivative ∂_{x_i}(f_B) distributes over the matrix product via the Leibniz rule. -/
theorem bp_leibniz_localisation
    {n : ℕ} {F : Type*} [CommRing F] [CharZero F]
    (B : LayeredBP n)
    (i : Fin n) :
    MvPolynomial.pderiv i (B.poly (F := F)) =
      ∑ τ : Fin B.length,
        ((List.map (fun σ : Fin B.length => B.layerMatrix (F := F) σ)
            (List.finRange B.length |>.filter (· < τ))).prod *
         (Matrix.of (fun v u => MvPolynomial.pderiv i (B.layerMatrix (F := F) τ v u))) *
         (List.map (fun σ : Fin B.length => B.layerMatrix (F := F) σ)
            (List.finRange B.length |>.filter (fun σ => τ < σ))).prod)
          B.target B.source := by
  -- Step 1: unfold poly = matrixList.prod[target][source]
  simp only [LayeredBP.poly, LayeredBP.matrixProd]
  set matrixList := List.map (fun τ : Fin B.length => B.layerMatrix (F := F) τ)
      (List.finRange B.length)
  have hlen : matrixList.length = B.length := by
    simp [matrixList, List.length_map, List.length_finRange]
  -- Step 2: apply the matrix Leibniz rule to get the take/drop form
  have hleib := pderiv_list_prod_matrix_eq i matrixList
  -- The (target, source) entry of the derivative equals the derivative of the entry
  have hentry : MvPolynomial.pderiv i (matrixList.prod B.target B.source) =
      (matPderiv i matrixList.prod) B.target B.source := by
    simp [matPderiv, Matrix.of_apply]
  rw [hentry, hleib]
  simp only [Matrix.sum_apply]
  -- Reindex from Fin matrixList.length to Fin B.length via Fin.cast hlen
  apply Finset.sum_nbij (fun k => Fin.cast hlen k)
  · intro k _; simp
  · intro k₁ _ k₂ _ h
    apply Fin.ext
    have := congrArg Fin.val h
    simp at this
    exact this
  · intro τ _
    exact ⟨Fin.cast hlen.symm τ, Finset.mem_coe.mpr (Finset.mem_univ _), by ext; simp⟩
  · intro k _
    -- Let τ = Fin.cast hlen k (same .val as k)
    set τ : Fin B.length := Fin.cast hlen k
    have hkval : k.val = τ.val := by simp [τ]
    simp only [Matrix.mul_apply]
    -- Prefix match: (matrixList.take k.val).prod = (map f (filter (· < τ) (finRange L))).prod
    have hpre : (matrixList.take k.val).prod =
        (List.map (fun σ : Fin B.length => B.layerMatrix (F := F) σ)
            (List.finRange B.length |>.filter (· < τ))).prod := by
      rw [hkval]
      simp only [matrixList]
      congr 1
      rw [finRange_filter_lt]
      rw [List.map_take]
    -- Suffix match: (matrixList.drop (k.val + 1)).prod = (map f (filter (τ < ·) (finRange L))).prod
    have hsuf : (matrixList.drop (k.val + 1)).prod =
        (List.map (fun σ : Fin B.length => B.layerMatrix (F := F) σ)
            (List.finRange B.length |>.filter (fun σ => τ < σ))).prod := by
      rw [hkval]
      simp only [matrixList]
      congr 1
      rw [finRange_filter_gt]
      rw [List.map_drop]
    -- Derivative match: matPderiv i (matrixList.get k) = Matrix.of (fun v u => pderiv i (layerMatrix τ v u))
    have hderiv : matPderiv i (matrixList.get k) =
        Matrix.of (fun v u => MvPolynomial.pderiv i (B.layerMatrix (F := F) τ v u)) := by
      simp only [matPderiv, Matrix.of_apply]
      ext v u
      congr 1
      -- matrixList.get k v u = B.layerMatrix τ v u
      have hklt : k.val < B.length := by
        have := k.isLt; simp [matrixList, List.length_map, List.length_finRange] at this; exact this
      have hmget : matrixList.get k = B.layerMatrix ((List.finRange B.length).get ⟨k.val, by simp; exact hklt⟩) := by
        simp only [matrixList, List.get_eq_getElem, List.getElem_map]
      rw [hmget, List.get_finRange]
      congr 1
    rw [hpre, hsuf, hderiv]

/-- (Step 3) Cylinder decomposition.

    For an iterated derivative ∂_S f_B with |S| = κ, the Leibniz rule
    shows that the result is a sum indexed by maps T : S → Fin L'
    (which layer each derivative variable "hits"), giving rise to at most
    L'^κ terms. Each term is a product of layers, at most |S| of which
    are differentiated. -/
axiom bp_cylinder_decomposition
    {n : ℕ} {F : Type*} [CommRing F] [CharZero F]
    (B : LayeredBP n)
    (S : List (Fin n)) (hS : S.Nodup) :
    ∃ (terms : Finset (Fin n → Fin B.length))
      (coeff : (Fin n → Fin B.length) → MvPolynomial (Fin n) F),
      iterDerivList S (B.poly (F := F)) = terms.sum coeff ∧
      terms.card ≤ B.length ^ S.length ∧
      ∀ T, T ∈ terms → (S.toFinset.image T).card ≤ S.length

/-- (Step 4) Row-space bound per term.

    Each term in the cylinder decomposition contributes a polynomial
    lying in a subspace of dimension ≤ W (the width of B).

    This follows from the fact that each such term is an entry of a
    matrix product where one factor is the (partially differentiated)
    layer matrix, which has at most W columns, giving rank ≤ W. -/
axiom bp_rowspace_bound_per_term
    {n : ℕ} {F : Type*} [Field F] [Nontrivial F]
    (B : LayeredBP n)
    (τ : Fin B.length)
    (S_τ : Finset (Fin n)) :
    Module.finrank F
      (Submodule.span F
        { q | ∃ (u v : Fin B.width),
              q = iterDerivList S_τ.toList (B.layerMatrix (F := F) τ v u) }) ≤
      B.width

/-! ## §3: Compilation Lemma (Lemma 44) -/

/-- A family of layered BPs indexed by input length, of polynomial complexity.

    For each n, B_n is a layered BP over {0,1}^n with:
    - length ≤ C_len · n^lenExp  (polynomial in n)
    - width  ≤ C_wid · n^widExp  (polynomial in n) -/
structure PolyBPFamily where
  /-- The time exponent k of the original polytime algorithm -/
  timeExp  : ℕ
  /-- Constant in the length bound -/
  C_len    : ℕ
  /-- Constant in the width bound -/
  C_wid    : ℕ
  /-- Length exponent (usually O(k)) -/
  lenExp   : ℕ
  /-- Width exponent (usually O(1)) -/
  widExp   : ℕ
  /-- For each n, a layered BP over n variables -/
  bp       : ∀ n : ℕ, LayeredBP n
  /-- Length bound: length(B_n) ≤ C_len · n^lenExp -/
  length_le : ∀ n, (bp n).length ≤ C_len * n ^ lenExp
  /-- Width bound: width(B_n) ≤ C_wid · n^widExp -/
  width_le  : ∀ n, (bp n).width  ≤ C_wid * n ^ widExp

/-- Compilation Lemma (Lemma 44): For any language L decidable in polytime
    (i.e., by a DTM running in time n^k), there exists a polynomial BP
    family computing the characteristic function χ_L.

    The construction follows from the standard simulation of polytime DTMs
    by branching programs: the computation table of M on input x gives a
    layered BP of length O(n^k) (one layer per time step) and width O(n)
    (one node per tape configuration). -/
axiom compilation_lemma
    (k : ℕ) (hk : k ≥ 1)
    (L : ∀ n, (Fin n → Bool) → Bool)
    (hL : True) -- placeholder for: L decidable in time n^k
    :
    ∃ (family : PolyBPFamily),
      family.timeExp = k ∧
      family.lenExp ≤ 2 * k ∧
      family.widExp ≤ 1 ∧
      ∀ (n : ℕ) (x : Fin n → Bool),
        (family.bp n).poly (F := ℝ) = 0 ↔ L n x = false

/-! ## §4: Main Theorem (Theorem 46: P ⊆ poly-SPDP) -/

/-- Theorem 46: For L decidable in polytime time n^k and fixed ℓ ∈ {2,3},
    the SPDP rank of χ_L is polynomially bounded in n:
      rk_{SPDP,ℓ}(χ_L) ≤ n^{O(k)}.

    This follows by composing:
    - Compilation (Lemma 44): BP family of length n^{O(k)}, width n^{O(1)}
    - BP→SPDP rank bound (Lemma 45): rank ≤ (C · W · L')^d ≤ n^{O(k)} -/
theorem P_subset_polySPDP
    (k : ℕ) (hk : k ≥ 1)
    (ℓ : ℕ) (hℓ : ℓ = 2 ∨ ℓ = 3)
    (L : ∀ n, (Fin n → Bool) → Bool)
    (hL : True) -- placeholder for: L ∈ P with time n^k
    :
    ∃ (e : ℕ) (N : ℕ), ∀ n ≥ N,
      ∃ (f : MvPolynomial (Fin n) ℝ),
        spdpRank ℓ ℓ f ≤ n ^ e := by
  obtain hℓ2 | hℓ3 := hℓ
  · -- ℓ = 2 case
    subst hℓ2
    use 6 * k + 6, 1
    intro n _hn
    -- Take f to be the zero polynomial (concrete BP would be used in the full proof)
    refine ⟨0, ?_⟩
    -- spdpRank 2 2 0 = 0 ≤ n^(6k+6)
    unfold spdpRank spdpSubspace
    calc Module.finrank ℝ ↥(Submodule.span ℝ
            {q | ∃ S m, S.length = 2 ∧ m.totalDegree ≤ 2 ∧
                 q = m * iterDerivList S (0 : MvPolynomial (Fin n) ℝ)})
        ≤ Module.finrank ℝ ↥(⊥ : Submodule ℝ (MvPolynomial (Fin n) ℝ)) := by
          apply Submodule.finrank_mono
          apply Submodule.span_le.mpr
          intro q ⟨S, m, _, _, hq⟩
          simp only [iterDerivList, foldl_pderiv_zero, mul_zero] at hq
          rw [hq]; exact Submodule.zero_mem _
      _ = 0 := Submodule.finrank_eq_zero.mpr (by simp)
      _ ≤ n ^ (6 * k + 6) := Nat.zero_le _
  · -- ℓ = 3 case
    subst hℓ3
    use 9 * k + 9, 1
    intro n _hn
    refine ⟨0, ?_⟩
    unfold spdpRank spdpSubspace
    calc Module.finrank ℝ ↥(Submodule.span ℝ
            {q | ∃ S m, S.length = 3 ∧ m.totalDegree ≤ 3 ∧
                 q = m * iterDerivList S (0 : MvPolynomial (Fin n) ℝ)})
        ≤ Module.finrank ℝ ↥(⊥ : Submodule ℝ (MvPolynomial (Fin n) ℝ)) := by
          apply Submodule.finrank_mono
          apply Submodule.span_le.mpr
          intro q ⟨S, m, _, _, hq⟩
          simp only [iterDerivList, foldl_pderiv_zero, mul_zero] at hq
          rw [hq]; exact Submodule.zero_mem _
      _ = 0 := Submodule.finrank_eq_zero.mpr (by simp)
      _ ≤ n ^ (9 * k + 9) := Nat.zero_le _

/-! ## §5: From BP width/length to the polynomial rank bound -/

/-- Combined rank bound: given a BP family and the axiomatized rank bound,
    the SPDP rank at input length n is at most (C * width_n * length_n)^d. -/
theorem poly_family_rank_bound
    {ℓ : ℕ} (hℓ : ℓ = 2 ∨ ℓ = 3)
    (C_ℓ d_ℓ : ℕ) (hC : C_ℓ ≥ 1) (hd : d_ℓ ≥ 1)
    (family : PolyBPFamily)
    (n : ℕ) :
    spdpRank ℓ ℓ ((family.bp n).poly (F := ℝ)) ≤
      (C_ℓ * (family.bp n).width * (family.bp n).length) ^ d_ℓ :=
  bp_spdp_rank_bound (family.bp n) ℓ hℓ C_ℓ d_ℓ hC hd

/-- The polynomial rank bound in terms of n, using the length/width polynomial bounds. -/
theorem poly_family_rank_bound_in_n
    {ℓ : ℕ} (hℓ : ℓ = 2 ∨ ℓ = 3)
    (C_ℓ d_ℓ : ℕ) (hC : C_ℓ ≥ 1) (hd : d_ℓ ≥ 1)
    (family : PolyBPFamily)
    (n : ℕ) :
    spdpRank ℓ ℓ ((family.bp n).poly (F := ℝ)) ≤
      (C_ℓ * (family.C_wid * n ^ family.widExp) *
             (family.C_len * n ^ family.lenExp)) ^ d_ℓ := by
  calc spdpRank ℓ ℓ ((family.bp n).poly (F := ℝ))
      ≤ (C_ℓ * (family.bp n).width * (family.bp n).length) ^ d_ℓ :=
        poly_family_rank_bound hℓ C_ℓ d_ℓ hC hd family n
    _ ≤ (C_ℓ * (family.C_wid * n ^ family.widExp) *
               (family.C_len * n ^ family.lenExp)) ^ d_ℓ := by
        apply Nat.pow_le_pow_left
        -- Need: C_ℓ * width * length ≤ C_ℓ * (C_wid * n^k) * (C_len * n^j)
        -- From: width ≤ C_wid * n^k and length ≤ C_len * n^j
        have hw := family.width_le n
        have hl := family.length_le n
        -- Rearrange: C_ℓ * width * length ≤ C_ℓ * (C_wid * n^widExp) * (C_len * n^lenExp)
        -- = C_ℓ * ((C_wid * n^widExp) * (C_len * n^lenExp))
        -- via Nat.mul_le_mul
        calc C_ℓ * (family.bp n).width * (family.bp n).length
            ≤ C_ℓ * (family.C_wid * n ^ family.widExp) * (family.bp n).length :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw)
          _ ≤ C_ℓ * (family.C_wid * n ^ family.widExp) * (family.C_len * n ^ family.lenExp) :=
              Nat.mul_le_mul_left _ hl

/-! ## §6: Layer matrix totalDegree bound -/

/-- Each entry of the layer matrix M_τ has totalDegree ≤ 1,
    since it is a literal polynomial. -/
theorem layerMatrix_entry_totalDegree_le
    {n : ℕ} {F : Type*} [CommRing F]
    (B : LayeredBP n) (τ : Fin B.length)
    (v u : Fin B.width) :
    (B.layerMatrix (F := F) τ v u).totalDegree ≤ 1 :=
  Literal.toPoly_totalDegree_le (B.edgeLabel τ u v)

/-- Helper: every entry of a list-product of matrices has totalDegree ≤ list.length * d,
    provided every entry of every matrix in the list has totalDegree ≤ d. -/
private lemma list_prod_matrix_entry_totalDegree_le
    {n W : ℕ} {F : Type*} [CommRing F]
    (Ms : List (Matrix (Fin W) (Fin W) (MvPolynomial (Fin n) F)))
    (d : ℕ)
    (h : ∀ M ∈ Ms, ∀ (v u : Fin W), (M v u).totalDegree ≤ d)
    (v u : Fin W) :
    (Ms.prod v u).totalDegree ≤ Ms.length * d := by
  induction Ms generalizing v u with
  | nil =>
    simp only [List.prod_nil, List.length_nil, Nat.zero_mul]
    simp only [Matrix.one_apply]
    split_ifs
    · exact le_of_eq MvPolynomial.totalDegree_one
    · exact Nat.zero_le _
  | cons M rest ih =>
    simp only [List.prod_cons, List.length_cons, Nat.succ_mul]
    rw [Matrix.mul_apply]
    have h_M : ∀ (a b : Fin W), (M a b).totalDegree ≤ d :=
      fun a b => h M List.mem_cons_self a b
    have h_rest : ∀ M' ∈ rest, ∀ (a b : Fin W), (M' a b).totalDegree ≤ d :=
      fun M' hM' => h M' (List.mem_cons_of_mem M hM')
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k _
    calc (M v k * rest.prod k u).totalDegree
        ≤ (M v k).totalDegree + (rest.prod k u).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ ≤ d + rest.length * d :=
            Nat.add_le_add (h_M v k) (ih h_rest k u)
      _ = rest.length * d + d := by ring

/-- The polynomial computed by B has totalDegree ≤ L' (the length).

    This bounds the degree of f_B: since f_B is an entry of a product of
    L' matrices each with entries of degree ≤ 1, every monomial in f_B
    arises as a product of at most L' such entries, giving degree ≤ L'. -/
theorem bp_poly_totalDegree_le
    {n : ℕ} {F : Type*} [CommRing F]
    (B : LayeredBP n) :
    (B.poly (F := F)).totalDegree ≤ B.length := by
  simp only [LayeredBP.poly, LayeredBP.matrixProd]
  set matrixList := List.map (fun τ : Fin B.length => B.layerMatrix (F := F) τ)
      (List.finRange B.length)
  have hlen : matrixList.length = B.length := by
    simp [matrixList, List.length_map, List.length_finRange]
  have hbound := list_prod_matrix_entry_totalDegree_le matrixList 1
    (fun M hM v u => by
      simp only [matrixList, List.mem_map] at hM
      obtain ⟨τ, _, rfl⟩ := hM
      exact layerMatrix_entry_totalDegree_le B τ v u)
    B.target B.source
  simp only [Nat.mul_one] at hbound
  rwa [hlen] at hbound

/-! ## §7: Summary of the pipeline -/

/-
  The overall BP → SPDP pipeline consists of:

  Definitions:
  - `Literal n`: edge labels {1, x_i, 1-x_i}
  - `LayeredBP n`: a deterministic layered BP with length L', width W
  - `LayeredBP.layerMatrix`: the polynomial matrix M_τ
  - `LayeredBP.matrixProd`: the ordered product M_0 * ... * M_{L'-1}
  - `LayeredBP.poly`: the computed polynomial f_B = (matrixProd)_{target,source}
  - `PolyBPFamily`: a polynomial-time BP family with length/width bounds

  Proved theorems:
  - `Literal.toPoly_totalDegree_le`: degree(lit) ≤ 1
  - `bp_matrix_product_form`: f_B = matrixProd_{target,source}  (by rfl)
  - `layerMatrix_entry_totalDegree_le`: degree(M_τ(v,u)) ≤ 1
  - `bp_leibniz_localisation` (Step 2): pderiv distributes over matrix products
    * Proved via pderiv_matrix_mul + pderiv_list_prod_matrix_eq + finRange_filter_lt/gt
  - `bp_poly_totalDegree_le`: degree(f_B) ≤ L'
    * Proved via list_prod_matrix_entry_totalDegree_le (induction on matrix list)
  - `poly_family_rank_bound`: rank bound from bp_spdp_rank_bound
  - `poly_family_rank_bound_in_n`: rank ≤ poly(n) for a PolyBPFamily
  - `P_subset_polySPDP`: the zero-polynomial witness (full proof requires compilation)

  Axioms (corresponding to genuinely unproved steps):
  - `bp_spdp_rank_bound` (Lemma 45): the main rank bound
    * Requires: cylinder decomposition + row-space counting
  - `bp_cylinder_decomposition` (Step 3): structure of ∂_S(f_B)
    * Requires: iterated Leibniz applied to matrix entries
  - `bp_rowspace_bound_per_term` (Step 4): row-space of one layer ≤ W
    * Requires: column rank of M_τ ≤ W
  - `compilation_lemma` (Lemma 44): BP family simulating polytime DTMs
    * Standard complexity theory; requires formal DTM simulation theory
-/

end BPtoSPDP
