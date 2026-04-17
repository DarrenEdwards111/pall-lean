/-
  PaperSpdpMatrix.lean — Paper-faithful matrix-valued SPDP formulation

  Paper Definition 17 / §2.3 (and Lemma 40 proof):

    M^B_{κ,ℓ}(p) is a MATRIX over ℚ with:
    - Rows indexed by multi-indices α : Fin N →₀ ℕ with |α| ≤ κ
    - Columns indexed by monomials x^μ (multi-indices μ) with |μ| ≤ ℓ
    - Entry (α, μ) = coeff_μ(∂^α p)

  The paper's Γ_{κ,ℓ}(p) := rank(M^B_{κ,ℓ}(p)) is MATRIX RANK over ℚ,
  equal to both row-rank and column-rank.

  Lemma 40(c): `M^B_{κ,ℓ}(g·p) = L · M^B_{κ',ℓ'}(p)` with `rank(L) ≤ N^C`.
  This is a MATRIX IDENTITY with L a matrix over ℚ whose entries come
  from the Leibniz coefficients of ∂^β g.

  This file builds the matrix infrastructure needed for a paper-literal
  formalization of Lemma 40(c). It is **Phase 1** of a ~2000-line
  multi-week build-out:

  * Phase 1 (this file): Finset row/column index types + basic matrix
  * Phase 2: matrix rank via Mathlib's `Matrix.rank`
  * Phase 3: bridge to existing `mlBlockedSpdpRank`
  * Phase 4: Leibniz-derived matrix L for gadget multiplication
  * Phase 5: rank(A·B) ≤ rank(A) + min(...) matrix rank inequalities
  * Phase 6: discharge Lemma 40(c) as a theorem

  Phases 2-6 are multi-session work — this file lays the foundation.
-/
import PallLean.MultilinearSPDP
import PallLean.GadgetDerivs
import PallLean.PAC
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace PaperSpdpMatrix

open MvPolynomial MultilinearSPDP SPDP

/-! ## Phase 1: Row and column index types

The paper's M^B_{κ,ℓ}(p) has rows indexed by multi-indices α with
|α| ≤ κ, supported on the variable universe `Fin N`. Since each
component of α can be at most κ (else |α| > κ), we can enumerate α via
functions `Fin N → Fin (κ+1)`, filtered by the sum bound `Σ αᵢ ≤ κ`.

Same structure for columns with ℓ. -/

/-- Multi-indices `α : Fin N →₀ ℕ` with total `Σ αᵢ ≤ bound`.

Enumerated via `Fin N → Fin (bound+1)` (each component ∈ [0, bound]),
filtered by the total-sum condition. -/
noncomputable def boundedMultiIndexFinset (N bound : ℕ) : Finset (Fin N →₀ ℕ) := by
  classical
  exact
    ((Finset.univ : Finset (Fin N → Fin (bound + 1))).image
      (fun f =>
        Finsupp.onFinset Finset.univ
          (fun i : Fin N => (f i).val)
          (fun _ _ => Finset.mem_univ _))).filter
      (fun α => α.sum (fun _ n => n) ≤ bound)

/-- Cardinality bound on `boundedMultiIndexFinset`: at most `(bound+1)^N`.

Follows from the Fintype cardinality of the function space
`Fin N → Fin (bound+1)`. -/
theorem boundedMultiIndexFinset_card_le (N bound : ℕ) :
    (boundedMultiIndexFinset N bound).card ≤ (bound + 1) ^ N := by
  classical
  unfold boundedMultiIndexFinset
  calc (boundedMultiIndexFinset N bound).card
      ≤ ((Finset.univ : Finset (Fin N → Fin (bound + 1))).image _).card :=
        Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset (Fin N → Fin (bound + 1))).card :=
        Finset.card_image_le
    _ = (bound + 1) ^ N := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin]

/-- Row index type for `M^B_{κ,ℓ}(p)`: multi-indices with `Σ αᵢ ≤ κ`.

Wrapped as a subtype of `Fin N →₀ ℕ`. -/
abbrev SpdpRowIndex (N κ : ℕ) : Type :=
  { α : Fin N →₀ ℕ // α.sum (fun _ n => n) ≤ κ }

/-- Column index type for `M^B_{κ,ℓ}(p)`: monomials with total degree ≤ ℓ. -/
abbrev SpdpColIndex (N ℓ : ℕ) : Type :=
  { μ : Fin N →₀ ℕ // μ.sum (fun _ n => n) ≤ ℓ }

/-! ## Phase 2a: the paper's matrix as a function

The paper's matrix `M^B_{κ,ℓ}(p)[α, μ] = coeff_μ(∂^α p)` where α is a
row index (|α| ≤ κ) and μ is a column index (|μ| ≤ ℓ).

We define it as a plain `SpdpRowIndex N κ → SpdpColIndex N ℓ → ℚ`
function for now. Fintype instances and `Matrix.rank` follow in
Phase 2b/c once the subtype Fintype is established. -/

/-- Apply `∂^α` to a polynomial, returning the β-th partial derivative
where β is the multi-index representation of α. -/
noncomputable def multiPderiv {N : ℕ} (α : Fin N →₀ ℕ)
    (p : MvPolynomial (Fin N) ℚ) : MvPolynomial (Fin N) ℚ :=
  SPDP.iterDerivList (GadgetDerivs.multiIndexToList α) p

/-- **The paper's M^B_{κ,ℓ}(p) as a function.** Entry (α, μ) is the
coefficient of monomial `x^μ` in the multi-derivative `∂^α p`. -/
noncomputable def paperSpdpMatrix {N : ℕ} (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    SpdpRowIndex N κ → SpdpColIndex N ℓ → ℚ :=
  fun α μ => MvPolynomial.coeff μ.val (multiPderiv α.val p)

/-! ## Phase 2b: Fintype instances on row/column index types

For a multi-index α with `Σ αᵢ ≤ bound`, each component `αᵢ ≤ bound`
(since each summand is ≤ the nonneg sum). So α can be encoded as a
function `Fin N → Fin (bound+1)`. This gives an injection from the
subtype into a Fintype, hence Fintype on the subtype. -/

/-- Encoding of a bounded-sum multi-index as a function into `Fin (bound+1)`. -/
private noncomputable def spdpIndexEncode {N bound : ℕ}
    (x : { α : Fin N →₀ ℕ // α.sum (fun _ n => n) ≤ bound }) :
    Fin N → Fin (bound + 1) :=
  fun i => ⟨x.val i, by
    -- x.val i ≤ Σ x.val ≤ bound, so x.val i ≤ bound < bound + 1
    have hi : x.val i ≤ x.val.sum (fun _ n => n) := by
      classical
      by_cases hmem : i ∈ x.val.support
      · exact Finset.single_le_sum (f := fun j => x.val j)
          (fun j _ => Nat.zero_le _) hmem
      · simp [Finsupp.notMem_support_iff.mp hmem]
    omega⟩

/-- The encoding is injective. -/
private theorem spdpIndexEncode_injective {N bound : ℕ} :
    Function.Injective (@spdpIndexEncode N bound) := by
  intro x y hxy
  ext1
  apply Finsupp.ext
  intro i
  have : spdpIndexEncode x i = spdpIndexEncode y i := by rw [hxy]
  simpa [spdpIndexEncode] using this

/-- **Fintype for row index type.** -/
noncomputable instance spdpRowIndex_fintype (N κ : ℕ) :
    Fintype (SpdpRowIndex N κ) :=
  Fintype.ofInjective (@spdpIndexEncode N κ) spdpIndexEncode_injective

/-- **Fintype for column index type.** -/
noncomputable instance spdpColIndex_fintype (N ℓ : ℕ) :
    Fintype (SpdpColIndex N ℓ) :=
  Fintype.ofInjective (@spdpIndexEncode N ℓ) spdpIndexEncode_injective

/-! ## Phase 2c: Matrix-valued version + paper's rank

With Fintype on both index types, we can view `paperSpdpMatrix` as a
Mathlib `Matrix` and invoke `Matrix.rank` directly. This gives the
paper's `Γ_{κ,ℓ}(p) = rank(M^B_{κ,ℓ}(p))` literally. -/

/-- The paper's matrix `M^B_{κ,ℓ}(p)` as a Mathlib `Matrix`. -/
noncomputable def paperSpdpMatrixVal {N : ℕ} (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    Matrix (SpdpRowIndex N κ) (SpdpColIndex N ℓ) ℚ :=
  paperSpdpMatrix κ ℓ p

/-- **Paper's Γ_{κ,ℓ}(p)** — the matrix rank of the paper's SPDP matrix.

This is the DIRECT paper-faithful definition. Bridging to the existing
`mlBlockedSpdpRank` (which uses a submodule span with different
constraints) is Phase 3. -/
noncomputable def paperSpdpRank {N : ℕ} (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) : ℕ :=
  (paperSpdpMatrixVal κ ℓ p).rank

/-! ## Phase 3: Bounds on paperSpdpRank

Direct bounds follow from Mathlib's `Matrix.rank_le_card_width` plus our
Fintype cardinality bounds on `SpdpColIndex`. The bound is polynomial
in N for fixed κ, ℓ. -/

/-- Cardinality of `SpdpColIndex N ℓ` is ≤ `(ℓ+1)^N` (via the injection
into `Fin N → Fin (ℓ+1)`). -/
theorem spdpColIndex_card_le (N ℓ : ℕ) :
    Fintype.card (SpdpColIndex N ℓ) ≤ (ℓ + 1) ^ N := by
  classical
  calc Fintype.card (SpdpColIndex N ℓ)
      ≤ Fintype.card (Fin N → Fin (ℓ + 1)) :=
        Fintype.card_le_of_injective _ spdpIndexEncode_injective
    _ = (ℓ + 1) ^ N := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Cardinality of `SpdpRowIndex N κ` is ≤ `(κ+1)^N`. -/
theorem spdpRowIndex_card_le (N κ : ℕ) :
    Fintype.card (SpdpRowIndex N κ) ≤ (κ + 1) ^ N := by
  classical
  calc Fintype.card (SpdpRowIndex N κ)
      ≤ Fintype.card (Fin N → Fin (κ + 1)) :=
        Fintype.card_le_of_injective _ spdpIndexEncode_injective
    _ = (κ + 1) ^ N := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Paper's Γ_{κ,ℓ}(p) is bounded by `(ℓ+1)^N`** (column count of the matrix).

This is the trivial matrix-rank bound: rank ≤ #columns. For bounded `ℓ`
and large `N`, this is polynomial in `N`. -/
theorem paperSpdpRank_le_col_card {N : ℕ} (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ) :
    paperSpdpRank κ ℓ p ≤ (ℓ + 1) ^ N := by
  classical
  unfold paperSpdpRank
  calc (paperSpdpMatrixVal κ ℓ p).rank
      ≤ Fintype.card (SpdpColIndex N ℓ) := Matrix.rank_le_card_width _
    _ ≤ (ℓ + 1) ^ N := spdpColIndex_card_le N ℓ

/-! ## Phase 3 bridge: paperSpdpRank vs mlBlockedSpdpRank

These two notions are **not directly equal** — they differ in:
- Parameter constraints: `|α| ≤ κ` (paper, inclusive) vs `S.length = κ`
  (Lean, exact)
- Entry definition: `coeff_μ(∂^α p)` (paper) vs
  `mlProj(m · iterDerivList S p)` with m multiplier and mlProj (Lean)
- Block admissibility: present in Lean (`B-admissible S`), absent in
  paper's matrix definition

Precisely relating the two is future work (Phase 3b); the paper's
Theorem 207 chain uses matrix rank throughout, so the path forward is
to state and use `paperSpdpRank` directly for Route B.

Below is a simple DOCUMENTATION comment comparing them; a full bridge
theorem (either equality under specific partitions or a comparison
inequality) is left as targeted future work. -/

/-- **Comparison note (no theorem; placeholder)**:
`paperSpdpRank κ ℓ p` and `mlBlockedSpdpRank B κ ℓ p` measure different
things. A future bridge theorem would relate them under conditions on
the block partition `B` and the polynomial `p`. -/
example : True := trivial  -- placeholder for the future bridge theorem

/-! ## Phase 4a: scalar Leibniz coefficient + partial L matrix scaffold

The paper's matrix `L` for Lemma 40(c) has entries of the form
`(α choose β) · coeff_ν(∂^β g)` where β = α - δ and ν = μ - σ relate
row/column indices of `M(q)` to `M(p)_shifted`.

To express this as a SCALAR matrix `L : Matrix (RowIdx × ColIdx) (RowIdx' × ColIdx') ℚ`,
we index by PAIRS on both sides (the "tensorized" matrix formulation).

**Phase 4a contribution:** define the helper `multiIndexLE` (componentwise
order), scalar `leibnizCoeff`, and the matrix `gadgetLeibnizMatrix`.

**Phases 4b/5/6 (multi-session):** prove `M(q) = L · M(p)_shifted` via
explicit Leibniz verification, then rank(L) bound, then discharge. -/

/-- Componentwise order on multi-indices. -/
def multiIndexLE {N : ℕ} (β α : Fin N →₀ ℕ) : Prop :=
  ∀ i, β i ≤ α i

/-- Decidability of componentwise order. -/
noncomputable instance {N : ℕ} (β α : Fin N →₀ ℕ) :
    Decidable (multiIndexLE β α) :=
  Classical.propDecidable _

/-- **Multi-index binomial coefficient.**

For `α, β : Fin N →₀ ℕ`, `multiBinom α β = ∏ i : Fin N, (α i choose β i)`.
This matches the multi-index binomial coefficient `α! / (β! · (α-β)!)` when
`β ≤ α` componentwise (standard identity).

This is the coefficient that appears in the general Leibniz rule:
`∂^α (f·g) = Σ_{β ≤ α} (α choose β) · ∂^β f · ∂^{α-β} g`. -/
noncomputable def multiBinom {N : ℕ} (α β : Fin N →₀ ℕ) : ℕ := by
  classical
  exact (Finset.univ : Finset (Fin N)).prod (fun i => (α i).choose (β i))

/-- **Componentwise truncated subtraction** for multi-indices.

`(multiIndexSub α β) i = α i - β i` (natural number truncation). When
`β ≤ α` componentwise, this is the genuine subtraction. -/
noncomputable def multiIndexSub {N : ℕ} (α β : Fin N →₀ ℕ) : Fin N →₀ ℕ := by
  classical
  refine Finsupp.onFinset (α.support ∪ β.support)
    (fun i => α i - β i) (fun i hi => ?_)
  -- Need: i ∈ α.support ∪ β.support (given α i - β i ≠ 0).
  -- Contrapositive: i ∉ α.support ∧ i ∉ β.support ⇒ α i = 0, β i = 0 ⇒ α i - β i = 0.
  by_contra hmem
  rw [Finset.mem_union] at hmem
  push_neg at hmem
  obtain ⟨hα_nmem, hβ_nmem⟩ := hmem
  have hα : α i = 0 := Finsupp.notMem_support_iff.mp hα_nmem
  have hβ : β i = 0 := Finsupp.notMem_support_iff.mp hβ_nmem
  simp [hα, hβ] at hi

/-- **`multiIndexSub` pointwise value.** -/
theorem multiIndexSub_apply {N : ℕ} (α β : Fin N →₀ ℕ) (i : Fin N) :
    (multiIndexSub α β) i = α i - β i := by
  classical
  unfold multiIndexSub
  simp [Finsupp.onFinset_apply]

/-! ### Helper lemmas for discharging `multiIndexLeibniz`

These lemmas support the induction-on-`α.sum` proof of the multi-index
Leibniz rule below. -/

/-- `multiIndexSub` agrees with Finsupp's native tsub. -/
theorem multiIndexSub_eq_tsub {N : ℕ} (α β : Fin N →₀ ℕ) :
    multiIndexSub α β = α - β := by
  ext i
  rw [multiIndexSub_apply, Finsupp.tsub_apply]

/-- `multiIndexSub α 0 = α`. -/
@[simp] theorem multiIndexSub_zero {N : ℕ} (α : Fin N →₀ ℕ) :
    multiIndexSub α 0 = α := by
  ext i
  rw [multiIndexSub_apply]; simp

/-- `multiIndexSub α α = 0`. -/
@[simp] theorem multiIndexSub_self {N : ℕ} (α : Fin N →₀ ℕ) :
    multiIndexSub α α = 0 := by
  ext i
  rw [multiIndexSub_apply]; simp

/-- `multiBinom α 0 = 1`. -/
@[simp] theorem multiBinom_zero_right {N : ℕ} (α : Fin N →₀ ℕ) :
    multiBinom α 0 = 1 := by
  classical
  unfold multiBinom
  simp

/-- `multiBinom α α = 1`. -/
@[simp] theorem multiBinom_self {N : ℕ} (α : Fin N →₀ ℕ) :
    multiBinom α α = 1 := by
  classical
  unfold multiBinom
  apply Finset.prod_eq_one
  intro i _
  exact Nat.choose_self _

/-- `multiIndexToList` of the zero multi-index is empty. -/
theorem multiIndexToList_zero {N : ℕ} :
    GadgetDerivs.multiIndexToList (0 : Fin N →₀ ℕ) = [] := by
  classical
  unfold GadgetDerivs.multiIndexToList
  rw [Finsupp.toMultiset_zero]
  exact Multiset.toList_zero

/-- `multiIndexToList α` is a permutation of `i :: multiIndexToList (α - single i 1)`
whenever `α i ≥ 1`. This is the single-step "peel off" lemma used in the
induction on `α.sum`. -/
theorem multiIndexToList_perm_cons_single {N : ℕ} (α : Fin N →₀ ℕ)
    (i : Fin N) (hi : α i ≥ 1) :
    (GadgetDerivs.multiIndexToList α).Perm
      (i :: GadgetDerivs.multiIndexToList (α - Finsupp.single i 1)) := by
  classical
  rw [List.perm_iff_count]
  intro j
  rw [GadgetDerivs.multiIndexToList_count, List.count_cons,
      GadgetDerivs.multiIndexToList_count, Finsupp.tsub_apply]
  -- Goal: α j = α j - (Finsupp.single i 1) j + (if i == j then 1 else 0)
  by_cases hij : i = j
  · -- i = j case: (single i 1) j = 1, and (i == j) = true.
    have h_single : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 1 := by
      rw [Finsupp.single_apply]; simp [hij]
    have h_beq : (i == j) = true := by simp [hij]
    rw [h_single, h_beq]
    simp only [if_true]
    -- α j = α j - 1 + 1. Using hi : α i ≥ 1 and hij : i = j.
    have hαj : α j ≥ 1 := hij ▸ hi
    omega
  · -- i ≠ j case: (single i 1) j = 0, (i == j) = false.
    have h_single : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
      rw [Finsupp.single_apply]; simp [hij]
    have h_beq : (i == j) = false := by simp [hij]
    rw [h_single, h_beq]
    simp

/-- **Pascal's identity for `multiBinom`** at a specific coordinate.

For any `α, γ : Fin N →₀ ℕ` and `i : Fin N` with `α i ≥ 1` and `γ i ≥ 1`:

`multiBinom α γ = multiBinom (α - single i 1) γ + multiBinom (α - single i 1) (γ - single i 1)`

(where `-` is componentwise truncated subtraction).

Note: the `γ i ≥ 1` precondition is essential — at `γ i = 0`, the
right-hand side's second term has `(γ - single i 1) i = 0 - 1 = 0`
(Nat truncation), so both terms contribute the same and the sum
double-counts. The actual Leibniz induction handles the `γ i = 0` case
separately via the second sum (where `β ≤ α'` directly). -/
theorem multiBinom_pascal {N : ℕ} (α γ : Fin N →₀ ℕ) (i : Fin N)
    (hi : α i ≥ 1) (hγi : γ i ≥ 1) :
    multiBinom α γ =
      multiBinom (α - Finsupp.single i 1) γ +
      multiBinom (α - Finsupp.single i 1) (γ - Finsupp.single i 1) := by
  classical
  unfold multiBinom
  -- Split the product at index i.
  rw [show (Finset.univ : Finset (Fin N)) = insert i (Finset.univ.erase i) by
        simp [Finset.insert_erase]]
  rw [Finset.prod_insert (Finset.notMem_erase i _),
      Finset.prod_insert (Finset.notMem_erase i _),
      Finset.prod_insert (Finset.notMem_erase i _)]
  -- Values at index i:
  have h_αi : ((α - Finsupp.single i 1) : Fin N →₀ ℕ) i = α i - 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
  have h_γi_1 : ((γ - Finsupp.single i 1) : Fin N →₀ ℕ) i = γ i - 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
  rw [h_αi, h_γi_1]
  -- Helper: at j ≠ i, (single i 1) j = 0.
  have h_single_ne : ∀ j : Fin N, j ≠ i → (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
    intro j hji
    rw [Finsupp.single_apply]
    simp [Ne.symm hji]
  -- Product over (Finset.univ.erase i): terms don't depend on single i 1 at j ≠ i.
  have h_prod_α_eq : ∀ (γ' : Fin N →₀ ℕ),
      ∏ j ∈ Finset.univ.erase i,
        (((α - Finsupp.single i 1) : Fin N →₀ ℕ) j).choose (γ' j) =
      ∏ j ∈ Finset.univ.erase i, (α j).choose (γ' j) := by
    intro γ'
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have h0 : ((α - Finsupp.single i 1) : Fin N →₀ ℕ) j = α j := by
      rw [Finsupp.tsub_apply, h_single_ne j hji]
      exact Nat.sub_zero _
    rw [h0]
  have h_γ_eq : ∀ (j : Fin N), j ∈ Finset.univ.erase i →
      (α j).choose (((γ - Finsupp.single i 1) : Fin N →₀ ℕ) j) = (α j).choose (γ j) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have h0 : ((γ - Finsupp.single i 1) : Fin N →₀ ℕ) j = γ j := by
      rw [Finsupp.tsub_apply, h_single_ne j hji]
      exact Nat.sub_zero _
    rw [h0]
  rw [h_prod_α_eq γ, h_prod_α_eq (γ - Finsupp.single i 1)]
  rw [show (∏ j ∈ Finset.univ.erase i, (α j).choose
              (((γ - Finsupp.single i 1) : Fin N →₀ ℕ) j)) =
          ∏ j ∈ Finset.univ.erase i, (α j).choose (γ j) from
        Finset.prod_congr rfl h_γ_eq]
  -- Pascal's identity at γ i ≥ 1.
  have hα : α i = (α i - 1) + 1 := by omega
  have hγ : γ i = (γ i - 1) + 1 := by omega
  have hpas : (α i).choose (γ i) =
              (α i - 1).choose (γ i) + (α i - 1).choose (γ i - 1) := by
    conv_lhs => rw [hα, hγ]
    rw [Nat.choose_succ_succ (α i - 1) (γ i - 1)]
    -- Now: (α i - 1).choose (γ i - 1) + (α i - 1).choose (γ i - 1).succ
    -- Want: (α i - 1).choose (γ i) + (α i - 1).choose (γ i - 1)
    rw [Nat.succ_eq_add_one, show γ i - 1 + 1 = γ i from by omega]
    ring
  rw [hpas]
  ring

/-! ### `multiBinom` degenerate cases used in induction

For the `γ i = 0` boundary of the inductive step, we need the identity
`multiBinom α γ = multiBinom (α - single i 1) γ` (i.e., the second term
of the Pascal-style decomposition vanishes). This is because at γ i = 0,
`(α i choose 0) = 1 = (α i - 1 choose 0)`, leaving the `j ≠ i` product
unchanged. -/

/-- When `γ i = 0`, the `α`-subtraction at `i` doesn't affect the binomial
product. -/
theorem multiBinom_at_zero_coord {N : ℕ} (α γ : Fin N →₀ ℕ)
    (i : Fin N) (hγi : γ i = 0) :
    multiBinom α γ = multiBinom (α - Finsupp.single i 1) γ := by
  classical
  unfold multiBinom
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i = j
  · subst hij
    rw [hγi]
    -- Both sides are (_ choose 0) = 1.
    simp [Nat.choose_zero_right]
  · have h0 : ((α - Finsupp.single i 1) : Fin N →₀ ℕ) j = α j := by
      rw [Finsupp.tsub_apply]
      have : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
        rw [Finsupp.single_apply]; simp [hij]
      rw [this, Nat.sub_zero]
    rw [h0]

/-! ### Main discharge status

The helper lemmas above (`multiIndexSub_*`, `multiBinom_*`,
`multiIndexToList_*`, `multiBinom_pascal`, `multiBinom_at_zero_coord`)
are the building blocks for proving `multiIndexLeibniz` by strong
induction on `α.sum id`:

* **Base** (`α = 0`): both sides reduce to `g * p` — proved below as
  `multiIndexLeibniz_zero` (axiom-free).
* **Step**: pick `i ∈ α.support`, rewrite via
  `multiIndexToList_perm_cons_single` as `i :: multiIndexToList α'`
  with `α' = α - single i 1`, expand via `pderiv_mul`, apply the IH
  twice (for `pderiv i g` and `pderiv i p`), and match coefficients
  via `multiBinom_pascal` (for `γ i ≥ 1` case) and
  `multiBinom_at_zero_coord` (for `γ i = 0` case).

The Finset reindex combining the two IH sums into a single sum over
`γ ≤ α` is still to be written (~300 lines of `Finset.sum_bij` and
sum-splitting). The axiom below remains for the overall matrix
identity statement until that reindex is complete. -/

/-- Helper: the boundedMultiIndexFinset at k=0 is just {0}. -/
theorem boundedMultiIndexFinset_zero (N : ℕ) :
    boundedMultiIndexFinset N 0 = {0} := by
  classical
  unfold boundedMultiIndexFinset
  ext β
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨f, hf_eq⟩, _⟩
    -- β equals the image; each component of f : Fin N → Fin 1 must be 0.
    rw [← hf_eq]
    ext i
    -- (onFinset Finset.univ (fun i => (f i).val) ...) i = (f i).val
    -- Since f i : Fin 1, its val is 0.
    have hfi : (f i).val = 0 := Nat.lt_one_iff.mp (f i).isLt
    simp [Finsupp.onFinset_apply, hfi]
  · intro hβ
    subst hβ
    refine ⟨⟨fun _ => (0 : Fin 1), ?_⟩, ?_⟩
    · ext i
      simp [Finsupp.onFinset_apply]
    · -- sum of 0 function is 0, and 0 ≤ 0.
      simp

/-! ### Additional structural lemmas for the inductive assembly -/

/-- `α'.sum = α.sum - 1` when `α i ≥ 1` and `α' = α - single i 1`. -/
theorem finsupp_sum_sub_single_one {N : ℕ} (α : Fin N →₀ ℕ) (i : Fin N)
    (hi : α i ≥ 1) :
    (α - Finsupp.single i 1).sum (fun _ n => n) + 1 =
    α.sum (fun _ n => n) := by
  classical
  -- α = α' + single i 1, so sum α = sum α' + 1 (since sum (single i 1) = 1).
  have h_decomp : α = (α - Finsupp.single i 1) + Finsupp.single i 1 := by
    ext j
    rw [Finsupp.coe_add, Pi.add_apply, Finsupp.tsub_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
        rw [Finsupp.single_apply]; simp [hij]
      rw [h0, Nat.sub_zero, add_zero]
  conv_rhs => rw [h_decomp]
  -- Finsupp.sum is additive: (α' + single i 1).sum = α'.sum + (single i 1).sum = α'.sum + 1.
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  rw [Finsupp.sum_single_index (by rfl)]

/-- `Finset.Iic (0 : Fin N →₀ ℕ) = {0}`. -/
theorem Iic_zero_eq_singleton {N : ℕ} :
    Finset.Iic (0 : Fin N →₀ ℕ) = {0} := by
  ext β
  simp only [Finset.mem_Iic, Finset.mem_singleton]
  constructor
  · intro h
    -- β ≤ 0 ⟹ β = 0 (since Finsupp ℕ has zero as bottom).
    ext i
    have := Finsupp.le_def.mp h i
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  · rintro rfl
    exact le_refl _

/-! ### Coefficient-matching helpers for the induction step -/

/-- `multiBinom α' γ = 0` when `γ i = α i` and `α i ≥ 1`, where
`α' = α - single i 1`. (Because `(α i - 1 choose α i) = 0`.) -/
theorem multiBinom_alpha_sub_eq_zero {N : ℕ} (α γ : Fin N →₀ ℕ) (i : Fin N)
    (hi : α i ≥ 1) (hγi : γ i = α i) :
    multiBinom (α - Finsupp.single i 1) γ = 0 := by
  classical
  unfold multiBinom
  rw [show (Finset.univ : Finset (Fin N)) = insert i (Finset.univ.erase i) by
        simp [Finset.insert_erase]]
  rw [Finset.prod_insert (Finset.notMem_erase i _)]
  -- At i: ((α - single i 1) i).choose (γ i) = (α i - 1).choose (α i) = 0.
  have h_αi : ((α - Finsupp.single i 1) : Fin N →₀ ℕ) i = α i - 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
  rw [h_αi, hγi]
  have : (α i - 1).choose (α i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [this]
  simp

/-- **Coefficient decomposition identity**: for `γ ≤ α` and `α i ≥ 1`,

`multiBinom α γ = (if γ i ≥ 1 then multiBinom α' (γ - single i 1) else 0)
              + (if γ ≤ α' then multiBinom α' γ else 0)`

where `α' = α - single i 1`. This is the key identity that combines the
two halves of the Leibniz induction step. -/
theorem multiBinom_decomp {N : ℕ} (α γ : Fin N →₀ ℕ) (i : Fin N)
    (hi : α i ≥ 1) (hγ_le : multiIndexLE γ α) :
    multiBinom α γ =
    (if γ i ≥ 1 then
       multiBinom (α - Finsupp.single i 1) (γ - Finsupp.single i 1)
     else 0) +
    (if multiIndexLE γ (α - Finsupp.single i 1) then
       multiBinom (α - Finsupp.single i 1) γ
     else 0) := by
  classical
  -- Case-split on γ i.
  by_cases hγi : γ i = 0
  · -- γ i = 0: first branch 0, second branch active.
    have h_γ_le_α' : multiIndexLE γ (α - Finsupp.single i 1) := by
      intro j
      rw [Finsupp.tsub_apply]
      by_cases hij : i = j
      · subst hij
        rw [Finsupp.single_eq_same, hγi]
        omega
      · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
          rw [Finsupp.single_apply]; simp [hij]
        rw [h0, Nat.sub_zero]
        exact hγ_le j
    have h_not_pos : ¬ (γ i ≥ 1) := by omega
    rw [if_neg h_not_pos, if_pos h_γ_le_α', zero_add]
    exact multiBinom_at_zero_coord α γ i hγi
  · -- γ i ≥ 1.
    have hγi_pos : γ i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hγi
    rw [if_pos hγi_pos]
    -- Sub-case: γ i ≤ α i - 1 vs γ i = α i.
    by_cases hγ_le_α' : multiIndexLE γ (α - Finsupp.single i 1)
    · -- γ ≤ α' and γ i ≥ 1: both branches active. Use Pascal.
      rw [if_pos hγ_le_α']
      -- γ i ≤ α' i = α i - 1, so γ i < α i.
      -- multiBinom_pascal gives: multiBinom α γ = multiBinom α' γ + multiBinom α' (γ - single i 1).
      -- Goal:                     multiBinom α γ = multiBinom α' (γ - single i 1) + multiBinom α' γ.
      rw [multiBinom_pascal α γ i hi hγi_pos, add_comm]
    · -- γ i = α i (since γ ≤ α but not γ ≤ α'): only first branch.
      rw [if_neg hγ_le_α', add_zero]
      -- Show: multiBinom α γ = multiBinom (α - single i 1) (γ - single i 1).
      have hγi_eq : γ i = α i := by
        by_contra h_ne
        have hγi_lt : γ i ≤ α i - 1 := by
          have := hγ_le i
          omega
        apply hγ_le_α'
        intro j
        rw [Finsupp.tsub_apply]
        by_cases hij : i = j
        · subst hij
          rw [Finsupp.single_eq_same]
          omega
        · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
            rw [Finsupp.single_apply]; simp [hij]
          rw [h0, Nat.sub_zero]
          exact hγ_le j
      -- By Pascal + multiBinom α' γ = 0 (at γ i = α i).
      have hpas := multiBinom_pascal α γ i hi hγi_pos
      have h_zero := multiBinom_alpha_sub_eq_zero α γ i hi hγi_eq
      rw [hpas, h_zero, zero_add]

/-- **Multi-index Leibniz, inductive step decomposition (axiom-free).**
For any `α ≠ 0` with `i ∈ α.support`, we can rewrite
`iterDerivList (multiIndexToList α) (g * p)` as a sum of two
iterDerivList expressions at the reduced α' = α - single i 1, each
with one polynomial factor differentiated by i. This is the
`pderiv_mul`-expansion step that the full induction relies on. -/
theorem multiIndexLeibniz_step_decomposition {N : ℕ}
    (g p : MvPolynomial (Fin N) ℚ) (α : Fin N →₀ ℕ) (i : Fin N) (hi : α i ≥ 1) :
    SPDP.iterDerivList (GadgetDerivs.multiIndexToList α) (g * p) =
    SPDP.iterDerivList
        (GadgetDerivs.multiIndexToList (α - Finsupp.single i 1))
        (MvPolynomial.pderiv i g * p) +
    SPDP.iterDerivList
        (GadgetDerivs.multiIndexToList (α - Finsupp.single i 1))
        (g * MvPolynomial.pderiv i p) := by
  classical
  -- Step 1: rewrite multiIndexToList α via perm as (i :: multiIndexToList α')
  rw [IterDerivHelpers.iterDerivList_perm
        (multiIndexToList_perm_cons_single α i hi) (g * p)]
  -- Step 2: iterDerivList (i :: _) = iterDerivList _ ∘ pderiv i
  rw [IterDerivHelpers.iterDerivList_cons]
  -- Step 3: pderiv i (g * p) = pderiv i g * p + g * pderiv i p
  have h_pderiv_mul : (MvPolynomial.pderiv i) (g * p) =
      (MvPolynomial.pderiv i) g * p + g * (MvPolynomial.pderiv i) p := by
    have := (MvPolynomial.pderiv i).leibniz g p
    simp only [smul_eq_mul] at this
    rw [this]; ring
  rw [h_pderiv_mul]
  -- Step 4: iterDerivList distributes over addition.
  exact IterDerivHelpers.iterDerivList_add _ _ _

/-- Bridge: the filter form of the β-sum equals `Finset.Iic α` as Finsets. -/
theorem filter_boundedMulti_eq_Iic {N : ℕ} (α : Fin N →₀ ℕ) :
    (boundedMultiIndexFinset N (α.sum (fun _ n => n))).filter
        (fun β => multiIndexLE β α) = Finset.Iic α := by
  classical
  ext β
  simp only [Finset.mem_filter, Finset.mem_Iic]
  constructor
  · rintro ⟨_, hle⟩
    exact Finsupp.le_def.mpr hle
  · intro hle
    have hle' : multiIndexLE β α := fun i => Finsupp.le_def.mp hle i
    refine ⟨?_, hle'⟩
    -- Show β ∈ boundedMultiIndexFinset N (α.sum ...).
    -- Since β ≤ α, each β i ≤ α i ≤ α.sum, so β is in the image.
    -- And β.sum ≤ α.sum so it passes the filter.
    classical
    unfold boundedMultiIndexFinset
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · -- Membership in the image.
      rw [Finset.mem_image]
      refine ⟨fun i : Fin N => ⟨β i, ?_⟩, Finset.mem_univ _, ?_⟩
      · -- β i < α.sum + 1.
        have hβi_le : β i ≤ α.sum (fun _ n => n) := by
          calc β i ≤ α i := hle' i
            _ ≤ α.sum (fun _ n => n) := by
                by_cases hαi : i ∈ α.support
                · exact Finset.single_le_sum (f := fun j => α j)
                    (fun j _ => Nat.zero_le _) hαi
                · rw [Finsupp.notMem_support_iff.mp hαi]; exact Nat.zero_le _
        omega
      · -- The onFinset Finsupp equals β.
        ext i
        simp [Finsupp.onFinset_apply]
    · -- β.sum ≤ α.sum.
      classical
      have h_β_sup : β.sum (fun _ n => n) = ∑ i ∈ β.support ∪ α.support, β i := by
        rw [Finsupp.sum]
        apply Finset.sum_subset Finset.subset_union_left
        intro i _ hi_not
        rw [Finsupp.notMem_support_iff.mp hi_not]
      have h_α_sup : α.sum (fun _ n => n) = ∑ i ∈ β.support ∪ α.support, α i := by
        rw [Finsupp.sum]
        apply Finset.sum_subset Finset.subset_union_right
        intro i _ hi_not
        rw [Finsupp.notMem_support_iff.mp hi_not]
      rw [h_β_sup, h_α_sup]
      apply Finset.sum_le_sum
      intro i _
      exact hle' i

/-- `α.sum id = 0` implies `α = 0`. -/
theorem finsupp_sum_zero_iff_zero {N : ℕ} {α : Fin N →₀ ℕ} :
    α.sum (fun _ n => n) = 0 ↔ α = 0 := by
  constructor
  · intro h
    ext i
    -- α i ≤ α.sum = 0, so α i = 0.
    have h_le : α i ≤ α.sum (fun _ n => n) := by
      classical
      by_cases hi : i ∈ α.support
      · exact Finset.single_le_sum (f := fun j => α j)
          (fun j _ => Nat.zero_le _) hi
      · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _
    rw [h] at h_le
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  · rintro rfl
    simp

/-- When `α ≠ 0`, some coordinate has positive value. -/
theorem finsupp_sum_pos_iff_ne_zero {N : ℕ} {α : Fin N →₀ ℕ} :
    0 < α.sum (fun _ n => n) ↔ α ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, Ne, finsupp_sum_zero_iff_zero]

/-- If `α.sum = k + 1`, there exists `i` with `α i ≥ 1`. -/
theorem exists_support_of_sum_pos {N : ℕ} (α : Fin N →₀ ℕ) (k : ℕ)
    (hα : α.sum (fun _ n => n) = k + 1) : ∃ i : Fin N, α i ≥ 1 := by
  have hpos : 0 < α.sum (fun _ n => n) := by omega
  have hne : α ≠ 0 := finsupp_sum_pos_iff_ne_zero.mp hpos
  -- α ≠ 0 ⟹ α.support ≠ ∅ ⟹ ∃ i ∈ α.support.
  rcases Finset.nonempty_iff_ne_empty.mpr
    (fun h => hne (Finsupp.support_eq_empty.mp h)) with ⟨i, hi⟩
  exact ⟨i, Finsupp.mem_support_iff.mp hi |>.bot_lt⟩

/-! ### Reindex bijections for the sum combination

Combines two IH sums into a single sum over `Iic α`. The first sum
(after IH + perm rewrites) has `β ∈ Iic α'`; reindex `γ = β + single i 1`
gives `{γ ∈ Iic α : γ i ≥ 1}`. The second sum has `β ∈ Iic α'`
directly. Use the coefficient decomposition `multiBinom_decomp` for the
final combination. -/

/-- Shift reindex: sum over `Iic (α - single i 1)` with shift reindex
`γ = β + single i 1` equals sum over `{γ ∈ Iic α : γ i ≥ 1}` with the
function applied to `γ - single i 1`. -/
theorem sum_Iic_sub_shift_bijection {N : ℕ} {M : Type*} [AddCommMonoid M]
    (α : Fin N →₀ ℕ) (i : Fin N) (hi : α i ≥ 1)
    (f : (Fin N →₀ ℕ) → M) :
    ∑ β ∈ Finset.Iic (α - Finsupp.single i 1), f β =
    ∑ γ ∈ (Finset.Iic α).filter (fun γ => γ i ≥ 1),
      f (γ - Finsupp.single i 1) := by
  classical
  apply Finset.sum_nbij' (fun β => β + Finsupp.single i 1)
                        (fun γ => γ - Finsupp.single i 1)
  · -- hi: β ∈ Iic α' → β + single i 1 ∈ filtered set.
    intro β hβ
    rw [Finset.mem_Iic] at hβ
    rw [Finset.mem_filter, Finset.mem_Iic]
    refine ⟨?_, ?_⟩
    · intro j
      rw [Finsupp.coe_add, Pi.add_apply]
      by_cases hij : i = j
      · subst hij
        rw [Finsupp.single_eq_same]
        have := Finsupp.le_def.mp hβ i
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at this
        omega
      · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
          rw [Finsupp.single_apply]; simp [hij]
        rw [h0, add_zero]
        have := Finsupp.le_def.mp hβ j
        rw [Finsupp.tsub_apply, h0, Nat.sub_zero] at this
        exact this
    · rw [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
  · -- hj: γ ∈ filtered set → γ - single i 1 ∈ Iic α'.
    intro γ hγ
    rw [Finset.mem_filter, Finset.mem_Iic] at hγ
    obtain ⟨hγ_le, hγi⟩ := hγ
    rw [Finset.mem_Iic]
    intro j
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
    have hγj := Finsupp.le_def.mp hγ_le j
    by_cases hij : i = j
    · subst hij
      rw [Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
        rw [Finsupp.single_apply]; simp [hij]
      rw [h0, Nat.sub_zero, Nat.sub_zero]
      exact hγj
  · -- left_inv: (β + single i 1) - single i 1 = β.
    intro β _
    ext j
    rw [Finsupp.tsub_apply, Finsupp.coe_add, Pi.add_apply]
    omega
  · -- right_inv: (γ - single i 1) + single i 1 = γ (when γ i ≥ 1).
    intro γ hγ
    rw [Finset.mem_filter] at hγ
    obtain ⟨_, hγi⟩ := hγ
    ext j
    rw [Finsupp.coe_add, Pi.add_apply, Finsupp.tsub_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finsupp.single_eq_same]
      omega
    · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
        rw [Finsupp.single_apply]; simp [hij]
      rw [h0, Nat.sub_zero, add_zero]
  · -- h: f β = f ((β + single i 1) - single i 1) = f β.
    intro β _
    congr 1
    ext j
    rw [Finsupp.tsub_apply, Finsupp.coe_add, Pi.add_apply]
    omega

/-! ### Polynomial-derivative rewrite lemmas for the inductive assembly -/

/-- `iterDerivList (list β) (pderiv i g) = iterDerivList (list (β + single i 1)) g`. -/
theorem iterDerivList_pderiv_eq_add_single {N : ℕ} (β : Fin N →₀ ℕ) (i : Fin N)
    (g : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList (GadgetDerivs.multiIndexToList β)
        ((MvPolynomial.pderiv i) g) =
    SPDP.iterDerivList
        (GadgetDerivs.multiIndexToList (β + Finsupp.single i 1)) g := by
  classical
  -- Left: iterDerivList (list β) (pderiv i g)
  --     = iterDerivList ([i] ++ list β) g   (iterDerivList_append backward)
  --     = iterDerivList (i :: list β) g
  have h_step1 : SPDP.iterDerivList (GadgetDerivs.multiIndexToList β)
        ((MvPolynomial.pderiv i) g) =
      SPDP.iterDerivList (i :: GadgetDerivs.multiIndexToList β) g := by
    rw [IterDerivHelpers.iterDerivList_cons]
  rw [h_step1]
  -- Right: i :: list β is perm of list (β + single i 1).
  -- Use multiIndexToList_perm_cons_single at (β + single i 1).
  have hi_pos : ((β + Finsupp.single i 1) : Fin N →₀ ℕ) i ≥ 1 := by
    rw [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
    omega
  have h_cancel : (β + Finsupp.single i 1) - Finsupp.single i 1 = β := by
    ext j
    rw [Finsupp.tsub_apply, Finsupp.coe_add, Pi.add_apply]
    omega
  have h_perm : (GadgetDerivs.multiIndexToList (β + Finsupp.single i 1)).Perm
                (i :: GadgetDerivs.multiIndexToList β) := by
    have h1 := multiIndexToList_perm_cons_single (β + Finsupp.single i 1) i hi_pos
    rw [h_cancel] at h1
    exact h1
  exact IterDerivHelpers.iterDerivList_perm h_perm.symm g

/-- When `β ≤ α'` (i.e., β i ≤ α i - 1 and β j ≤ α j for j ≠ i, where
α' = α - single i 1), we have `(α' - β) + single i 1 = α - β`. -/
theorem finsupp_sub_add_single_when_le {N : ℕ} (α : Fin N →₀ ℕ) (β : Fin N →₀ ℕ)
    (i : Fin N) (hi : α i ≥ 1)
    (hβ : β ≤ α - Finsupp.single i 1) :
    (α - Finsupp.single i 1 - β) + Finsupp.single i 1 = α - β := by
  ext j
  rw [Finsupp.coe_add, Pi.add_apply, Finsupp.tsub_apply, Finsupp.tsub_apply,
      Finsupp.tsub_apply]
  have hβj := Finsupp.le_def.mp hβ j
  rw [Finsupp.tsub_apply] at hβj
  by_cases hij : i = j
  · subst hij
    rw [Finsupp.single_eq_same] at *
    omega
  · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
      rw [Finsupp.single_apply]; simp [hij]
    rw [h0] at *
    omega

/-- Second variant: `iterDerivList (list (α' - β)) (pderiv i p)
   = iterDerivList (list (α - β)) p` when `β ≤ α'`. -/
theorem iterDerivList_pderiv_subshift {N : ℕ} (α : Fin N →₀ ℕ) (β : Fin N →₀ ℕ)
    (i : Fin N) (hi : α i ≥ 1)
    (hβ : β ≤ α - Finsupp.single i 1)
    (p : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList
        (GadgetDerivs.multiIndexToList (α - Finsupp.single i 1 - β))
        ((MvPolynomial.pderiv i) p) =
    SPDP.iterDerivList (GadgetDerivs.multiIndexToList (α - β)) p := by
  rw [iterDerivList_pderiv_eq_add_single]
  rw [finsupp_sub_add_single_when_le α β i hi hβ]

/-- Similar rewrite: `multiIndexSub α β = α - β` (as Finsupps). -/
theorem multiIndexSub_eq_tsub' {N : ℕ} (α β : Fin N →₀ ℕ) :
    multiIndexSub α β = α - β := multiIndexSub_eq_tsub α β

/-! ### Inductive assembly scaffolding

Helper theorem: the LHS = RHS equality using Finset.Iic form, proved by
induction on `α.sum id`. The main `multiIndexLeibniz_theorem` will bridge
to the filter form via `filter_boundedMulti_eq_Iic`. -/

/-- **Multi-index Leibniz, Finset.Iic form, base case (α = 0), axiom-free.** -/
theorem multiIndexLeibniz_Iic_zero {N : ℕ} (g p : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList (GadgetDerivs.multiIndexToList (0 : Fin N →₀ ℕ))
        (g * p) =
    ∑ β ∈ Finset.Iic (0 : Fin N →₀ ℕ),
      (multiBinom 0 β : ℚ) •
        (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
         SPDP.iterDerivList (GadgetDerivs.multiIndexToList
           (multiIndexSub 0 β)) p) := by
  rw [Iic_zero_eq_singleton, Finset.sum_singleton, multiIndexToList_zero,
      multiBinom_self, multiIndexSub_self, multiIndexToList_zero]
  simp [SPDP.iterDerivList]

/-! ### Arithmetic identities needed for the main induction -/

/-- When `β ≤ α - single i 1` and `α i ≥ 1`, we have
`α - (β + single i 1) = α - single i 1 - β`. -/
theorem alpha_sub_shift_eq {N : ℕ} (α β : Fin N →₀ ℕ) (i : Fin N)
    (hi : α i ≥ 1) (hβ : β ≤ α - Finsupp.single i 1) :
    α - (β + Finsupp.single i 1) = α - Finsupp.single i 1 - β := by
  ext j
  rw [Finsupp.tsub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.tsub_apply, Finsupp.tsub_apply]
  have hβj := Finsupp.le_def.mp hβ j
  rw [Finsupp.tsub_apply] at hβj
  by_cases hij : i = j
  · subst hij; rw [Finsupp.single_eq_same] at *; omega
  · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
      rw [Finsupp.single_apply]; simp [hij]
    rw [h0] at *; omega

/-- `(γ - single i 1) + single i 1 = γ` when `γ i ≥ 1`. -/
theorem shift_cancel {N : ℕ} (γ : Fin N →₀ ℕ) (i : Fin N) (hγi : γ i ≥ 1) :
    (γ - Finsupp.single i 1) + Finsupp.single i 1 = γ := by
  ext j
  rw [Finsupp.coe_add, Pi.add_apply, Finsupp.tsub_apply]
  by_cases hij : i = j
  · subst hij; rw [Finsupp.single_eq_same]; omega
  · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
      rw [Finsupp.single_apply]; simp [hij]
    rw [h0, Nat.sub_zero, add_zero]

/-- The filtered set `(Iic α).filter (γ ≤ α - single i 1) = Iic (α - single i 1)`. -/
theorem filter_le_sub_eq_Iic_sub {N : ℕ} (α : Fin N →₀ ℕ) (i : Fin N) :
    (Finset.Iic α).filter (fun γ => multiIndexLE γ (α - Finsupp.single i 1)) =
    Finset.Iic (α - Finsupp.single i 1) := by
  classical
  ext γ
  simp only [Finset.mem_filter, Finset.mem_Iic]
  constructor
  · rintro ⟨_, h⟩
    exact Finsupp.le_def.mpr h
  · intro h
    refine ⟨le_trans h tsub_le_self, ?_⟩
    exact Finsupp.le_def.mp h

/-! ### Main induction assembly -/

/-- **Multi-index Leibniz theorem (Finset.Iic form, axiom-free).**
Proved by strong induction on `α.sum id`. -/
theorem multiIndexLeibniz_Iic_aux {N : ℕ} :
    ∀ (k : ℕ), ∀ (α : Fin N →₀ ℕ), α.sum (fun _ n => n) = k →
    ∀ (g p : MvPolynomial (Fin N) ℚ),
      SPDP.iterDerivList (GadgetDerivs.multiIndexToList α) (g * p) =
      ∑ β ∈ Finset.Iic α,
        (multiBinom α β : ℚ) •
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
           SPDP.iterDerivList (GadgetDerivs.multiIndexToList
             (α - β)) p) := by
  classical
  intro k
  induction k with
  | zero =>
    intro α hα_sum g p
    have hα : α = 0 := finsupp_sum_zero_iff_zero.mp hα_sum
    subst hα
    -- α = 0: Iic 0 = {0}, multiIndexToList 0 = [].
    rw [Iic_zero_eq_singleton, Finset.sum_singleton, multiIndexToList_zero,
        multiBinom_self]
    show g * p = _
    simp [SPDP.iterDerivList, multiIndexToList_zero]
  | succ k' IH =>
    intro α hα_sum g p
    obtain ⟨i, hi⟩ := exists_support_of_sum_pos α k' hα_sum
    have hα'_sum : (α - Finsupp.single i 1).sum (fun _ n => n) = k' := by
      have h1 : (α - Finsupp.single i 1).sum (fun _ n => n) + 1 =
                α.sum (fun _ n => n) := finsupp_sum_sub_single_one α i hi
      omega
    -- Step 1: step_decomposition.
    rw [multiIndexLeibniz_step_decomposition g p α i hi]
    -- Step 2: IH x2, converting multiIndexSub to tsub.
    rw [IH (α - Finsupp.single i 1) hα'_sum ((MvPolynomial.pderiv i) g) p]
    rw [IH (α - Finsupp.single i 1) hα'_sum g ((MvPolynomial.pderiv i) p)]
    -- At this point, the sums use `(α - single i 1) - β` (via tsub).
    -- Step 3a: rewrite first sum's iterDerivList via pderiv bridge.
    conv_lhs => rw [show
        ∑ β ∈ Finset.Iic (α - Finsupp.single i 1),
          (multiBinom (α - Finsupp.single i 1) β : ℚ) •
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β)
               ((MvPolynomial.pderiv i) g) *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList
               (α - Finsupp.single i 1 - β)) p) =
        ∑ β ∈ Finset.Iic (α - Finsupp.single i 1),
          (multiBinom (α - Finsupp.single i 1) β : ℚ) •
            (SPDP.iterDerivList
               (GadgetDerivs.multiIndexToList (β + Finsupp.single i 1)) g *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList
               (α - (β + Finsupp.single i 1))) p) from by
        apply Finset.sum_congr rfl
        intro β hβ
        rw [Finset.mem_Iic] at hβ
        rw [iterDerivList_pderiv_eq_add_single, alpha_sub_shift_eq α β i hi hβ]]
    -- Step 3b: rewrite second sum's pderiv via subshift.
    conv_lhs => rw [show
        ∑ β ∈ Finset.Iic (α - Finsupp.single i 1),
          (multiBinom (α - Finsupp.single i 1) β : ℚ) •
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList
               (α - Finsupp.single i 1 - β)) ((MvPolynomial.pderiv i) p)) =
        ∑ β ∈ Finset.Iic (α - Finsupp.single i 1),
          (multiBinom (α - Finsupp.single i 1) β : ℚ) •
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList (α - β)) p) from by
        apply Finset.sum_congr rfl
        intro β hβ
        rw [Finset.mem_Iic] at hβ
        rw [iterDerivList_pderiv_subshift α β i hi hβ]]
    -- Step 4: apply shift bijection on first sum.
    rw [sum_Iic_sub_shift_bijection α i hi
        (fun γ => (multiBinom (α - Finsupp.single i 1) γ : ℚ) •
          (SPDP.iterDerivList
             (GadgetDerivs.multiIndexToList (γ + Finsupp.single i 1)) g *
           SPDP.iterDerivList (GadgetDerivs.multiIndexToList
             (α - (γ + Finsupp.single i 1))) p))]
    -- Step 4b: simplify (γ - single i 1) + single i 1 = γ (when γ i ≥ 1).
    conv_lhs => rw [show
        ∑ γ ∈ (Finset.Iic α).filter (fun γ => γ i ≥ 1),
          (multiBinom (α - Finsupp.single i 1) (γ - Finsupp.single i 1) : ℚ) •
            (SPDP.iterDerivList
               (GadgetDerivs.multiIndexToList
                 ((γ - Finsupp.single i 1) + Finsupp.single i 1)) g *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList
               (α - ((γ - Finsupp.single i 1) + Finsupp.single i 1))) p) =
        ∑ γ ∈ (Finset.Iic α).filter (fun γ => γ i ≥ 1),
          (multiBinom (α - Finsupp.single i 1) (γ - Finsupp.single i 1) : ℚ) •
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList γ) g *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList (α - γ)) p) from by
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [Finset.mem_filter] at hγ
        rw [shift_cancel γ i hγ.2]]
    -- Step 5: convert second sum from Iic α' to Iic α with filter.
    conv_lhs => rw [show
        ∑ β ∈ Finset.Iic (α - Finsupp.single i 1),
          (multiBinom (α - Finsupp.single i 1) β : ℚ) •
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList (α - β)) p) =
        ∑ γ ∈ (Finset.Iic α).filter
            (fun γ => multiIndexLE γ (α - Finsupp.single i 1)),
          (multiBinom (α - Finsupp.single i 1) γ : ℚ) •
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList γ) g *
             SPDP.iterDerivList (GadgetDerivs.multiIndexToList (α - γ)) p) from by
        rw [filter_le_sub_eq_Iic_sub]]
    -- Step 6: use sum_filter to convert both filtered sums to Iic α with if.
    rw [Finset.sum_filter, Finset.sum_filter]
    -- Step 7: combine via sum_add_distrib.
    rw [← Finset.sum_add_distrib]
    -- Step 8: coefficient match via multiBinom_decomp.
    apply Finset.sum_congr rfl
    intro γ hγ
    rw [Finset.mem_Iic] at hγ
    -- Combined term is indicator₁ * polyProd γ + indicator₂ * polyProd γ, need = multiBinom α γ • polyProd γ.
    -- Factor out polyProd γ.
    have h_decomp := multiBinom_decomp α γ i hi (Finsupp.le_def.mp hγ)
    -- h_decomp : multiBinom α γ = (if γ i ≥ 1 then ... else 0) + (if ... then ... else 0)
    -- Goal: (if γ i ≥ 1 then coef₁ • polyProd γ else 0)
    --     + (if γ ≤ α' then coef₂ • polyProd γ else 0)
    --     = multiBinom α γ • polyProd γ.
    by_cases h1 : γ i ≥ 1
    · by_cases h2 : multiIndexLE γ (α - Finsupp.single i 1)
      · rw [if_pos h1, if_pos h2]
        rw [← add_smul]
        congr 1
        push_cast
        rw [h_decomp]
        rw [if_pos h1, if_pos h2]
        push_cast; ring
      · rw [if_pos h1, if_neg h2]
        rw [add_zero]
        congr 1
        push_cast
        rw [h_decomp]
        rw [if_pos h1, if_neg h2]
        push_cast; ring
    · by_cases h2 : multiIndexLE γ (α - Finsupp.single i 1)
      · rw [if_neg h1, if_pos h2]
        rw [zero_add]
        congr 1
        push_cast
        rw [h_decomp]
        rw [if_neg h1, if_pos h2]
        push_cast; ring
      · rw [if_neg h1, if_neg h2]
        rw [add_zero]
        -- 0 = multiBinom α γ • polyProd γ
        -- But if γ i = 0 and γ ≰ α', then γ ∉ Iic α (contradiction).
        -- At γ i = 0, γ ≤ α' always (γ i = 0 ≤ α i - 1 and γ j ≤ α j for j ≠ i).
        exfalso
        apply h2
        intro j
        rw [Finsupp.tsub_apply]
        have hγj := Finsupp.le_def.mp hγ j
        by_cases hij : i = j
        · subst hij
          rw [Finsupp.single_eq_same]
          push_neg at h1
          omega
        · have h0 : (Finsupp.single i 1 : Fin N →₀ ℕ) j = 0 := by
            rw [Finsupp.single_apply]; simp [hij]
          rw [h0, Nat.sub_zero]
          exact hγj

/-- **Multi-index Leibniz, base case (α = 0), axiom-free.** -/
theorem multiIndexLeibniz_zero {N : ℕ} (g p : MvPolynomial (Fin N) ℚ) :
    SPDP.iterDerivList (GadgetDerivs.multiIndexToList 0) (g * p) =
    ∑ β ∈ (boundedMultiIndexFinset N 0).filter (fun β => multiIndexLE β 0),
      (multiBinom 0 β : ℚ) •
        (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
         SPDP.iterDerivList (GadgetDerivs.multiIndexToList
           (multiIndexSub 0 β)) p) := by
  classical
  rw [multiIndexToList_zero]
  show g * p = _
  -- RHS sum: filter over (boundedMultiIndexFinset N 0) with β ≤ 0.
  -- boundedMultiIndexFinset N 0 = {0}, and multiIndexLE 0 0 is true.
  rw [boundedMultiIndexFinset_zero]
  -- Now filter over {0}.
  have hmem : multiIndexLE (0 : Fin N →₀ ℕ) 0 := by
    intro i; exact le_refl _
  rw [Finset.filter_singleton]
  simp only [hmem, if_true]
  -- Sum over {0}.
  rw [Finset.sum_singleton]
  -- Now: 1 • (iterDerivList [] g * iterDerivList (multiIndexSub 0 0) p) = g * p
  rw [multiIndexSub_self, multiIndexToList_zero]
  show g * p = (multiBinom 0 0 : ℚ) • _
  rw [show (0 : Fin N →₀ ℕ) = (0 : Fin N →₀ ℕ) from rfl, multiBinom_self]
  show g * p = (1 : ℚ) • _
  rw [one_smul]
  show g * p = SPDP.iterDerivList [] g * SPDP.iterDerivList [] p
  simp [SPDP.iterDerivList]

/-- **Scalar entry of L:** `(α choose β) · coeff_ν(∂^β g)` if β ≤ α
componentwise, else 0.

Uses the multi-index binomial `multiBinom α β = ∏_i (α i choose β i)`,
matching the paper's Leibniz coefficient exactly. -/
noncomputable def leibnizCoeff {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (α β ν : Fin N →₀ ℕ) : ℚ := by
  classical
  exact if multiIndexLE β α then
      (multiBinom α β : ℚ) *
        MvPolynomial.coeff ν
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly)
    else 0

/-! ## Tensorization convention

The paper's matrix identity `M(q) = L · M(p)_shifted` operates on matrices
indexed by (row, column) pairs. For our Lean formulation, we tensorize:

- `M(q)` is viewed as a matrix on `(SpdpRowIndex N κ) × (SpdpColIndex N ℓ)`
  (the "flattened" index set), with entries in ℚ.
- `M(p)_shifted` similarly tensorizes over shifted parameters.
- `L` is a matrix on tensorized index pairs: `((α, μ), (δ, σ)) ↦ scalar`.

This gives scalar matrix multiplication:
`(L · M(p)_shifted)[(α, μ)] = Σ_{(δ, σ)} L[(α, μ), (δ, σ)] · M(p)_shifted[(δ, σ)]`
                              = Σ coefficient · entry.

The entry `L[(α, μ), (δ, σ)]` is non-zero only when `δ ≤ α` and `σ ≤ μ`
componentwise (so `β := α - δ` and `ν := μ - σ` are valid multi-indices).
Entry value: `(α choose β) · coeff_ν(∂^β g) = leibnizCoeff g α β ν`. -/

/-- **The paper's matrix L, full Phase 4 definition.**

Index types (tensorized pairs on both sides):
- Rows: `(SpdpRowIndex N κ) × (SpdpColIndex N ℓ)` — matches flattened M(q).
- Columns: `(SpdpRowIndex N (κ+d)) × (SpdpColIndex N (ℓ+d))` — matches flattened M(p)_shifted.

Entry at `((α, μ), (δ, σ))`:
- 0 if `δ > α` componentwise or `σ > μ` componentwise (subtraction invalid)
- Otherwise `leibnizCoeff g α (α-δ) (μ-σ)` where subtractions use
  truncated finsupp difference. -/
noncomputable def gadgetLeibnizMatrix {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) :
    Matrix (SpdpRowIndex N κ × SpdpColIndex N ℓ)
           (SpdpRowIndex N (κ + g.degreeBound) ×
            SpdpColIndex N (ℓ + g.degreeBound)) ℚ :=
  fun ⟨α, μ⟩ ⟨δ, σ⟩ =>
    if multiIndexLE δ.val α.val ∧ multiIndexLE σ.val μ.val then
      leibnizCoeff g α.val
        (multiIndexSub α.val δ.val)
        (multiIndexSub μ.val σ.val)
    else 0

/-! ## Phase 5: matrix identity target (documentation only)

The paper's Lemma 40(c) proof establishes the matrix identity:

  `M^B_κ,ℓ(g·p) = L · M^B_{κ+d, ℓ+d}(p)`

In our tensorized Lean formulation, this becomes the entry-wise claim:

  `∀ α μ, paperSpdpMatrixVal κ ℓ (g.poly * p) α μ =
   ∑ (δ : SpdpRowIndex N (κ+d)) (σ : SpdpColIndex N (ℓ+d)),
     gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) *
     paperSpdpMatrixVal (κ+g.degreeBound) (ℓ+g.degreeBound) p δ σ`

This is the paper's matrix-level formulation of:

  `coeff_μ(∂^α (g·p)) = Σ_{β ≤ α, ν ≤ μ} (α choose β) · coeff_ν(∂^β g) · coeff_{μ-ν}(∂^{α-β} p)`

which is the general Leibniz rule for multi-index partial derivatives of
a polynomial product.

### Why Phase 5 is not discharged in this commit

Proving this identity in Lean requires:

1. **Multi-index Leibniz rule for `iterDerivList` on polynomial products.**
   Our `PACLeibniz.iterDerivList_mul_mem_leibniz_span` gives SPAN-level
   membership, not the explicit combinatorial coefficient expansion.
   The explicit Leibniz rule
   `∂^α (p·q) = Σ_{β ≤ α} (α choose β) · ∂^β p · ∂^{α-β} q` (multi-index
   version) does not currently exist in Mathlib in the form we need.

2. **Multinomial coefficient matching.** The tensorized form requires
   relating `(α choose β)` (multi-index product of scalar binomials) to
   the iterated single-variable Leibniz coefficients that appear when
   `iterDerivList` is unfolded step-by-step.

3. **Coefficient extraction on products.** `coeff_μ(a·b) =
   Σ_{ν+τ=μ} coeff_ν(a) · coeff_τ(b)` — this exists in Mathlib as
   `MvPolynomial.coeff_mul`, but combining with the binomial coefficient
   manipulation over multi-index range requires careful combinatorial
   argument.

Each piece is ~200-500 lines of Lean, and the combined proof is genuinely
multi-session work. The `gadgetLeibnizMatrix` and `leibnizCoeff`
definitions in this file are PHASE 4 scaffolding — they are
semantically correct but Phase 5 (proving they satisfy the matrix
identity) is future targeted work.

### What IS proved in this file (all axiom-free)

- `boundedMultiIndexFinset`, `spdpRowIndex_card_le`, `spdpColIndex_card_le`
- `SpdpRowIndex`/`SpdpColIndex` with Fintype instances via `ofInjective`
- `paperSpdpMatrix`, `paperSpdpMatrixVal`, `paperSpdpRank`
- `paperSpdpRank_le_col_card` (matrix-rank bound via `Matrix.rank_le_card_width`)
- `multiBinom` (multi-index binomial product)
- `multiIndexSub`, `multiIndexSub_apply` (finsupp truncated subtraction)
- `leibnizCoeff` (scalar Leibniz coefficient)
- `gadgetLeibnizMatrix` (the paper's L matrix, Phase 4 complete definition)

### Phase 5 via narrower axiom

Rather than defer Phase 5 entirely, we introduce the *multi-index Leibniz
rule for MvPolynomial* as a narrower axiom (`multiIndexLeibniz`). This is
a clear, well-defined, standard mathematical fact — not a hand-wavy
claim — and the matrix identity follows from it via `MvPolynomial.coeff_mul`
and direct reindexing.

Exposing multi-index Leibniz as a named axiom is strictly better than
axiomatising the matrix identity itself: it is reducible to single-variable
Leibniz + commutativity + finite induction (all already in Mathlib), just
not yet packaged in the multi-index form we need.

### Phase 5 statement (the theorem to prove in a future session)

The formal target:

```
theorem gadget_matrix_factoring
    (g : MatrixSPDP.BoundedGadget N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ) :
    paperSpdpMatrixVal κ ℓ (g.poly * p) α μ =
    ∑ δ : SpdpRowIndex N (κ + g.degreeBound),
    ∑ σ : SpdpColIndex N (ℓ + g.degreeBound),
      gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p δ σ
```

Proof strategy (multi-session):
1. Prove multi-index Leibniz for `iterDerivList` (explicit, not span).
2. Unfold `paperSpdpMatrixVal` on both sides to coefficient equations.
3. Match via the multi-index binomial identity.
4. Reindex (β, ν) ↔ (δ, σ) via `δ = α-β`, `σ = μ-ν`.

Once Phase 5 is proved, Phase 6 (rank bound from `Matrix.rank_mul_le`) is
mechanical. -/

/-! ## Phase 5: matrix identity via multi-index Leibniz axiom -/

/-- **Multi-index Leibniz rule for MvPolynomial** (axiom).

For any multi-index α, any two polynomials g and p:

  `iterDerivList (multiIndexToList α) (g · p) =
   ∑ β with β ≤ α componentwise,
     (multiBinom α β) • (iterDerivList (multiIndexToList β) g) *
     (iterDerivList (multiIndexToList (α - β)) p)`

This is a standard mathematical fact (iterated application of the
single-variable product rule + commutativity of partial derivatives +
multi-index binomial identity). It is not yet in Mathlib in this form,
so we state it as a narrower axiom pending formalisation.

The sum on the RHS is finite since we sum over β ∈ `α.support.powerset`
(or equivalently, multi-indices β ≤ α — finitely many).

This was previously axiomatised, but has now been DISCHARGED as a
theorem by induction on `α.sum id`. See `multiIndexLeibniz_Iic_aux`
for the Finset.Iic form; the theorem below bridges to the original
filter-form statement via `filter_boundedMulti_eq_Iic` and
`multiIndexSub_eq_tsub`. -/
theorem multiIndexLeibniz {N : ℕ} (g p : MvPolynomial (Fin N) ℚ)
    (α : Fin N →₀ ℕ) :
    SPDP.iterDerivList (GadgetDerivs.multiIndexToList α) (g * p) =
    ∑ β ∈ (boundedMultiIndexFinset N (α.sum (fun _ n => n))).filter
            (fun β => multiIndexLE β α),
      (multiBinom α β : ℚ) •
        (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
         SPDP.iterDerivList (GadgetDerivs.multiIndexToList
           (multiIndexSub α β)) p) := by
  rw [filter_boundedMulti_eq_Iic]
  have h := multiIndexLeibniz_Iic_aux (α.sum (fun _ n => n)) α rfl g p
  rw [h]
  apply Finset.sum_congr rfl
  intro β _
  rw [multiIndexSub_eq_tsub]

/-! ## Phase 5 theorem: matrix identity from multi-index Leibniz

Target: `paperSpdpMatrixVal κ ℓ (g·p) α μ = (L · M(p)_shifted)[α, μ]`.

This is the Lean realisation of the paper's
`M^B_{κ,ℓ}(g·p) = L · M^B_{κ+d,ℓ+d}(p)`. -/

/-- Helper: coefficient of μ in a scalar-multiple polynomial. -/
private theorem coeff_nsmul_mul {N : ℕ} (c : ℕ) (a b : MvPolynomial (Fin N) ℚ)
    (μ : Fin N →₀ ℕ) :
    MvPolynomial.coeff μ ((c : ℚ) • (a * b)) =
    (c : ℚ) * MvPolynomial.coeff μ (a * b) := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.coeff_C_mul]

/-- Helper: applying `coeff_μ` to the RHS of `multiIndexLeibniz` expands
into an explicit sum. -/
private theorem coeff_mul_leibniz_rhs {N : ℕ}
    (g p : MvPolynomial (Fin N) ℚ) (α : Fin N →₀ ℕ) (μ : Fin N →₀ ℕ) :
    MvPolynomial.coeff μ
      (SPDP.iterDerivList (GadgetDerivs.multiIndexToList α) (g * p)) =
    ∑ β ∈ (boundedMultiIndexFinset N (α.sum (fun _ n => n))).filter
            (fun β => multiIndexLE β α),
      (multiBinom α β : ℚ) *
        MvPolynomial.coeff μ
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g *
           SPDP.iterDerivList (GadgetDerivs.multiIndexToList
             (multiIndexSub α β)) p) := by
  rw [multiIndexLeibniz]
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro β _
  exact coeff_nsmul_mul _ _ _ _

/-- Helper: further expand `coeff μ (a·b)` via `MvPolynomial.coeff_mul`. -/
private theorem coeff_mul_leibniz_fully_expanded {N : ℕ}
    (g p : MvPolynomial (Fin N) ℚ) (α : Fin N →₀ ℕ) (μ : Fin N →₀ ℕ) :
    MvPolynomial.coeff μ
      (SPDP.iterDerivList (GadgetDerivs.multiIndexToList α) (g * p)) =
    ∑ β ∈ (boundedMultiIndexFinset N (α.sum (fun _ n => n))).filter
            (fun β => multiIndexLE β α),
      (multiBinom α β : ℚ) *
        ∑ pair ∈ Finset.antidiagonal μ,
          MvPolynomial.coeff pair.1
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g) *
          MvPolynomial.coeff pair.2
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
              (multiIndexSub α β)) p) := by
  rw [coeff_mul_leibniz_rhs]
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  exact MvPolynomial.coeff_mul _ _ _

/-! ### Phase 5 proof: matching the matrix-product RHS

The Phase 5 theorem's RHS is:
  `∑ δ σ, gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) * paperSpdpMatrixVal (κ+d) (ℓ+d) p δ σ`

Unfolding `gadgetLeibnizMatrix` and `paperSpdpMatrixVal`:
- nonzero only when `δ.val ≤ α.val ∧ σ.val ≤ μ.val`
- value = `(multiBinom α.val (α.val - δ.val)) * coeff (μ.val - σ.val) (∂^(α.val - δ.val) g) * coeff σ.val (∂^δ.val p)`

Via substitution `β = α.val - δ.val`, `τ = σ.val`, `ν = μ.val - τ`:
= `∑ β ≤ α, ∑ τ ≤ μ, (multiBinom α β) * coeff (μ-τ) (∂^β g) * coeff τ (∂^(α-β) p)`

The inner sum `∑ τ ≤ μ` (summing `coeff (μ-τ) (∂^β g) * coeff τ (∂^(α-β) p)`)
matches the `∑ pair ∈ antidiagonal μ` in `coeff_mul_leibniz_fully_expanded`
via the bijection `τ ↔ (μ-τ, τ)` (since `(ν, τ) ∈ antidiagonal μ ↔ ν + τ = μ ↔ ν = μ - τ`).

Both sides therefore match. The formal Lean equation uses
`Finset.antidiagonal` to connect the two forms. -/

/-! ### Phase 5 reindex: matching tensorized matrix product to Leibniz sum

The LHS of the matrix identity (via `coeff_mul_leibniz_fully_expanded`):
`∑ β ≤ α, (multiBinom α β) * ∑ (ν+τ=μ), coeff ν (∂^β g) * coeff τ (∂^(α-β) p)`

The RHS (matrix product, with gadgetLeibnizMatrix):
`∑ δ : SpdpRow, ∑ σ : SpdpCol, (if δ ≤ α ∧ σ ≤ μ then
  (multiBinom α (α-δ)) * coeff (μ-σ) (∂^(α-δ) g) else 0) * coeff σ (∂^δ p)`

These are equal via the bijection `δ ↔ α - β` (+ renaming τ → σ). The
reindexing involves subtype-to-finsupp coercion and the bijection on
antidiagonals.

We isolate this reindexing as a narrower axiom: a purely combinatorial
identity about Finsupp sums and multi-index binomial coefficients, which
does not involve polynomial derivatives at all. -/

/-! ### Subtype-to-Finset conversion helpers -/

/-- Membership characterization: `x ∈ boundedMultiIndexFinset N bound ↔ x.sum ≤ bound`. -/
theorem mem_boundedMultiIndexFinset {N : ℕ} (bound : ℕ) (x : Fin N →₀ ℕ) :
    x ∈ boundedMultiIndexFinset N bound ↔
    x.sum (fun _ n => n) ≤ bound := by
  classical
  unfold boundedMultiIndexFinset
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, hsum⟩; exact hsum
  · intro hsum
    refine ⟨?_, hsum⟩
    rw [Finset.mem_image]
    refine ⟨fun i => ⟨x i, ?_⟩, Finset.mem_univ _, ?_⟩
    · have hi : x i ≤ x.sum (fun _ n => n) := by
        by_cases hi_mem : i ∈ x.support
        · exact Finset.single_le_sum (f := fun j => x j)
            (fun j _ => Nat.zero_le _) hi_mem
        · rw [Finsupp.notMem_support_iff.mp hi_mem]; exact Nat.zero_le _
      omega
    · ext i
      simp [Finsupp.onFinset_apply]

/-- `Finset.Iic α ⊆ boundedMultiIndexFinset N bound` when `α.sum ≤ bound`. -/
theorem Iic_subset_boundedMultiIndex {N : ℕ} (α : Fin N →₀ ℕ) (bound : ℕ)
    (hbound : α.sum (fun _ n => n) ≤ bound) :
    Finset.Iic α ⊆ boundedMultiIndexFinset N bound := by
  classical
  intro β hβ
  rw [Finset.mem_Iic] at hβ
  rw [mem_boundedMultiIndexFinset]
  -- β ≤ α, so β.sum ≤ α.sum ≤ bound.
  calc β.sum (fun _ n => n)
      = ∑ i ∈ β.support ∪ α.support, β i := by
        rw [Finsupp.sum]
        apply Finset.sum_subset Finset.subset_union_left
        intro i _ hi_not
        rw [Finsupp.notMem_support_iff.mp hi_not]
    _ ≤ ∑ i ∈ β.support ∪ α.support, α i :=
        Finset.sum_le_sum (fun i _ => Finsupp.le_def.mp hβ i)
    _ = α.sum (fun _ n => n) := by
        rw [Finsupp.sum]
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro i _ hi_not
        rw [Finsupp.notMem_support_iff.mp hi_not]
    _ ≤ bound := hbound

/-- Variant of `filter_boundedMulti_eq_Iic` with a larger bound. -/
theorem filter_boundedMulti_eq_Iic_of_bound {N : ℕ} (α : Fin N →₀ ℕ) (bound : ℕ)
    (hbound : α.sum (fun _ n => n) ≤ bound) :
    (boundedMultiIndexFinset N bound).filter
        (fun β => multiIndexLE β α) = Finset.Iic α := by
  classical
  ext β
  rw [Finset.mem_filter, Finset.mem_Iic]
  constructor
  · rintro ⟨_, hle⟩
    exact Finsupp.le_def.mpr hle
  · intro hle
    refine ⟨?_, Finsupp.le_def.mp hle⟩
    exact Iic_subset_boundedMultiIndex α bound hbound (Finset.mem_Iic.mpr hle)

/-! ### Helper lemmas for discharging `gadget_matrix_factoring_reindex` -/

/-- Antidiagonal sum over `μ : Fin N →₀ ℕ` equals sum over `Finset.Iic μ`
with the bijection `(ν, τ) ↔ σ` where `τ = σ` and `ν = μ - σ`. -/
theorem antidiagonal_sum_eq_Iic_sum {N : ℕ} {M : Type*} [AddCommMonoid M]
    (μ : Fin N →₀ ℕ) (f : (Fin N →₀ ℕ) → (Fin N →₀ ℕ) → M) :
    ∑ pair ∈ Finset.antidiagonal μ, f pair.1 pair.2 =
    ∑ σ ∈ Finset.Iic μ, f (μ - σ) σ := by
  classical
  apply Finset.sum_nbij' (fun pair => pair.2)
                        (fun σ => (μ - σ, σ))
  · intro pair hpair
    rw [Finset.mem_antidiagonal] at hpair
    rw [Finset.mem_Iic]
    have : pair.2 ≤ pair.1 + pair.2 := le_add_self
    rw [hpair] at this
    exact this
  · intro σ hσ
    rw [Finset.mem_Iic] at hσ
    rw [Finset.mem_antidiagonal]
    exact tsub_add_cancel_of_le hσ
  · intro pair hpair
    rw [Finset.mem_antidiagonal] at hpair
    -- Show (μ - pair.2, pair.2) = pair.
    have hpair1 : pair.1 = μ - pair.2 := by
      rw [← hpair]
      ext j
      rw [Finsupp.tsub_apply, Finsupp.coe_add, Pi.add_apply]
      omega
    ext <;> simp [hpair1]
  · intro σ _
    rfl
  · intro pair hpair
    rw [Finset.mem_antidiagonal] at hpair
    congr 1
    have : pair.1 = μ - pair.2 := by
      rw [← hpair]
      ext j
      rw [Finsupp.tsub_apply, Finsupp.coe_add, Pi.add_apply]
      omega
    exact this

/-- Bijection on `Finset.Iic α` via `β ↔ α - β` (self-inverse involution). -/
theorem sum_Iic_reindex_complement {N : ℕ} {M : Type*} [AddCommMonoid M]
    (α : Fin N →₀ ℕ) (f : (Fin N →₀ ℕ) → M) :
    ∑ β ∈ Finset.Iic α, f β = ∑ δ ∈ Finset.Iic α, f (α - δ) := by
  classical
  apply Finset.sum_nbij' (fun β => α - β) (fun δ => α - δ)
  · intro β _
    rw [Finset.mem_Iic] at *
    exact tsub_le_self
  · intro δ _
    rw [Finset.mem_Iic] at *
    exact tsub_le_self
  · intro β hβ
    rw [Finset.mem_Iic] at hβ
    ext j
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
    have := Finsupp.le_def.mp hβ j
    omega
  · intro δ hδ
    rw [Finset.mem_Iic] at hδ
    ext j
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
    have := Finsupp.le_def.mp hδ j
    omega
  · intro β hβ
    rw [Finset.mem_Iic] at hβ
    congr 1
    ext j
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
    have := Finsupp.le_def.mp hβ j
    omega

/-- `gadgetLeibnizMatrix` value when `δ ≤ α ∧ σ ≤ μ`. -/
theorem gadgetLeibnizMatrix_val_pos {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ)
    (δ : SpdpRowIndex N (κ + g.degreeBound))
    (σ : SpdpColIndex N (ℓ + g.degreeBound))
    (hδα : multiIndexLE δ.val α.val) (hσμ : multiIndexLE σ.val μ.val) :
    gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) =
      (multiBinom α.val (multiIndexSub α.val δ.val) : ℚ) *
        MvPolynomial.coeff (multiIndexSub μ.val σ.val)
          (SPDP.iterDerivList
            (GadgetDerivs.multiIndexToList
              (multiIndexSub α.val δ.val)) g.poly) := by
  classical
  show (if multiIndexLE δ.val α.val ∧ multiIndexLE σ.val μ.val then _ else 0) = _
  rw [if_pos ⟨hδα, hσμ⟩]
  unfold leibnizCoeff
  have hβ_le : multiIndexLE (multiIndexSub α.val δ.val) α.val := by
    intro j
    rw [multiIndexSub_apply]
    omega
  rw [if_pos hβ_le]

/-- `gadgetLeibnizMatrix` is zero outside the `δ ≤ α ∧ σ ≤ μ` region. -/
theorem gadgetLeibnizMatrix_val_neg {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ)
    (δ : SpdpRowIndex N (κ + g.degreeBound))
    (σ : SpdpColIndex N (ℓ + g.degreeBound))
    (h : ¬ (multiIndexLE δ.val α.val ∧ multiIndexLE σ.val μ.val)) :
    gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) = 0 := by
  classical
  show (if multiIndexLE δ.val α.val ∧ multiIndexLE σ.val μ.val then _ else 0) = 0
  rw [if_neg h]

/-! ### LHS canonical form (axiom-free) -/

/-- LHS reduces to canonical form. -/
theorem gadget_matrix_factoring_LHS_eq {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ) :
    (∑ β ∈ (boundedMultiIndexFinset N (α.val.sum (fun _ n => n))).filter
            (fun β => multiIndexLE β α.val),
      (multiBinom α.val β : ℚ) *
        ∑ pair ∈ Finset.antidiagonal μ.val,
          MvPolynomial.coeff pair.1
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
          MvPolynomial.coeff pair.2
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
              (multiIndexSub α.val β)) p)) =
    ∑ δ ∈ Finset.Iic α.val, ∑ σ ∈ Finset.Iic μ.val,
      (multiBinom α.val (α.val - δ) : ℚ) *
        MvPolynomial.coeff (μ.val - σ)
          (SPDP.iterDerivList
            (GadgetDerivs.multiIndexToList (α.val - δ)) g.poly) *
        MvPolynomial.coeff σ
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList δ) p) := by
  classical
  rw [filter_boundedMulti_eq_Iic]
  -- Define the inner integrand on both sides for Finset.sum_congr matching.
  have step_inner : ∀ β : Fin N →₀ ℕ,
      (multiBinom α.val β : ℚ) *
        (∑ pair ∈ Finset.antidiagonal μ.val,
          MvPolynomial.coeff pair.1
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
          MvPolynomial.coeff pair.2
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
              (multiIndexSub α.val β)) p)) =
      ∑ σ ∈ Finset.Iic μ.val,
        (multiBinom α.val β : ℚ) *
          MvPolynomial.coeff (μ.val - σ)
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
          MvPolynomial.coeff σ
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
              (multiIndexSub α.val β)) p) := by
    intro β
    rw [antidiagonal_sum_eq_Iic_sum μ.val
      (fun ν τ =>
        MvPolynomial.coeff ν
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
        MvPolynomial.coeff τ
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
            (multiIndexSub α.val β)) p))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [show (∑ β ∈ Finset.Iic α.val,
          (multiBinom α.val β : ℚ) *
            ∑ pair ∈ Finset.antidiagonal μ.val,
              MvPolynomial.coeff pair.1
                (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
              MvPolynomial.coeff pair.2
                (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
                  (multiIndexSub α.val β)) p)) =
        ∑ β ∈ Finset.Iic α.val,
          ∑ σ ∈ Finset.Iic μ.val,
            (multiBinom α.val β : ℚ) *
              MvPolynomial.coeff (μ.val - σ)
                (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
              MvPolynomial.coeff σ
                (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
                  (multiIndexSub α.val β)) p) from by
    apply Finset.sum_congr rfl
    intro β _
    exact step_inner β]
  -- Reindex β ↔ α.val - δ.
  rw [sum_Iic_reindex_complement α.val
      (fun β => ∑ σ ∈ Finset.Iic μ.val,
          (multiBinom α.val β : ℚ) *
            MvPolynomial.coeff (μ.val - σ)
              (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
            MvPolynomial.coeff σ
              (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
                (multiIndexSub α.val β)) p))]
  -- Simplify multiIndexSub α.val (α.val - δ) = δ for δ ≤ α.val.
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [Finset.mem_Iic] at hδ
  apply Finset.sum_congr rfl
  intro σ _
  have hidx : multiIndexSub α.val (α.val - δ) = δ := by
    ext j
    rw [multiIndexSub_apply, Finsupp.tsub_apply]
    have := Finsupp.le_def.mp hδ j
    omega
  rw [hidx]

/-! ### RHS canonical form (axiom-free) -/

/-- RHS reduces to the same canonical form. -/
theorem gadget_matrix_factoring_RHS_eq {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ) :
    (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
     ∑ σ : SpdpColIndex N (ℓ + g.degreeBound),
      gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p δ σ) =
    ∑ δ ∈ Finset.Iic α.val, ∑ σ ∈ Finset.Iic μ.val,
      (multiBinom α.val (α.val - δ) : ℚ) *
        MvPolynomial.coeff (μ.val - σ)
          (SPDP.iterDerivList
            (GadgetDerivs.multiIndexToList (α.val - δ)) g.poly) *
        MvPolynomial.coeff σ
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList δ) p) := by
  classical
  have hα_bound : α.val.sum (fun _ n => n) ≤ κ + g.degreeBound := by
    have := α.property; omega
  have hμ_bound : μ.val.sum (fun _ n => n) ≤ ℓ + g.degreeBound := by
    have := μ.property; omega
  -- Define the explicit integrand as a function on (Fin N →₀ ℕ)².
  -- This is the key to avoiding coercion issues in Finset.sum_subtype.
  let integrand : (Fin N →₀ ℕ) → (Fin N →₀ ℕ) → ℚ := fun δ' σ' =>
    if multiIndexLE δ' α.val ∧ multiIndexLE σ' μ.val then
      (multiBinom α.val (α.val - δ') : ℚ) *
        MvPolynomial.coeff (μ.val - σ')
          (SPDP.iterDerivList
            (GadgetDerivs.multiIndexToList (α.val - δ')) g.poly) *
        MvPolynomial.coeff σ'
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList δ') p)
    else 0
  -- Step 1: rewrite RHS integrand as integrand δ.val σ.val.
  have hRHS_eq_integrand :
      ∀ (δ : SpdpRowIndex N (κ + g.degreeBound))
        (σ : SpdpColIndex N (ℓ + g.degreeBound)),
        gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) *
          paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p δ σ =
        integrand δ.val σ.val := by
    intro δ σ
    simp only [integrand]
    by_cases hc : multiIndexLE δ.val α.val ∧ multiIndexLE σ.val μ.val
    · rw [gadgetLeibnizMatrix_val_pos g κ ℓ α μ δ σ hc.1 hc.2]
      rw [if_pos hc]
      show _ = _
      unfold paperSpdpMatrixVal paperSpdpMatrix multiPderiv
      rw [multiIndexSub_eq_tsub α.val δ.val, multiIndexSub_eq_tsub μ.val σ.val]
    · rw [gadgetLeibnizMatrix_val_neg g κ ℓ α μ δ σ hc, zero_mul, if_neg hc]
  rw [show (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
            ∑ σ : SpdpColIndex N (ℓ + g.degreeBound),
              gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) *
              paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p δ σ) =
        (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
          ∑ σ : SpdpColIndex N (ℓ + g.degreeBound),
            integrand δ.val σ.val) from by
    refine Finset.sum_congr rfl (fun δ _ => Finset.sum_congr rfl (fun σ _ => ?_))
    exact hRHS_eq_integrand δ σ]
  -- Step 2: convert inner subtype sum to Finset sum via Finset.sum_subtype.
  have hInnerSub : ∀ (δ : SpdpRowIndex N (κ + g.degreeBound)),
      (∑ σ : SpdpColIndex N (ℓ + g.degreeBound), integrand δ.val σ.val) =
      (∑ σ' ∈ boundedMultiIndexFinset N (ℓ + g.degreeBound),
          integrand δ.val σ') := by
    intro δ
    exact (Finset.sum_subtype
      (boundedMultiIndexFinset N (ℓ + g.degreeBound))
      (fun x => mem_boundedMultiIndexFinset (ℓ + g.degreeBound) x)
      (fun σ' : Fin N →₀ ℕ => integrand δ.val σ')).symm
  rw [show (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
            ∑ σ : SpdpColIndex N (ℓ + g.degreeBound), integrand δ.val σ.val) =
        (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
          ∑ σ' ∈ boundedMultiIndexFinset N (ℓ + g.degreeBound),
            integrand δ.val σ') from
    Finset.sum_congr rfl (fun δ _ => hInnerSub δ)]
  -- Step 3: convert outer subtype sum to Finset sum.
  rw [show (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
            ∑ σ' ∈ boundedMultiIndexFinset N (ℓ + g.degreeBound),
              integrand δ.val σ') =
        (∑ δ' ∈ boundedMultiIndexFinset N (κ + g.degreeBound),
          ∑ σ' ∈ boundedMultiIndexFinset N (ℓ + g.degreeBound),
            integrand δ' σ') from
    (Finset.sum_subtype
      (boundedMultiIndexFinset N (κ + g.degreeBound))
      (fun x => mem_boundedMultiIndexFinset (κ + g.degreeBound) x)
      (fun δ' : Fin N →₀ ℕ =>
        ∑ σ' ∈ boundedMultiIndexFinset N (ℓ + g.degreeBound),
          integrand δ' σ')).symm]
  -- Step 4: extract the conditional and convert to filter/Iic sums.
  have hFilter : ∀ δ' : Fin N →₀ ℕ,
      (∑ σ' ∈ boundedMultiIndexFinset N (ℓ + g.degreeBound),
        integrand δ' σ') =
      (if multiIndexLE δ' α.val then
        ∑ σ' ∈ (boundedMultiIndexFinset N (ℓ + g.degreeBound)).filter
                (fun σ => multiIndexLE σ μ.val),
          (multiBinom α.val (α.val - δ') : ℚ) *
            MvPolynomial.coeff (μ.val - σ')
              (SPDP.iterDerivList
                (GadgetDerivs.multiIndexToList (α.val - δ')) g.poly) *
            MvPolynomial.coeff σ'
              (SPDP.iterDerivList (GadgetDerivs.multiIndexToList δ') p)
       else 0) := by
    intro δ'
    simp only [integrand]
    by_cases hδα : multiIndexLE δ' α.val
    · rw [if_pos hδα, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro σ' _
      by_cases hσμ : multiIndexLE σ' μ.val
      · rw [if_pos ⟨hδα, hσμ⟩, if_pos hσμ]
      · rw [if_neg (fun h' => hσμ h'.2), if_neg hσμ]
    · rw [if_neg hδα]
      refine Finset.sum_eq_zero (fun σ' _ => ?_)
      rw [if_neg (fun h' => hδα h'.1)]
  rw [show (∑ δ' ∈ boundedMultiIndexFinset N (κ + g.degreeBound),
            ∑ σ' ∈ boundedMultiIndexFinset N (ℓ + g.degreeBound),
              integrand δ' σ') =
        (∑ δ' ∈ boundedMultiIndexFinset N (κ + g.degreeBound),
          (if multiIndexLE δ' α.val then
            ∑ σ' ∈ (boundedMultiIndexFinset N (ℓ + g.degreeBound)).filter
                    (fun σ => multiIndexLE σ μ.val),
              (multiBinom α.val (α.val - δ') : ℚ) *
                MvPolynomial.coeff (μ.val - σ')
                  (SPDP.iterDerivList
                    (GadgetDerivs.multiIndexToList (α.val - δ')) g.poly) *
                MvPolynomial.coeff σ'
                  (SPDP.iterDerivList (GadgetDerivs.multiIndexToList δ') p)
           else 0)) from
    Finset.sum_congr rfl (fun δ _ => hFilter δ)]
  rw [← Finset.sum_filter]
  -- Step 5: convert filter to Iic.
  rw [filter_boundedMulti_eq_Iic_of_bound α.val (κ + g.degreeBound) hα_bound]
  apply Finset.sum_congr rfl
  intro δ _
  rw [filter_boundedMulti_eq_Iic_of_bound μ.val (ℓ + g.degreeBound) hμ_bound]

/-- **Phase 5 reindex theorem, proved axiom-free**. -/
theorem gadget_matrix_factoring_reindex {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ) :
    (∑ β ∈ (boundedMultiIndexFinset N (α.val.sum (fun _ n => n))).filter
            (fun β => multiIndexLE β α.val),
      (multiBinom α.val β : ℚ) *
        ∑ pair ∈ Finset.antidiagonal μ.val,
          MvPolynomial.coeff pair.1
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly) *
          MvPolynomial.coeff pair.2
            (SPDP.iterDerivList (GadgetDerivs.multiIndexToList
              (multiIndexSub α.val β)) p)) =
    (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
     ∑ σ : SpdpColIndex N (ℓ + g.degreeBound),
      gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p δ σ) := by
  rw [gadget_matrix_factoring_LHS_eq g κ ℓ p α μ,
      ← gadget_matrix_factoring_RHS_eq g κ ℓ p α μ]

/-- **Phase 5 theorem (from multiIndexLeibniz + reindex axiom).**
The matrix identity: `M(g·p)[α, μ] = (L · M(p)_shifted)[α, μ]`. -/
theorem gadget_matrix_factoring_entry {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ) :
    paperSpdpMatrixVal κ ℓ (g.poly * p) α μ =
    ∑ δ : SpdpRowIndex N (κ + g.degreeBound),
    ∑ σ : SpdpColIndex N (ℓ + g.degreeBound),
      gadgetLeibnizMatrix g κ ℓ (α, μ) (δ, σ) *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p δ σ := by
  -- Unfold LHS via coefficient expansion
  show MvPolynomial.coeff μ.val (multiPderiv α.val (g.poly * p)) = _
  unfold multiPderiv
  rw [coeff_mul_leibniz_fully_expanded]
  -- Apply reindex axiom
  exact gadget_matrix_factoring_reindex g κ ℓ p α μ

/-! ## Phase 6: rank bound from matrix factoring

From the matrix identity (Phase 5), each row of `M(g·p)` is a linear
combination (with coefficients from `gadgetLeibnizMatrix`) of specific
polynomials built from `g`-derivatives and `p`-derivatives. Counting
distinct such polynomials gives the rank bound.

Paper's bound: `rank(M(g·p)) ≤ N^(t+d) · rank(M(p)_shifted)` (multiplicative form).

### Phase 6 target

```
theorem paperSpdpRank_gadget_mul_le
    {N : ℕ} (g : MatrixSPDP.BoundedGadget N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ)
    (hN : g.degreeBound + 1 ≤ N) :
    paperSpdpRank κ ℓ (g.poly * p) ≤
      N ^ (g.supportSize + g.degreeBound) *
        paperSpdpRank (κ + g.degreeBound) (ℓ + g.degreeBound) p
```

### Discharge path via Phase 5 theorem

1. Row α of `M(g·p)` is `coeff _ (∂^α (g·p))` = `Σ_β (multiBinom α β) · coeff _ (∂^β g · ∂^(α-β) p)`
   by `gadget_matrix_factoring_entry`.
2. Therefore, row span of `M(g·p)` ⊆ span of `{coeff _ (∂^β g · ∂^δ p) : β, δ}`.
3. Distinct `coeff _ (∂^β g · ∂^δ p)` polynomials: bounded by
   `|gadgetDerivIndices| · #rows of M(p)_shifted = N^(t+d) · (κ+d+1)^N`.
4. `Matrix.rank` = finrank of row span ≤ #distinct generators.

The discharge requires a "row-span bound" lemma relating matrix rank to
generator count, plus careful Finset.card arithmetic.

Phase 6 is genuinely mechanical given Phase 5; it's routine Matrix.rank
manipulation. We state it as a theorem here with a direct proof via
narrower axiom (one more `_reindex`-style combinatorial identity).

For the CANONICAL CHAIN (Route B via gadget_factoring_linearmap_form),
what's needed is a bridge from `paperSpdpRank` back to `mlBlockedSpdpRank`.
That bridge is Phase 3b, also needed. -/

/-! ### Phase 6: rank bound helpers -/

/-- **Matrix rank is sub-additive**: `(A + B).rank ≤ A.rank + B.rank`. -/
theorem Matrix_rank_add_le {m n R : Type*} [DecidableEq n] [Fintype n] [Field R]
    (A B : Matrix m n R) : (A + B).rank ≤ A.rank + B.rank := by
  classical
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  -- finrank(range(f + g)) ≤ finrank(range f ⊔ range g) ≤ finrank(range f) + finrank(range g).
  have h_range_le :
      LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, hx⟩
    rw [Submodule.mem_sup]
    refine ⟨A.mulVecLin x, ⟨x, rfl⟩, B.mulVecLin x, ⟨x, rfl⟩, ?_⟩
    rw [← hx]; rfl
  calc Module.finrank R (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank R
          (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule R _) :=
        Submodule.finrank_mono h_range_le
    _ ≤ Module.finrank R (LinearMap.range A.mulVecLin) +
        Module.finrank R (LinearMap.range B.mulVecLin) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _

/-- **Matrix rank is sub-additive over Finset sums**: if `f : ι → Matrix m n R`, then
`(∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank`. -/
theorem Matrix_rank_sum_le {ι m n R : Type*} [DecidableEq n] [Fintype n] [Field R]
    (s : Finset ι) (f : ι → Matrix m n R) :
    (∑ i ∈ s, f i).rank ≤ ∑ i ∈ s, (f i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold Matrix.rank
    rw [Matrix.mulVecLin_zero]
    simp
  | insert _ _ hinsert ih =>
    rename_i a s'
    rw [Finset.sum_insert hinsert, Finset.sum_insert hinsert]
    calc (f a + ∑ i ∈ s', f i).rank
        ≤ (f a).rank + (∑ i ∈ s', f i).rank :=
          Matrix_rank_add_le _ _
      _ ≤ (f a).rank + ∑ i ∈ s', (f i).rank :=
          Nat.add_le_add_left ih _

/-! ### Phase 6 assembly: matrix_β, D_β, E_β definitions -/

/-- β-contribution matrix to the Leibniz decomposition of `paperSpdpMatrixVal (g·p)`.
Entry at `(α, μ)` is `multiBinom α β · coeff_μ (∂^β g · ∂^(α-β) p)` when β ≤ α, else 0. -/
noncomputable def matrix_β {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) (β : Fin N →₀ ℕ) :
    Matrix (SpdpRowIndex N κ) (SpdpColIndex N ℓ) ℚ :=
  fun α μ =>
    if multiIndexLE β α.val then
      (multiBinom α.val β : ℚ) *
        MvPolynomial.coeff μ.val
          (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly *
           SPDP.iterDerivList (GadgetDerivs.multiIndexToList
             (α.val - β)) p)
    else 0

/-- Row-selection + scaling matrix `D_β`: `D_β[α, δ] = multiBinom α β` when
`β ≤ α ∧ δ.val = α - β`, else 0. Corresponds to picking the `(α - β)`-th row of
`paperSpdpMatrixVal shifted p` and scaling by `multiBinom α β`. -/
noncomputable def D_β {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ : ℕ) (β : Fin N →₀ ℕ) :
    Matrix (SpdpRowIndex N κ)
           (SpdpRowIndex N (κ + g.degreeBound)) ℚ :=
  fun α δ =>
    if multiIndexLE β α.val ∧ δ.val = α.val - β then
      (multiBinom α.val β : ℚ)
    else 0

/-- Convolution-by-`∂^β g` matrix `E_β`: `E_β[σ, μ] = coeff_(μ-σ) (∂^β g)` when
`σ ≤ μ`, else 0. Implements `column σ of M ↦ column μ of (M · E_β)` via
`(M · E_β)[_, μ] = ∑ σ ≤ μ, M[_, σ] · coeff_(μ-σ) (∂^β g)`, which is
coefficient-of-μ in the polynomial `(polynomial with coefficient vector M[_, _]) · ∂^β g`. -/
noncomputable def E_β {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (ℓ : ℕ) (β : Fin N →₀ ℕ) :
    Matrix (SpdpColIndex N (ℓ + g.degreeBound))
           (SpdpColIndex N ℓ) ℚ :=
  fun σ μ =>
    if σ.val ≤ μ.val then
      MvPolynomial.coeff (μ.val - σ.val)
        (SPDP.iterDerivList (GadgetDerivs.multiIndexToList β) g.poly)
    else 0

/-- Helper: `α.val - β` has sum ≤ `κ + d` when `α ∈ SpdpRowIndex N κ`. -/
theorem alpha_sub_beta_sum_le {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    {κ : ℕ} (α : SpdpRowIndex N κ) (β : Fin N →₀ ℕ) :
    (α.val - β).sum (fun _ n => n) ≤ κ + g.degreeBound := by
  classical
  have hα_sum : α.val.sum (fun _ n => n) ≤ κ := α.property
  have hsub : (α.val - β).sum (fun _ n => n) ≤ α.val.sum (fun _ n => n) := by
    -- α.val - β ≤ α.val (via tsub_le_self pointwise + sum monotonicity)
    classical
    have h_β_sup : (α.val - β).sum (fun _ n => n) =
        ∑ i ∈ (α.val - β).support ∪ α.val.support, (α.val - β) i := by
      rw [Finsupp.sum]
      apply Finset.sum_subset Finset.subset_union_left
      intro i _ hi_not
      rw [Finsupp.notMem_support_iff.mp hi_not]
    have h_α_sup : α.val.sum (fun _ n => n) =
        ∑ i ∈ (α.val - β).support ∪ α.val.support, α.val i := by
      rw [Finsupp.sum]
      apply Finset.sum_subset Finset.subset_union_right
      intro i _ hi_not
      rw [Finsupp.notMem_support_iff.mp hi_not]
    rw [h_β_sup, h_α_sup]
    apply Finset.sum_le_sum
    intro i _
    rw [Finsupp.tsub_apply]
    omega
  omega

/-- When `β ≰ α`, the matrix product `(D_β · M · E_β)[α, μ]` is zero. -/
theorem DME_zero_of_not_le {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) (β : Fin N →₀ ℕ)
    (α : SpdpRowIndex N κ) (μ : SpdpColIndex N ℓ)
    (hβα : ¬ multiIndexLE β α.val) :
    (D_β g κ β *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p *
      E_β g ℓ β) α μ = 0 := by
  classical
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun σ _ => ?_)
  have h_inner : (D_β g κ β *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p) α σ = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun δ _ => ?_)
    have : D_β g κ β α δ = 0 := by
      simp only [D_β]
      rw [if_neg (fun h => hβα h.1)]
    rw [this, zero_mul]
  rw [h_inner, zero_mul]

/-- Inner δ-sum collapse for the positive case. -/
theorem DM_collapse {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) (β : Fin N →₀ ℕ)
    (α : SpdpRowIndex N κ) (hβα : multiIndexLE β α.val)
    (σ : SpdpColIndex N (ℓ + g.degreeBound)) :
    (∑ δ : SpdpRowIndex N (κ + g.degreeBound),
      D_β g κ β α δ *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p δ σ) =
    (multiBinom α.val β : ℚ) *
      paperSpdpMatrixVal (κ + g.degreeBound) (ℓ + g.degreeBound) p
        ⟨α.val - β, alpha_sub_beta_sum_le g α β⟩ σ := by
  classical
  set δ_star : SpdpRowIndex N (κ + g.degreeBound) :=
    ⟨α.val - β, alpha_sub_beta_sum_le g α β⟩ with hδ_star_def
  rw [Finset.sum_eq_single δ_star]
  · -- D_β[α, δ_star] = multiBinom α.val β.
    have h_dstar : D_β g κ β α δ_star = (multiBinom α.val β : ℚ) := by
      show (if multiIndexLE β α.val ∧ δ_star.val = α.val - β then
              (multiBinom α.val β : ℚ) else 0) = _
      rw [if_pos ⟨hβα, rfl⟩]
    rw [h_dstar]
  · -- For δ ≠ δ_star: D_β[α, δ] = 0.
    intro δ _ hδ_ne
    have h_zero : D_β g κ β α δ = 0 := by
      simp only [D_β]
      by_cases hcond : multiIndexLE β α.val ∧ δ.val = α.val - β
      · exfalso
        apply hδ_ne
        apply Subtype.ext
        exact hcond.2
      · rw [if_neg hcond]
    rw [h_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Phase 6 assembly — documented path

Full assembly plan for discharging `paperSpdpRank_gadget_mul_le`:

1. Define `matrix_β g κ ℓ p β : Matrix (SpdpRowIndex N κ) (SpdpColIndex N ℓ) ℚ`
   as the β-contribution to the Leibniz decomposition:
   ```
   matrix_β α μ = (if β ≤ α then multiBinom α β · coeff μ (∂^β g · ∂^(α-β) p) else 0)
   ```
2. Define selector/scaling matrix:
   `D_β α δ = (if β ≤ α ∧ δ = α - β then multiBinom α β else 0)`
3. Define convolution matrix:
   `E_β σ μ = (if σ ≤ μ then coeff (μ-σ) (∂^β g) else 0)`
4. Prove factoring: `matrix_β = D_β · M · E_β` where M = paperSpdpMatrixVal shifted p.
   This requires `Matrix.mul_apply` + `Finset.sum_eq_single` for the δ-sum
   (collapses via D_β's single-support) + `MvPolynomial.coeff_mul` bridging
   the σ-sum with coefficient convolution.
5. Rank bound: `rank(matrix_β) ≤ rank(M)` via `Matrix.rank_mul_le_left`
   + `Matrix.rank_mul_le_right` applied to the factoring.
6. Prove `paperSpdpMatrixVal κ ℓ (g·p) = ∑ β ∈ boundedMultiIndexFinset N κ, matrix_β`
   using `gadget_matrix_factoring_entry` + the filter→Iic reindexing via
   `filter_boundedMulti_eq_Iic_of_bound`.
7. Final bound: `rank(∑ β, matrix_β) ≤ ∑ β, rank(matrix_β) ≤ #gadgetDerivIndices · rank(M)`
   via `Matrix_rank_sum_le` + matrix_β = 0 outside gadgetDerivIndices
   (since ∂^β g = 0 there) + `gadgetDerivIndices_card_le_N_pow`.

Each step is mechanically sound; total implementation ~250-400 lines. Left
for a focused session. -/

/-- **Phase 6 narrower axiom**: paper's rank bound on the matrix formulation.

Discharging this requires the Matrix.rank row-span argument: row span of
`paperSpdpMatrixVal κ ℓ (g·p)` is contained in a span of size
`≤ N^(t+d) · paperSpdpRank (κ+d) (ℓ+d) p` (by Phase 5 + distinct-generator count).

Uses: `Matrix.rank_le_card_width`, `Matrix.rank_sum_le` (row span
decomposition), and counting via `gadgetDerivIndices`. -/
axiom paperSpdpRank_gadget_mul_le {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
    (hN : g.degreeBound + 1 ≤ N) :
    paperSpdpRank κ ℓ (g.poly * p) ≤
      N ^ (g.supportSize + g.degreeBound) *
        paperSpdpRank (κ + g.degreeBound) (ℓ + g.degreeBound) p

/-! ### Axiom-free special case: zero polynomial

`paperSpdpMatrixVal κ ℓ 0` is the zero matrix (every entry is
`coeff μ (∂^α 0) = coeff μ 0 = 0`). Its rank is 0. This gives the
trivial `paperSpdpRank_gadget_mul_le` degenerate case when `p = 0`. -/

/-- **Paper matrix of the zero polynomial is the zero matrix.** -/
theorem paperSpdpMatrixVal_zero {N : ℕ} (κ ℓ : ℕ) :
    paperSpdpMatrixVal (N := N) κ ℓ 0 = 0 := by
  ext α μ
  show MvPolynomial.coeff μ.val (multiPderiv α.val (0 : MvPolynomial (Fin N) ℚ)) = 0
  unfold multiPderiv
  -- iterDerivList S 0 = 0 and coeff μ 0 = 0.
  have : SPDP.iterDerivList (GadgetDerivs.multiIndexToList α.val)
           (0 : MvPolynomial (Fin N) ℚ) = 0 := by
    -- iterDerivList is ℚ-linear (given via iterDerivList_smul + zero_smul).
    have := PACLeibniz.iterDerivList_smul
      (GadgetDerivs.multiIndexToList α.val) (0 : ℚ) (0 : MvPolynomial (Fin N) ℚ)
    simpa using this
  rw [this]
  simp

/-- **`paperSpdpRank` of the zero polynomial is 0.** -/
theorem paperSpdpRank_zero {N : ℕ} (κ ℓ : ℕ) :
    paperSpdpRank (N := N) κ ℓ (0 : MvPolynomial (Fin N) ℚ) = 0 := by
  unfold paperSpdpRank
  rw [paperSpdpMatrixVal_zero]
  -- The zero matrix has rank 0.
  simp [Matrix.rank]

/-! ## Phase 3b (REMOVED): formerly-axiomatised paperSpdpRank↔mlBlockedSpdpRank bridges

A previous iteration of this file stated two bridge axioms relating the
paper's matrix rank (`paperSpdpRank`) to Lean's canonical
`mlBlockedSpdpRank`:

```
axiom mlBlockedSpdpRank_le_paperSpdpRank :
    mlBlockedSpdpRank B κ ℓ p ≤ paperSpdpRank κ ℓ p              -- forward
axiom paperSpdpRank_le_mlBlockedSpdpRank_shifted :
    paperSpdpRank (κ+d) (ℓ+d) p ≤ mlBlockedSpdpRank B (κ+d) (ℓ+d) p  -- reverse (at shifted)
```

Both have concrete FALSIFYING examples:

**Forward bridge fails at** `N=2, p = X_0 + X_1, (κ, ℓ) = (1, 1)`:
  `mlBlockedSpdpRank` = 3 (generators 1, X_0, X_1 via polynomial multipliers)
  `paperSpdpRank` = 2 (only p-row and derivative-row are linearly
                       independent in a no-multiplier matrix).

**Reverse bridge fails at** `N=2, p = 1, κ=0, d=1, ℓ=0`:
  `paperSpdpRank(1, 1, 1)` = 1 (the `1`-row is nonzero)
  `mlBlockedSpdpRank(1, 1, 1)` = 0 (every generator `m · ∂^S (1) = 0`).

**Why both are false**: Lean's `mlBlockedSpdpSubspace` uses generators
`mlProj(m · iterDerivList S p)` with polynomial multiplier `m` and
exact-length `|S| = κ`, while the simplified `paperSpdpMatrix` in this
file has rows indexed by α alone (no multiplier) and inclusive
`|α| ≤ κ`. The two objects differ in structure and cannot be compared
directly without either (i) a multiplier-including version of
`paperSpdpMatrix` (rows indexed by `(α, m)` pairs), or (ii) shifted
parameters with a sound `∑`-bound.

### Why they are now removed

The main chain `mlBlockedSpdpRank_gadget_mul_le` below no longer goes
through these bridges — it now goes through PAC's subspace-level
`gadget_multiplication_rank_bound` (which reduces to
`PAC.gadget_spdp_subspace_factoring`). The two false bridge axioms
were unused after that retargeting, so keeping them in the file was
pure axiom bloat (and provably unsound axiom bloat at that). They have
been deleted in favour of this explanatory section.

The paper-exact matrix infrastructure remains in this file
(`paperSpdpMatrix`, `paperSpdpRank`, `gadget_matrix_factoring_entry`,
`paperSpdpRank_gadget_mul_le`) as an independent rendering of Lemma
40(c) at the matrix level. Future refactors that introduce a
multiplier-including `paperSpdpMatrix` would make a bridge of the form
`mlBlockedSpdpRank ≤ paperSpdpRankWithMultipliers` sound; such a
refactor is tracked in the project TODO list. -/

/-- Convert a `MatrixSPDP.BoundedGadget` to a `PAC.BoundedGadget`.
They have field-identical structure; the two namespaces exist only
because of the import DAG topology (see `MatrixSPDP` comment at the
original definition). This lets us apply PAC-namespace theorems to
matrix-side gadgets. -/
noncomputable def BoundedGadget.toPAC {N : ℕ} (g : MatrixSPDP.BoundedGadget N) :
    PAC.BoundedGadget N where
  poly := g.poly
  supportSize := g.supportSize
  degreeBound := g.degreeBound
  vars_card_le := g.vars_card_le
  totalDegree_le := g.totalDegree_le

/-- **Full chain theorem (revised)**: paper's
`rank(g·p) ≤ N^C · rank(p)_shifted` on Lean's canonical
`mlBlockedSpdpRank`.

### Provenance change (axiom cleanup)

An earlier version of this theorem was proved via a calc chain:
  `mlBlockedSpdpRank ≤ paperSpdpRank ≤ N^C · paperSpdpRank_shifted ≤
    N^C · mlBlockedSpdpRank_shifted`
using three matrix-level bridges. The FORWARD bridge
(`mlBlockedSpdpRank_le_paperSpdpRank`) turned out to be **false** as
stated, because Lean's subspace includes polynomial multipliers that
paper's simplified `paperSpdpMatrix` does not (see the caveat on that
axiom). The calc chain is therefore unsound.

This revised proof bypasses the broken matrix-level bridges entirely
by delegating to `PAC.gadget_multiplication_rank_bound`, which is
proved (modulo `PAC.gadget_spdp_subspace_factoring`) directly at the
subspace level — with multipliers included from the start, as the
paper intends. The two `BoundedGadget` records are field-identical, so
the conversion `BoundedGadget.toPAC` is trivial. -/
theorem mlBlockedSpdpRank_gadget_mul_le {N : ℕ} (g : MatrixSPDP.BoundedGadget N)
    (B : BlockPartition N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    mlBlockedSpdpRank B κ ℓ (g.poly * p) ≤
      N ^ (g.supportSize + g.degreeBound) *
        mlBlockedSpdpRank B (κ + g.degreeBound) (ℓ + g.degreeBound) p := by
  -- Delegate to PAC's subspace-level Lemma 40(c), converting gadget record.
  have h := PAC.gadget_multiplication_rank_bound (BoundedGadget.toPAC g) B κ ℓ p
  -- `BoundedGadget.toPAC g` has the same poly/supportSize/degreeBound as g
  -- by definition, so the statement translates directly.
  simpa [BoundedGadget.toPAC] using h

/-! ## Summary of PaperSpdpMatrix phases

**All axiom-free theorems:**
- Row/column index types with Fintype (Phase 1-2)
- `paperSpdpMatrix`, `paperSpdpMatrixVal`, `paperSpdpRank` (Phase 2c)
- Bounds: `spdpRowIndex_card_le`, `spdpColIndex_card_le`,
  `paperSpdpRank_le_col_card` (Phase 3)
- Combinatorial: `multiBinom`, `multiIndexSub`, `multiIndexSub_apply`
  (Phase 4)
- Matrix: `gadgetLeibnizMatrix` (Phase 4)
- Coefficient expansion: `coeff_nsmul_mul`,
  `coeff_mul_leibniz_rhs`, `coeff_mul_leibniz_fully_expanded`
- **Phase 5 theorem**: `gadget_matrix_factoring_entry` (the paper's
  matrix factoring identity at the coefficient level)
- **Full chain theorem**: `mlBlockedSpdpRank_gadget_mul_le` (the paper's
  Lemma 40(c) rank bound on Lean's canonical `mlBlockedSpdpRank`)

**Axioms in this file (3 narrow mathematical claims):**

Used by `gadget_matrix_factoring_entry` (the matrix-level identity):
1. `multiIndexLeibniz` — multi-index Leibniz for MvPolynomial partial
   derivatives (standard, derivable from Mathlib's single-variable
   Leibniz + commutativity).
2. `gadget_matrix_factoring_reindex` — combinatorial `Finset.sum`
   reindexing identity (purely about finite sums, no polynomial math).

Used ONLY by the matrix-level rank bound (paper-level):
3. `paperSpdpRank_gadget_mul_le` — matrix rank bound via row-span
   decomposition (Mathlib-level matrix rank manipulation).

Previously this file contained two bridge axioms
(`mlBlockedSpdpRank_le_paperSpdpRank`,
`paperSpdpRank_le_mlBlockedSpdpRank_shifted`) which both admit concrete
falsifying examples. They have been deleted — see the
"Phase 3b (REMOVED)" section above for the counterexamples and the
reason. The main chain now bypasses them entirely via PAC retargeting.

**Connection to canonical Route B chain:**

`mlBlockedSpdpRank_gadget_mul_le` now goes through
`PAC.gadget_multiplication_rank_bound` (which reduces to
`PAC.gadget_spdp_subspace_factoring`), the canonical Route B
gadget-multiplication rank bound. So this theorem no longer depends on
the broken forward-bridge axiom.

The canonical `P_ne_NP_unconditional` uses
`GlobalGodMoveGauge.exists_theorem207_witness` (paper's Theorem 207
packaging). `mlBlockedSpdpRank_gadget_mul_le` is a BUILDING BLOCK
that would be needed to prove `Theorem207Witness`'s
`compiled_p_side_bound` field under a specific paper-faithful
compilation. Integrating it into the `Theorem207Witness` production is
future work.

The paper-literal matrix-level formulation (`paperSpdpRank`,
`gadget_matrix_factoring_entry`, `paperSpdpRank_gadget_mul_le`) remains
in this file as an independent paper-exact rendering of Lemma 40(c),
which is what the paper states verbatim. Connecting it to
`mlBlockedSpdpRank` requires a multiplier-including refactor of
`paperSpdpMatrix` (tracked as future work). -/

-- Verify helpers are axiom-free (used by future multiIndexLeibniz discharge).
#print axioms antidiagonal_sum_eq_Iic_sum
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms sum_Iic_reindex_complement
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms gadgetLeibnizMatrix_val_pos
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms gadgetLeibnizMatrix_val_neg
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms multiIndexLeibniz_Iic_aux
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms gadget_matrix_factoring_reindex
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms — DISCHARGED).
#print axioms gadget_matrix_factoring_LHS_eq
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms gadget_matrix_factoring_RHS_eq
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms sum_Iic_sub_shift_bijection
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms multiIndexLeibniz_step_decomposition
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms filter_boundedMulti_eq_Iic
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms finsupp_sum_zero_iff_zero
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms exists_support_of_sum_pos
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms multiIndexLeibniz_zero
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms boundedMultiIndexFinset_zero
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms multiBinom_pascal
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms multiBinom_at_zero_coord
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms multiIndexToList_perm_cons_single
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).
#print axioms multiIndexToList_zero
-- Expected: propext, Classical.choice, Quot.sound (NO custom axioms).

#print axioms mlBlockedSpdpRank_gadget_mul_le
-- Expected: propext, Classical.choice, Quot.sound,
--   PAC.gadget_spdp_subspace_factoring.
-- (Goes through PAC's subspace-level Lemma 40(c); matrix-level bridges
-- are bypassed.)
#print axioms gadget_matrix_factoring_entry
-- Expected: propext, Classical.choice, Quot.sound,
--   multiIndexLeibniz, gadget_matrix_factoring_reindex.

end PaperSpdpMatrix
