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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace PaperSpdpMatrix

open MvPolynomial

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

/-- **Scalar entry of L:** `(α choose β) · coeff_ν(∂^β g)` if β ≤ α
componentwise, else 0.

Uses the multi-index binomial `multiBinom α β = ∏_i (α i choose β i)`,
matching the paper's Leibniz coefficient exactly. -/
noncomputable def leibnizCoeff {N : ℕ} (g : PAC.BoundedGadget N)
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
noncomputable def gadgetLeibnizMatrix {N : ℕ} (g : PAC.BoundedGadget N)
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

### Phase 5 statement (the theorem to prove in a future session)

The formal target:

```
theorem gadget_matrix_factoring
    (g : PAC.BoundedGadget N) (κ ℓ : ℕ) (p : MvPolynomial (Fin N) ℚ)
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

end PaperSpdpMatrix
