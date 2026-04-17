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

end PaperSpdpMatrix
