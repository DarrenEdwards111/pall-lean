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

end PaperSpdpMatrix
