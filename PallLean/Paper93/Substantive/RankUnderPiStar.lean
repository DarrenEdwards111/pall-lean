/-
  PallLean/Paper93/Substantive/RankUnderPiStar.lean

  W6 — Rank-under-Π⋆ bound.

  We prove that any polynomial `p ∈ MvPolynomial (Fin N) ℚ` satisfies
  `mlBlockedSpdpRank B κ ℓ (piStarConcrete N p) ≤ 0` (i.e. equals 0)
  whenever `1 ≤ κ`. This is the precise substantive statement of paper
  §7.1's claim that the universal gauge `Π⋆`, realised concretely as
  projection onto the span of the constant polynomial `1`, collapses the
  SPDP rank to at most one (in fact, zero under the multilinear
  projection, since all nonzero generators are killed by `pderiv`).

  ## Proof sketch

    1. `piStarConcrete N p = (constantCoeff p) • 1 = C (constantCoeff p)`
       (Lemma `piStar_image_is_constant`).

    2. For any constant `C c`, every SPDP generator
       `mlProj (m · iterDerivList S (C c))` vanishes when `S.length = κ ≥ 1`,
       because `iterDerivList S (C c) = 0` on nonempty `S`
       (`GodMoveReal.iterDerivList_C_eq_zero`). Hence the multilinear
       SPDP subspace of `C c` is `⊥` and its rank is 0
       (Lemma `constant_spdp_rank_zero`).

    3. Combine (1) and (2) to conclude
       `mlBlockedSpdpRank B κ ℓ (piStarConcrete N p) ≤ 0`
       (Theorem `piStar_rank_bounded`).

  ## Paper citations

    * §7.1 pp. 25–26 — the universal observer gauge `Π⋆` and its
      rank-minimising property (rank at most 1, collapsing on constants).
    * §28.3 pp. 137–138 — rank-collapse term in the N-Frame Lagrangian.
    * Lemma 40(c), Definition 12 — multilinear SPDP rank.
    * Paper-faithful version of Route C ⇒ Route A at the rank level:
      the universal gauge sends every SPDP-generator polynomial to a
      constant, so its blocked multilinear SPDP rank is 0.

  Kernel-only. No `sorry`. No bespoke axioms.
-/

import PallLean.Paper93.Substantive.ConcretePiStar
import PallLean.GodMoveReal
import PallLean.MultilinearSPDP
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

namespace PallLean.Paper93.Substantive

open MvPolynomial

/-- **Under `Π⋆` (constant projection), every polynomial maps to a constant**.

For any `p : MvPolynomial (Fin N) ℚ`, `piStarConcrete N p = C c` where
`c = constantCoeff p`. The proof reduces the smul-form
`constantCoeff p • 1` to the canonical `C`-form via
`MvPolynomial.C_eq_smul_one`. -/
theorem piStar_image_is_constant (N : ℕ) (p : MvPolynomial (Fin N) ℚ) :
    ∃ c : ℚ, piStarConcrete N p = (MvPolynomial.C c) := by
  refine ⟨MvPolynomial.constantCoeff p, ?_⟩
  -- Unfold `piStarConcrete` to the explicit smul form.
  show (MvPolynomial.constantCoeff p) • (1 : MvPolynomial (Fin N) ℚ) =
        MvPolynomial.C (MvPolynomial.constantCoeff p)
  -- `C c = c • 1` in `MvPolynomial σ F` for any commutative ring `F`.
  rw [MvPolynomial.C_eq_smul_one]

/-- **The multilinear blocked SPDP subspace of a constant is trivial**
(`= ⊥`) whenever `1 ≤ κ`.

Every generator has the form `mlProj (m · iterDerivList S (C c))` with
`S.length = κ ≥ 1`, hence `S` is nonempty and `iterDerivList S (C c) = 0`
by `GodMoveReal.iterDerivList_C_eq_zero`. Each generator therefore
equals `mlProj 0 = 0`, and the spanning set collapses to `{0}`. -/
theorem constant_mlBlockedSpdpSubspace_eq_bot
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ) (hκ : 1 ≤ κ) (c : ℚ) :
    MultilinearSPDP.mlBlockedSpdpSubspace B κ ℓ
        (MvPolynomial.C c : MvPolynomial (Fin N) ℚ) = ⊥ := by
  -- It suffices to show the span-generating set lies in `⊥`.
  apply le_antisymm _ bot_le
  -- Reduce to showing every generator is `0`.
  unfold MultilinearSPDP.mlBlockedSpdpSubspace
  rw [Submodule.span_le]
  rintro q ⟨S, m, hSlen, _hmdeg, _hmvar, _hadm, hq⟩
  -- `S.length = κ ≥ 1`, so `S` is nonempty.
  have hS_ne : S ≠ [] := by
    intro h
    subst h
    simp only [List.length_nil] at hSlen
    omega
  -- `iterDerivList S (C c) = 0` on nonempty `S`.
  have h_iter_zero :
      SPDP.iterDerivList S (MvPolynomial.C c : MvPolynomial (Fin N) ℚ) = 0 :=
    GodMoveReal.iterDerivList_C_eq_zero c S hS_ne
  -- Hence `q = mlProj (m * 0) = mlProj 0 = 0`.
  have hq0 : q = 0 := by
    rw [hq, h_iter_zero, mul_zero, MultilinearSPDP.mlProj_zero]
  -- `q = 0 ∈ ⊥`.
  rw [hq0]
  exact Submodule.zero_mem _

/-- **Constants have multilinear blocked SPDP rank `0` for `κ ≥ 1`**.

Immediate from `constant_mlBlockedSpdpSubspace_eq_bot` via
`finrank_bot`. -/
theorem constant_spdp_rank_zero
    {N B κ ℓ} (c : ℚ) (hκ : 1 ≤ κ) :
    MultilinearSPDP.mlBlockedSpdpRank (n := N) B κ ℓ
        (MvPolynomial.C c : MvPolynomial (Fin N) ℚ) = 0 := by
  unfold MultilinearSPDP.mlBlockedSpdpRank
  rw [constant_mlBlockedSpdpSubspace_eq_bot B κ ℓ hκ c]
  -- `finrank ℚ (⊥ : Submodule ℚ _) = 0`.
  exact finrank_bot ℚ (MvPolynomial (Fin N) ℚ)

/-- **Full result: rank of `Π⋆(p)` is `≤ 0` (hence `= 0`) for any `p`**,
provided the SPDP order parameter satisfies `1 ≤ κ`.

This is the precise statement of paper §7.1's rank-collapse claim in the
multilinear SPDP basis. Route C ⇒ Route A at the rank level for the
universal constant-projection gauge. -/
theorem piStar_rank_bounded
    {N B κ ℓ} (p : MvPolynomial (Fin N) ℚ) (hκ : 1 ≤ κ) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piStarConcrete N p) ≤ 0 := by
  obtain ⟨c, hc⟩ := piStar_image_is_constant N p
  rw [hc]
  exact le_of_eq (constant_spdp_rank_zero (N := N) (B := B) (κ := κ) (ℓ := ℓ) c hκ)


end PallLean.Paper93.Substantive
