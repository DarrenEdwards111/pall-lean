/-
  PallLean/Paper93/Substantive/Theorem10Concrete.lean

  Agent W9 — Paper §7.1 Theorem 10 **concrete instance at `cookLevinQ`**
  using W4's concrete `piStarConcrete` witness.

  ## Scope

  This file composes two earlier ingredients:

    * **W4** (`PallLean/Paper93/Substantive/ConcretePiStar.lean`) —
      `piStarConcrete N : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ`
      is the rank-1 ℚ-linear projection `p ↦ constantCoeff p • 1`.

    * **W6** (`PallLean/PaperFaithfulCompilation.lean` — imports
      `GodMoveReal` and `MultilinearSPDP`) — supplies
      `PaperFaithfulCompilation.cookLevinQ`, the Cook–Levin compiled
      witness, and `mlBlockedSpdpRank_add_const`, the κ ≥ 1
      rank-invariance under adding a constant polynomial.

  The substantive finding is that `piStarConcrete n` sends *any*
  polynomial to a scalar multiple of the constant polynomial `1`.
  In particular, at the Cook–Levin compiled witness `cookLevinQ`, the
  image is `C (constantCoeff cookLevinQ)` — a constant polynomial —
  and for any `κ ≥ 1` the multilinear blocked SPDP rank of a constant
  polynomial is `0` (all `|S| = κ` partial-derivative rows vanish).
  Consequently the projected rank is `0`, which is bounded by `n^200`
  by `positivity`; this is the concrete instance of paper §7.1
  Theorem 10 at `cookLevinQ`.

  ## Paper citation

    * §7.1 Theorem 10 — projected SPDP rank after Π⋆ is polynomial
      in the input length (paper pp. 25–26).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  Expected `#print axioms theorem10_at_cookLevinQ`:
      [propext, Classical.choice, Quot.sound]
-/
import PallLean.Paper93.Substantive.ConcretePiStar
import PallLean.PaperFaithfulCompilation
import PallLean.GodMoveReal

namespace PallLean.Paper93.Substantive

open MvPolynomial SPDP MultilinearSPDP

/-- **Rank bound for `piStarConcrete`-projected polynomials.**

For any `κ ≥ 1`, any block partition `B` on `Fin n`, and any degree
ceiling `ℓ`, the multilinear blocked SPDP rank of
`piStarConcrete n p` is `0`.

Proof idea: `piStarConcrete n p = (constantCoeff p) • 1`, which equals
the constant polynomial `C (constantCoeff p)`.  For `κ ≥ 1`, adding a
constant polynomial does not change the SPDP rank
(`GodMoveReal.mlBlockedSpdpRank_add_const`), and the rank of the zero
polynomial is `0` (`mlBlockedSpdpRank_zero`).  Writing
`C c = 0 + C c`, we conclude `rank (C c) = rank 0 = 0`. -/
theorem piStar_rank_bounded {n : ℕ} {B : SPDP.BlockPartition n} {κ ℓ : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (hκ : 1 ≤ κ) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ (piStarConcrete n p) ≤ 0 := by
  -- Unfold `piStarConcrete n p` to `constantCoeff p • 1`.
  show MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      ((constantCoeff p) • (1 : MvPolynomial (Fin n) ℚ)) ≤ 0
  -- Rewrite `constantCoeff p • 1` as the constant polynomial
  -- `C (constantCoeff p)` via Mathlib's `C_eq_smul_one`.
  rw [show (constantCoeff p) • (1 : MvPolynomial (Fin n) ℚ) =
          (C (constantCoeff p) : MvPolynomial (Fin n) ℚ)
        from (MvPolynomial.C_eq_smul_one (a := constantCoeff p)).symm]
  -- Express `C c` as `0 + C c` so that `mlBlockedSpdpRank_add_const`
  -- applies.
  rw [show (C (constantCoeff p) : MvPolynomial (Fin n) ℚ) =
          ((0 : MvPolynomial (Fin n) ℚ) + C (constantCoeff p))
        from (zero_add _).symm]
  -- Use `GodMoveReal.mlBlockedSpdpRank_add_const` to discard the
  -- constant summand (valid because `κ ≥ 1`).
  rw [GodMoveReal.mlBlockedSpdpRank_add_const B κ ℓ hκ
        (0 : MvPolynomial (Fin n) ℚ) (constantCoeff p)]
  -- The rank of the zero polynomial is `0`.
  rw [MultilinearSPDP.mlBlockedSpdpRank_zero]

/-- **Paper §7.1 Theorem 10 at `cookLevinQ`: Π⋆(cookLevinQ) has
polynomial rank.**

Specialising `piStar_rank_bounded` to the Cook–Levin compiled witness
`cookLevinQ` and bounding `0 ≤ n^200` by `positivity`, we obtain the
concrete Theorem-10 instance: the multilinear blocked SPDP rank of
`piStarConcrete n (cookLevinQ M n hn htb hns)` is at most `n^200`.

This is the W9 substantive compilation of paper §7.1 Theorem 10's
P-side polynomial-rank conclusion, using the concrete `piStarConcrete`
projection from W4 (`PallLean.Paper93.Substantive.ConcretePiStar`). -/
theorem theorem10_at_cookLevinQ
    (M : TuringMachine.DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {B : SPDP.BlockPartition n} {κ ℓ : ℕ} (hκ : 1 ≤ κ) :
    MultilinearSPDP.mlBlockedSpdpRank B κ ℓ
      (piStarConcrete n (PaperFaithfulCompilation.cookLevinQ M n hn htb hns)) ≤ n^200 := by
  apply le_trans (piStar_rank_bounded _ hκ)
  positivity

/-! ## Kernel-only axiom trace -/

#print axioms piStar_rank_bounded
#print axioms theorem10_at_cookLevinQ

end PallLean.Paper93.Substantive
