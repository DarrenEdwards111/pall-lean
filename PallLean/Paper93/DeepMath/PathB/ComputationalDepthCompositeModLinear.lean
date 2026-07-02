import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCompositeModSym

/-!
# Composite `MOD_m`: the gate is `SYM` of a degree-1 linear form

Rung 6 (`…MvPoly`) gave an exact degree-`n` `MvPolynomial` for a `MOD_m` gate — but that degree `n` is entirely an
*arithmetisation artifact* of writing the exponential `ζ^{count}` as a product over all bits.  Semantically the gate reads
only the **count** `k = ∑ᵢ xᵢ`, which is a **degree-1 linear form**.  This file makes that precise: `MOD_m` is a symmetric
function applied to a degree-1 polynomial.

  `countPoly` — the count as a linear polynomial `∑ᵢ Xᵢ` over `ℤ`.
  `countPoly_totalDegree_le` — **PROVED**: `deg (countPoly) ≤ 1`.
  `eval_countPoly` — **PROVED**: it evaluates to the input count `boolCount x`.
  `modSym_eq_of_countPoly` — **PROVED**: `MOD_m x = (symmetric fn) (eval countPoly x)` — the gate is a symmetric function
        of the degree-1 count, its inner polynomial degree being `1`, not `n`.

## Honest scope — locating the degree, definitively

Together with the earlier composite files this pins the degree budget of `ACC⁰[m]` exactly.  A single `MOD_m` gate costs
degree `1` (a symmetric function of the linear count) — *not* the degree `n` of its char-sum arithmetisation, which was an
artifact.  So the genuine degree cost in a depth-`d` `ACC⁰[m]` circuit comes entirely from the `AND`/`OR` layers composed
with the `MOD` gates — exactly the Razborov–Smolensky low-degree approximation this repo's prime-modulus arc
(`…RazborovSmolensky*`, rungs 20–28) already formalises, but which over incompatible characteristics needs Toda's
`ℤ`-lifting.  Composing the (degree-1) `MOD`-symmetric tops with the low-degree `AND`/`OR` approximations across the whole
circuit at quasipolynomial total degree is the `NEXP`-strength open piece, **not** established here.  This file states the
single-gate degree honestly.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositeMod

open MvPolynomial

variable {n : ℕ}

/-- The input count as a linear polynomial `∑ᵢ Xᵢ` over `ℤ`. -/
noncomputable def countPoly : MvPolynomial (Fin n) ℤ := ∑ i, X i

/-- **The count polynomial is linear (proved)**: `deg ≤ 1`. -/
theorem countPoly_totalDegree_le : (countPoly (n := n)).totalDegree ≤ 1 := by
  rw [countPoly]
  exact le_trans (totalDegree_finset_sum _ _) (Finset.sup_le (fun i _ => (totalDegree_X i).le))

/-- **The count polynomial evaluates to the count (proved)**. -/
theorem eval_countPoly (x : Fin n → Bool) :
    (eval (fun i => (if x i then 1 else 0 : ℤ))) countPoly = (boolCount x : ℤ) := by
  rw [countPoly, map_sum]
  simp only [eval_X]
  rw [boolCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  cases x i <;> simp

/-- **`MOD_m` is `SYM` of the degree-1 count (proved)**: the gate is a symmetric function `modAccept m` of the value of the
degree-`1` polynomial `countPoly` — inner degree `1`, not `n`. -/
theorem modSym_eq_of_countPoly (m : ℕ) (x : Fin n → Bool) :
    modSym m x = modAccept m ((eval (fun i => (if x i then 1 else 0 : ℤ))) countPoly).toNat := by
  rw [eval_countPoly, Int.toNat_natCast, modSym]

end PallLean.Paper93.DeepMath.PathB.CompositeMod

#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.countPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.eval_countPoly
#print axioms PallLean.Paper93.DeepMath.PathB.CompositeMod.modSym_eq_of_countPoly
