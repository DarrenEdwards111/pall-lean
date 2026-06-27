import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSymAnd
import Mathlib

/-!
# MOD gates and the modular polynomial representation (PROVED) — Razborov–Smolensky core

The polynomial method's modular side: over the field `𝔽_p`, the `MOD_p` gate is **exactly** a low-degree
polynomial.  The algebraic heart is Fermat's little theorem — in a finite field of order `q`, the zero-indicator
`[y = 0]` equals `1 - y^(q-1)`, a degree-`(q-1)` polynomial.

  `indicator_zero_eq` — `[y = 0] = 1 - y^(q-1)` in any finite field of order `q` (the field zero-indicator).
  `modPoly_eval` — `MOD_p` on Boolean inputs is computed exactly on `{0,1}ⁿ` by the polynomial
        `1 - (Σᵢ Xᵢ)^(p-1)` over `𝔽_p`.
  `modPoly_totalDegree_le` — that polynomial has total degree `≤ p - 1`.

So `MOD_p` is a degree-`(p-1)` `𝔽_p`-polynomial — the *easy, exact* direction of Razborov–Smolensky.  The hard
directions — that `MOD_q` (`q` coprime to `p`) and `OR` are **not** low degree over `𝔽_p` (the lower bound), and
the probabilistic low-degree approximation of `OR`/`AND` — remain the genuine open theorems (cited
axioms/targets); this builds the exact-representation infrastructure honestly.
-/

open MvPolynomial

namespace PallLean.Paper93.DeepMath.PathB.SymAnd

/-- **The field zero-indicator is a degree-`(q-1)` polynomial.**  For `y` in a finite field of order `q`,
`[y = 0] = 1 - y^(q-1)` (Fermat: `y^(q-1) = 1` for `y ≠ 0`, and `0^(q-1) = 0`).  This is exactly why `MOD_p` has
low degree over `𝔽_p`. -/
theorem indicator_zero_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K] (y : K) :
    (if y = 0 then (1 : K) else 0) = 1 - y ^ (Fintype.card K - 1) := by
  by_cases h : y = 0
  · subst h
    have hq : Fintype.card K - 1 ≠ 0 := by
      have h2 : 1 < Fintype.card K := Fintype.one_lt_card
      omega
    simp [zero_pow hq]
  · rw [if_neg h, FiniteField.pow_card_sub_one_eq_one y h]; ring

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The input-weight of a Boolean assignment, read in `𝔽_p`: `Σᵢ xᵢ`. -/
def modSum (x : Fin n → Bool) : ZMod p := ∑ i, ((x i).toNat : ZMod p)

/-- The `MOD_p` gate: fires iff the number of true inputs is `≡ 0 (mod p)`. -/
def modGateBool (x : Fin n → Bool) : Bool := decide (modSum p n x = 0)

/-- The `MOD_p` polynomial over `𝔽_p`: `1 - (Σᵢ Xᵢ)^(p-1)`. -/
noncomputable def modPoly : MvPolynomial (Fin n) (ZMod p) := 1 - (∑ i, X i) ^ (p - 1)

/-- **Faithful representation of `MOD_p`.**  Evaluated at a Boolean point, the polynomial `1 - (Σ Xᵢ)^(p-1)`
equals the `MOD_p` indicator `[Σ xᵢ ≡ 0 (mod p)]` — exact on `{0,1}ⁿ`. -/
theorem modPoly_eval (x : Fin n → Bool) :
    eval (fun i => ((x i).toNat : ZMod p)) (modPoly p n)
      = if modSum p n x = 0 then 1 else 0 := by
  rw [indicator_zero_eq, ZMod.card, modPoly, map_sub, map_one, map_pow, map_sum]
  simp only [eval_X]
  rfl

/-- **`MOD_p` is a degree-`(p-1)` polynomial.**  The representing polynomial has total degree `≤ p - 1`: a sum of
variables has degree `≤ 1`, its `(p-1)`-th power degree `≤ p - 1`, and subtracting the constant `1` does not
raise it. -/
theorem modPoly_totalDegree_le : (modPoly p n).totalDegree ≤ p - 1 := by
  rw [modPoly]
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  refine max_le (Nat.zero_le _) ?_
  refine le_trans (totalDegree_pow _ _) ?_
  have hsum : (∑ i, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree ≤ 1 := by
    refine le_trans (totalDegree_finset_sum _ _) ?_
    refine Finset.sup_le (fun i _ => ?_)
    simp [totalDegree_X]
  calc (p - 1) * (∑ i, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree
      ≤ (p - 1) * 1 := by exact Nat.mul_le_mul_left _ hsum
    _ = p - 1 := by ring

end PallLean.Paper93.DeepMath.PathB.SymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.indicator_zero_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.modPoly_eval
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.modPoly_totalDegree_le
