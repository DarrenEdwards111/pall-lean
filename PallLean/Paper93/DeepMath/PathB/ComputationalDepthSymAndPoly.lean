import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSymAnd
import Mathlib

/-!
# The AND gate as a genuine `MvPolynomial` (PROVED) — the polynomial method, made precise

`ComputationalDepthSymAnd` represented an `AND` gate's value as a concrete product of `0/1` indicators.  Here we
lift that to an actual multivariate polynomial `andPoly g : MvPolynomial (Fin n) ℤ`, and prove the two facts the
polynomial method rests on:

* `andPoly_eval` — the polynomial is a **faithful representation**: evaluated at a Boolean point it equals the
  gate's value `[g fires]`.
* `andPoly_totalDegree_le` — its **total degree is at most the fan-in** `gateDegree g` (the number of literals).

So an `AND` of `d` literals is exactly a degree-`d` polynomial.  Summing over the gates, the firing count of a
`SYM∘AND` circuit is represented by a polynomial of degree = the maximum fan-in — the algebraic object on which
the Razborov–Smolensky / Williams machinery (low-degree approximation of `OR`/`MOD`, fast evaluation) operates.
This is real, unconditional polynomial-method infrastructure; the deep theorems (low-degree approximation, the
degree lower bound, Beigel–Tarui) remain cited axioms / targets.
-/

open MvPolynomial

namespace PallLean.Paper93.DeepMath.PathB.SymAnd

variable {n : ℕ}

/-- The literal polynomial for gate `g` at variable `i`, over `ℤ`: `1` if unconstrained, `Xᵢ` for a positive
literal, `1 - Xᵢ` for a negative one.  Degree `≤ 1`. -/
noncomputable def litPoly (g : AndGate n) (i : Fin n) : MvPolynomial (Fin n) ℤ :=
  match g i with
  | none => 1
  | some true => X i
  | some false => 1 - X i

/-- The polynomial of an `AND` gate: the product of its literal polynomials. -/
noncomputable def andPoly (g : AndGate n) : MvPolynomial (Fin n) ℤ := ∏ i, litPoly g i

/-- A Boolean input as a `0/1` point in `ℤ`. -/
def boolPt (x : Fin n → Bool) : Fin n → ℤ := fun i => (x i).toNat

/-- Each literal polynomial evaluates to its `0/1` indicator. -/
theorem litPoly_eval (g : AndGate n) (i : Fin n) (x : Fin n → Bool) :
    eval (boolPt x) (litPoly g i) = (litIndicator g i x : ℤ) := by
  rcases hgi : g i with _ | b
  · simp [litPoly, litIndicator, litHolds, hgi]
  · cases b <;> cases hx : x i <;>
      simp [litPoly, litIndicator, litHolds, boolPt, hgi, hx, eval_X, map_sub, map_one]

/-- **Faithful representation.**  The `AND` polynomial, evaluated at a Boolean point, equals the gate's value
`[g fires]` — the polynomial *computes* the gate exactly on `{0,1}ⁿ`. -/
theorem andPoly_eval (g : AndGate n) (x : Fin n → Bool) :
    eval (boolPt x) (andPoly g) = ((andEval g x).toNat : ℤ) := by
  rw [andPoly, map_prod, andEval_eq_prod, Nat.cast_prod]
  exact Finset.prod_congr rfl (fun i _ => litPoly_eval g i x)

/-- A literal polynomial has total degree `≤ 1`. -/
theorem litPoly_totalDegree_le (g : AndGate n) (i : Fin n) :
    (litPoly g i).totalDegree ≤ 1 := by
  unfold litPoly
  split <;>
    first
    | simp [totalDegree_X, totalDegree_one]
    | (refine le_trans (totalDegree_sub _ _) ?_; simp [totalDegree_X, totalDegree_one])

/-- **Degree = fan-in.**  The `AND` polynomial has total degree at most `gateDegree g`, the number of literals:
the unconstrained variables contribute degree `0`, each literal degree `1`.  So an `AND` of `d` literals is a
degree-`d` polynomial. -/
theorem andPoly_totalDegree_le (g : AndGate n) :
    (andPoly g).totalDegree ≤ gateDegree g := by
  refine le_trans (totalDegree_finset_prod _ _) ?_
  rw [gateDegree, Finset.card_filter]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rcases hgi : g i with _ | b
  · simp [litPoly, hgi, totalDegree_one]
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true]
    exact litPoly_totalDegree_le g i

end PallLean.Paper93.DeepMath.PathB.SymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.andPoly_eval
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.andPoly_totalDegree_le
