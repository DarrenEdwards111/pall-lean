import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiBase

/-!
# Beigel–Tarui, rung 6: degree composition through a bounded-depth formula

The polynomial method controls a circuit's degree by composing per-gate polynomials.  This file proves the
**composition bookkeeping** for the *exact* arithmetisation of rung 1: the polynomial of an `AND`/`OR`/`NOT` formula has
total degree at most its **leaf count**, hence at most `2^depth`.  Both `AND` (product: degrees add) and `OR`
(`x+y-xy`: degree `= deg x + deg y`) add degrees, so the arithmetisation degree accumulates additively over the formula
— the skeleton the Razborov–Smolensky per-gate *low-degree* approximators (rungs 2–5) plug into.

  `arithP` — the formula's arithmetisation as an `MvPolynomial` (`X i`, `1-·`, `·`, inclusion–exclusion).
  `eval_arithP` — **PROVED**: `arithP` evaluates to the Boolean function on Boolean inputs (the polynomial computes the
        formula).
  `numLeaves` / `depth` — the leaf count and depth of a formula.
  `arithP_totalDegree_le` — **PROVED**: the arithmetisation degree is at most the leaf count — degrees add through
        `AND`/`OR`.
  `arithP_totalDegree_le_two_pow_depth` — **PROVED**: hence at most `2^depth` — the exact-arithmetisation depth bound.

## Honest scope

This is the composition for the **exact** arithmetisation: degree `≤ 2^depth`, which for a depth-`d` circuit of size `s`
is `≤ s` — no low-degree gain.  The Beigel–Tarui / Razborov–Smolensky *degree reduction* comes from substituting, at each
gate, the **low-degree probabilistic approximator** (rung 2's degree `t(p-1)`, rung 4's `2^{-t}` error, rung 5's
existence) instead of the exact gate polynomial: the same additive/multiplicative degree bookkeeping proved here then
gives degree `(t(p-1))^depth = polylog` for the whole circuit, at the cost of a per-gate error that the rung-4/5 union
bound over the `size` gates keeps small.  Wiring that probabilistic substitution through this composition skeleton, and
folding the result into one `SYM∘AND` with `m` quasipolynomial, is the remaining Beigel–Tarui content.  This file
supplies the composition skeleton.  Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

open MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The arithmetisation of a formula as an `MvPolynomial`. -/
noncomputable def arithP : BForm n → MvPolynomial (Fin n) R
  | .var i => X i
  | .bnot a => 1 - arithP a
  | .band a b => arithP a * arithP b
  | .bor a b => arithP a + arithP b - arithP a * arithP b

/-- **The polynomial computes the formula (proved)**: `arithP f` evaluates to the Boolean value of `f` on every Boolean
input. -/
theorem eval_arithP (f : BForm n) (x : Fin n → Bool) :
    (eval (fun i => (embed (x i) : R))) (arithP f) = embed (f.eval x) := by
  induction f with
  | var i => simp [arithP, BForm.eval, embed]
  | bnot a ih => rw [arithP, map_sub, map_one, ih, embed_not, BForm.eval]
  | band a b iha ihb => rw [arithP, map_mul, iha, ihb, embed_and, BForm.eval]
  | bor a b iha ihb =>
      rw [arithP, map_sub, map_add, map_mul, iha, ihb, embed_or, BForm.eval]

/-- The number of variable-leaves of a formula. -/
def numLeaves : BForm n → ℕ
  | .var _ => 1
  | .bnot a => numLeaves a
  | .band a b => numLeaves a + numLeaves b
  | .bor a b => numLeaves a + numLeaves b

/-- The depth of a formula. -/
def depth : BForm n → ℕ
  | .var _ => 0
  | .bnot a => depth a + 1
  | .band a b => max (depth a) (depth b) + 1
  | .bor a b => max (depth a) (depth b) + 1

/-- **Degree composes additively (proved)**: the arithmetisation degree is at most the leaf count — both `AND` (product)
and `OR` (`x+y-xy`) add the degrees of their inputs. -/
theorem arithP_totalDegree_le [Nontrivial R] (f : BForm n) :
    (arithP (R := R) f).totalDegree ≤ numLeaves f := by
  induction f with
  | var i => simp only [arithP, numLeaves]; exact (totalDegree_X i).le
  | bnot a ih =>
      refine le_trans (le_trans (totalDegree_sub 1 _) ?_) ih
      simp only [totalDegree_one]; omega
  | band a b iha ihb =>
      exact le_trans (totalDegree_mul _ _) (Nat.add_le_add iha ihb)
  | bor a b iha ihb =>
      refine le_trans (totalDegree_sub _ _) (max_le (le_trans (totalDegree_add _ _) (max_le ?_ ?_))
        (le_trans (totalDegree_mul _ _) (Nat.add_le_add iha ihb)))
      · exact le_trans iha (Nat.le_add_right _ _)
      · exact le_trans ihb (Nat.le_add_left _ _)

/-- The leaf count is at most `2^depth`. -/
theorem numLeaves_le_two_pow_depth (f : BForm n) : numLeaves f ≤ 2 ^ depth f := by
  induction f with
  | var i => simp [numLeaves, depth]
  | bnot a ih =>
      simp only [numLeaves, depth]
      exact le_trans ih (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
  | band a b iha ihb =>
      simp only [numLeaves, depth]
      calc numLeaves a + numLeaves b
          ≤ 2 ^ max (depth a) (depth b) + 2 ^ max (depth a) (depth b) :=
            Nat.add_le_add (le_trans iha (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
              (le_trans ihb (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)))
        _ = 2 ^ (max (depth a) (depth b) + 1) := by rw [pow_succ]; ring
  | bor a b iha ihb =>
      simp only [numLeaves, depth]
      calc numLeaves a + numLeaves b
          ≤ 2 ^ max (depth a) (depth b) + 2 ^ max (depth a) (depth b) :=
            Nat.add_le_add (le_trans iha (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)))
              (le_trans ihb (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)))
        _ = 2 ^ (max (depth a) (depth b) + 1) := by rw [pow_succ]; ring

/-- **The exact-arithmetisation depth bound (proved)**: the arithmetisation degree is at most `2^depth`. -/
theorem arithP_totalDegree_le_two_pow_depth [Nontrivial R] (f : BForm n) :
    (arithP (R := R) f).totalDegree ≤ 2 ^ depth f :=
  le_trans (arithP_totalDegree_le f) (numLeaves_le_two_pow_depth f)

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.eval_arithP
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.arithP_totalDegree_le_two_pow_depth
