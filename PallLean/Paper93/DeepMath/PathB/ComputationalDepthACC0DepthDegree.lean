import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DegreeCompose

/-!
# Brick C-iterate — depth-`d` composition keeps degree `≤ D^d` (proved)

Iterating the substitution degree bound (Brick C, `totalDegree_bind₁_le`) across `d` layers: a depth-`d` composition of
degree-`≤ D` substitutions has total degree `≤ (initial degree) · D^d`.  For a *constant* depth `d` and `D = polylog`, this
is `polylog` — and Brick D (`degLeMonomials_card_le`) then caps the monomials at `(n+1)^{D^d}` = quasipolynomial `< 2^n`.
This is the exact degree control the Yao–Beigel–Tarui normal form needs over constant-depth `ACC⁰`.

Note: `totalDegree_bind₁_le` (and hence this iterate) holds over **any** `CommSemiring R` — in particular the CRT product
ring `∏ ZMod pᵢ` of Brick A.1.  So the **cross-prime** case (different-modulus `MOD` gates, where the single field is proven
dead) needs no new degree lemma: the composition runs over the product ring.

## What is proved (clean axioms, no `sorry`)

* **`totalDegree_bind₁_iterate`** (PROVED) — `(∀ i, (g i).totalDegree ≤ D) → ((bind₁ g)^[d] P).totalDegree ≤ P.totalDegree
  · D^d`: the depth-`d` degree bound, by induction on `d` over Brick C.

## Honest scope

This is the **depth-degree wiring** (degree `≤ D^d` over constant depth, any ring including CRT products).  It does **not**
prove the prime-power (`e≥2`) Toda lifting (the genuinely hard remaining classical theorem — *not* socketed here), nor the
final assembly of `degree^d` + Brick D + the `SYM∘AND` form into `composite_BT_degree` over an actual `ACC0Circuit`.  General
YBT / `composite_BT_degree` remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DepthDegree

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- **Depth-`d` composition keeps degree `≤ D^d` (PROVED).** -/
theorem totalDegree_bind₁_iterate (g : σ → MvPolynomial σ R) (D : ℕ) (hg : ∀ i, (g i).totalDegree ≤ D)
    (P : MvPolynomial σ R) (d : ℕ) :
    ((bind₁ g)^[d] P).totalDegree ≤ P.totalDegree * D ^ d := by
  induction d with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ, ← mul_assoc]
      calc (bind₁ g ((bind₁ g)^[k] P)).totalDegree
          ≤ ((bind₁ g)^[k] P).totalDegree * D :=
            ACC0DegreeCompose.totalDegree_bind₁_le g _ D hg
        _ ≤ P.totalDegree * D ^ k * D := by gcongr

/-!
**The depth-degree wiring, proved.**  Constant-depth composition keeps the degree at `≤ D^d` (polylog), over any ring —
including the CRT product ring, so cross-prime composition needs no new degree lemma.  Combined with Brick D, the composed
circuit has `≤ (n+1)^{D^d}` `AND`-terms, quasipolynomial.  Remaining for general YBT: the prime-power Toda lifting (hard,
*not* socketed) and the final `ACC0Circuit`-level assembly.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0DepthDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthDegree.totalDegree_bind₁_iterate
