import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pFoundations
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.ZMod.Basic

/-!
# Layer 3 — Razborov–Smolensky low-degree approximation: the single-form test (degree atom)

The exact representation (`…AC0pPoly*`) is high-degree (`∧`/`∨` have degree = fan-in).  The lower bound
comes from the **low-degree approximation** (`SCOPE_LAYER3_RS_APPROXIMATION.md`): replace each `∨`/`∧`
gate by a *probabilistic* polynomial of degree `O((p-1)·log(1/ε))` agreeing on a `1-ε` fraction.

This file builds the **atom** of that construction — a single random-linear-form "zero test" — and its
**total-degree bound**:

* `linFormTest p r` — `1 - (∑_i r_i · X_i)^(p-1)`, the Fermat indicator of "the random linear form
  `∑ r_i x_i` is zero".  (For a `{0,1}` input that is *not* all-zero, the form is nonzero with
  probability `≥ 1 - 1/p` over random `r` — the *agreement* half, deferred; this file is the degree.)
* `linFormTest_totalDegree_le` — `totalDegree (linFormTest p r) ≤ p - 1`.

A product of `t` such tests has degree `≤ (p-1)·t`; that is the degree side of the OR-approximator.  No
lower bound, no capstone.  AC⁰[p] is a higher circuit-lower-bound layer; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial

variable {m : ℕ}

/-- A single random-linear-form **zero test**: `1 - (∑_i r_i · X_i)^(p-1)`.  Over a prime field this is
the Fermat indicator of "`∑ r_i x_i = 0`" (`fermat_indicator`), the atom of the OR-approximator. -/
noncomputable def linFormTest (p : ℕ) (r : Fin m → ZMod p) : MvPolynomial (Fin m) (ZMod p) :=
  1 - (∑ i, C (r i) * X i) ^ (p - 1)

/-- **Degree of the single-form test:** `totalDegree (linFormTest p r) ≤ p - 1`. -/
theorem linFormTest_totalDegree_le (p : ℕ) [Fact p.Prime] (r : Fin m → ZMod p) :
    (linFormTest p r).totalDegree ≤ p - 1 := by
  have hform : (∑ i : Fin m, C (r i) * X i).totalDegree ≤ 1 := by
    refine le_trans (totalDegree_finset_sum _ _) (Finset.sup_le fun i _ => ?_)
    refine le_trans (totalDegree_mul _ _) ?_
    rw [totalDegree_C, zero_add]
    exact le_of_eq (totalDegree_X i)
  have hpow : ((∑ i : Fin m, C (r i) * X i) ^ (p - 1)).totalDegree ≤ p - 1 := by
    refine le_trans (totalDegree_pow _ _) ?_
    calc (p - 1) * (∑ i : Fin m, C (r i) * X i).totalDegree
        ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ hform
      _ = p - 1 := Nat.mul_one _
  rw [linFormTest]
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  simpa using hpow

end PallLean.Paper93.DeepMath.PathB.Layer3
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.linFormTest_totalDegree_le
