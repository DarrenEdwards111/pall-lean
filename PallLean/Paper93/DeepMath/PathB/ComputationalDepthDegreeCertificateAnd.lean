import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDegreeCertificate

/-!
# Instantiating the log bound: the AND family has high GF(2)-degree

The `n`-bit AND `andN` has GF(2)-degree exactly `n` — its `n`-fold mixed finite difference over the `n`
unit directions is the constant top coefficient `1`.  Feeding that certificate into
`DegreeCertificate.highDegree_needs_nonlinear` gives, for `n = 2^m+1`, a lower bound of `m+1` nonlinear
gates on *any* circuit computing `andN`.

* **`andN` / `unitVec`** — the `n`-bit AND and the unit directions.
* **`andN_needs_nonlinear_3` (proved)** — any circuit computing the `3`-bit AND has `≥ 2` nonlinear
  gates.  (Tight: `3`-bit AND has multiplicative complexity exactly `2`.)
* **`andN_needs_nonlinear_5` (proved)** — the `5`-bit AND needs `≥ 3` nonlinear gates.
* **`andN_needs_nonlinear_9` (proved)** — the `9`-bit AND needs `≥ 4` nonlinear gates.

So the log lower bound `nlCount ≥ ⌊log₂ n⌋ + 1` is realized on a concrete family — machine-checked,
unconditional, and growing with `n`.

**Honest scope.**  These are real unconditional lower bounds on the *nonlinear-gate count* of AND
circuits, established via the degree machinery.  They are only **logarithmic** in `n` (that is all the
degree method gives — the `n`-bit AND actually needs `n-1` nonlinear gates), and they bound the
nonlinear-gate count, not the total gate count.  The general size lower bound `cost_super` needs — the
full Uhlig no-sharing bound — remains the open wall.  The instances here are specific `n`; the uniform
family bound follows the same `decide` certificate at each `n = 2^m+1`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DegreeCertificateAnd

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.WireDegreeBound
open PallLean.Paper93.DeepMath.PathB.DegreeCertificate

/-- The `n`-bit AND. -/
def andN {n : ℕ} : (Fin n → Bool) → Bool := fun x => decide (∀ i, x i = true)

/-- The `i`-th unit direction. -/
def unitVec {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

/-- **The `3`-bit AND needs `≥ 2` nonlinear gates (proved).**  Tight. -/
theorem andN_needs_nonlinear_3 (c : List (CGate 3)) (hc : output c = andN) : 2 ≤ nlCount c := by
  have h := highDegree_needs_nonlinear c 1 [unitVec 0, unitVec 1, unitVec 2] (fun _ => true)
    (by decide) (by rw [hc]; decide)
  omega

/-- **The `5`-bit AND needs `≥ 3` nonlinear gates (proved).** -/
theorem andN_needs_nonlinear_5 (c : List (CGate 5)) (hc : output c = andN) : 3 ≤ nlCount c := by
  have h := highDegree_needs_nonlinear c 2
    [unitVec 0, unitVec 1, unitVec 2, unitVec 3, unitVec 4] (fun _ => true)
    (by decide) (by rw [hc]; decide)
  omega

/-- **The `9`-bit AND needs `≥ 4` nonlinear gates (proved).** -/
theorem andN_needs_nonlinear_9 (c : List (CGate 9)) (hc : output c = andN) : 4 ≤ nlCount c := by
  have h := highDegree_needs_nonlinear c 3
    [unitVec 0, unitVec 1, unitVec 2, unitVec 3, unitVec 4, unitVec 5, unitVec 6, unitVec 7, unitVec 8]
    (fun _ => true) (by decide) (by rw [hc]; decide)
  omega

end PallLean.Paper93.DeepMath.PathB.DegreeCertificateAnd

#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCertificateAnd.andN_needs_nonlinear_3
#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCertificateAnd.andN_needs_nonlinear_5
#print axioms PallLean.Paper93.DeepMath.PathB.DegreeCertificateAnd.andN_needs_nonlinear_9
