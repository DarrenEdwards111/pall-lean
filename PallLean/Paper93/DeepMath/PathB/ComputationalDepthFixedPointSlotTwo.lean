import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNonNaturalSkeleton
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalWeakBound

/-!
# Filling slot 2 with the self-referential fixed-point property — for the fixed point, not for SAT

Slot 2 of the `NonNaturalCertificate` skeleton is the open needle: `P sat`.  The natural candidate is
the **self-referential fixed-point property** — a function that is a fixed point of the diagonalizer,
`Diagonalizes f g : ∀ i, g i = !(f i i)` (g negates each enumerated circuit on its own index).  This
file fills slot 2 with it, honestly, and reports exactly what that achieves.

**It fills all three slots — for the fixed point itself.**  `diag f` satisfies `Diagonalizes f` *by
construction* (`diag_diagonalizes`, `rfl`), so slot 2 closes; the property is useful
(`useful_fp`: a fixed point differs from every enumerated circuit) and rare
(`antidiag_not_diagonalizes`: the anti-diagonal fails it).  `fixedPointCertificate` is therefore a
*complete, non-toy* non-natural certificate — for the fixed point `diag f`.

**But the fixed point is the diagonal, not SAT, and the bound is restricted.**  `works` on it yields
`NotEnumerated f (diag f)` — `diag f` is uncomputed by the *fixed enumeration* `f`.  That is the LINEAR
bound of `DiagonalWeakBound` (against `m+1` circuits), not a superpolynomial one, and `diag f` is a
constructed object, not SAT.

**Slot 2 for SAT is exactly "SAT is the fixed point" — and that is `cost_super`.**  `satCertificate`
produces a certificate for any `sat` *given* `Diagonalizes f sat` — i.e. given that SAT negates every
enumerated circuit, that SAT **is** the diagonal at scale.  That hypothesis is the open input; it is
not proved, and proving it (at superpolynomial scale, for the actual NP-complete SAT) is `cost_super`.

So the fixed-point property works perfectly — for the diagonal, at restricted scale.  It does **not**
fill slot 2 for SAT: that requires SAT to be the self-referential fixed point, which is the wall.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo

open PallLean.Paper93.DeepMath.PathB.NonNaturalSkeleton
open PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound

/-- **The self-referential fixed-point property.**  `g` is a fixed point of the diagonalizer against
enumeration `f`: it negates each enumerated circuit on its own index. -/
def Diagonalizes {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) (g : Fin (m + 1) → Bool) : Prop :=
  ∀ i, g i = !(f i i)

/-- The restricted hardness predicate: `g` is computed by no enumerated circuit. -/
def NotEnumerated {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) (g : Fin (m + 1) → Bool) : Prop :=
  ∀ i, g ≠ f i

/-- **Slot 1 (useful), proved.**  A fixed point differs from every enumerated circuit: if `g`
negates `f i` on index `i`, then `g ≠ f i`. -/
theorem useful_fp {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) (g : Fin (m + 1) → Bool)
    (h : Diagonalizes f g) : NotEnumerated f g := by
  intro i heq
  have hi : g i = !(f i i) := h i
  rw [heq] at hi
  exact absurd hi (by cases f i i <;> decide)

/-- **Slot 2 (high on the fixed point), proved BY CONSTRUCTION.**  `diag f` satisfies the fixed-point
property definitionally — this is what "self-referential fixed point" means. -/
theorem diag_diagonalizes {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) :
    Diagonalizes f (diag f) := fun _ => rfl

/-- **Slot 3 (rare), proved.**  The anti-diagonal `fun j => f j j` — which *agrees* with each circuit's
self-application instead of negating — fails the fixed-point property. -/
theorem antidiag_not_diagonalizes {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) :
    ¬ Diagonalizes f (fun j => f j j) := by
  intro h
  have h0 : f 0 0 = !(f 0 0) := h 0
  exact absurd h0 (by cases f 0 0 <;> decide)

/-- **A complete, non-toy non-natural certificate — for the fixed point `diag f`.**  All three slots
filled: `useful` (proved), `rare` (proved), and `highOnSAT` = `Diagonalizes f (diag f)` (BY
CONSTRUCTION).  The target is `diag f`, the random function is the anti-diagonal, the lower bound is
against the fixed enumeration `f`. -/
def fixedPointCertificate {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) :
    NonNaturalCertificate (diag f) (fun j => f j j) (NotEnumerated f) where
  P := Diagonalizes f
  useful := useful_fp f
  rare := antidiag_not_diagonalizes f
  highOnSAT := diag_diagonalizes f

/-- **The fixed point is hard — against the fixed enumeration (proved).**  `works` on the certificate:
`diag f` is computed by no enumerated circuit.  This is the LINEAR/restricted bound, not
superpolynomial, and `diag f` is a constructed object, not SAT. -/
theorem fixedPoint_is_hard {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) :
    NotEnumerated f (diag f) :=
  works (fixedPointCertificate f)

/-- **Slot 2 for SAT is exactly "SAT is the fixed point" (proved as a reduction).**  Given the OPEN
input `Diagonalizes f sat` — that SAT negates every enumerated circuit, i.e. SAT *is* the diagonal at
scale — a full certificate for `sat` follows.  That hypothesis is `cost_super`: it is not proved here,
and proving it for the actual NP-complete SAT at superpolynomial scale is the wall. -/
def satCertificate {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool) (sat : Fin (m + 1) → Bool)
    (h_sat_is_fixedpoint : Diagonalizes f sat) :
    NonNaturalCertificate sat (fun j => f j j) (NotEnumerated f) where
  P := Diagonalizes f
  useful := useful_fp f
  rare := antidiag_not_diagonalizes f
  highOnSAT := h_sat_is_fixedpoint

/-- **The reduction, made explicit (proved).**  A hardness certificate for `sat` exists iff SAT is the
self-referential fixed point (`Diagonalizes f sat`) — the open slot-2 input for SAT, which is
`cost_super`. -/
theorem sat_hard_of_sat_is_fixedpoint {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → Bool)
    (sat : Fin (m + 1) → Bool) (h_sat_is_fixedpoint : Diagonalizes f sat) :
    NotEnumerated f sat :=
  works (satCertificate f sat h_sat_is_fixedpoint)

end PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo

#print axioms PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo.useful_fp
#print axioms PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo.diag_diagonalizes
#print axioms PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo.antidiag_not_diagonalizes
#print axioms PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo.fixedPoint_is_hard
#print axioms PallLean.Paper93.DeepMath.PathB.FixedPointSlotTwo.sat_hard_of_sat_is_fixedpoint
