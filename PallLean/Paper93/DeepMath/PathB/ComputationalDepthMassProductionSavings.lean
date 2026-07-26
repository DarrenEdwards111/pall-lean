import Mathlib.Data.Nat.Basic

/-!
# The mass-production savings bound: the exact threshold the wall turns on

`ReadKOneStep` localized the entire remaining gap to one phenomenon — **Uhlig mass production**: the two
copies of `composite d` on disjoint input blocks might be computed *together* for fewer than `2·c d`
gates.  This file goes at the savings quantitatively.

Write the per-step savings `save d` by `c (d+1) + save d = 2 · c d`.  Two extremes bound it:

* `save d = 0` — no sharing: `c (d+1) = 2 · c d`, the formula/tree doubling (`2^d`).
* `save d = c d` — a *full copy* saved: `c (d+1) = c d`, flat, no growth (mass production wins).

and `save d ∈ [0, c d]` whenever the composite computes `composite d` at least once.

## What is proved

* **`no_saving_doubles` / `full_saving_flat` / `saving_le_copy` (proved)** — the two extremes and the
  `save d ≤ c d` bound.
* **`geometric_growth` (proved)** — **the core**: if the savings leave *any* multiplicative growth
  (ratio `≥ p/q > 1`, i.e. `p · c d ≤ q · c (d+1)`), then `c` blows up geometrically:
  `p^d · c 0 ≤ q^d · c d`.  At `p = 2, q = 1` this is the tree doubling `2^d ≤ c d`; for any `p/q > 1` it
  is superpolynomial.  **Any saving bounded away from a full copy gives a superpoly lower bound.**

## The dichotomy — and the honest frontier

So the wall is a single threshold on the savings:

* if mass production saves **less than a full copy** by a fixed ratio (`c (d+1) ≥ (p/q)·c d`, `p/q > 1`),
  `geometric_growth` gives `c d ≥ (p/q)^d` — superpoly — and the separation follows;
* if it saves a **full copy** (`save d = c d`), `full_saving_flat` gives `c (d+1) = c d` — flat — and no
  separation follows.

The **open** question — the wall itself — is *which side the composite tower is on*: can Uhlig's 2-copy
mass production actually save a full copy per step for the tower functions?  Uhlig (1974) shows mass
production of *many* copies can save almost everything; the *two-copy, per-step* quantity for these
composites is exactly `cost_super` and is **not resolved here**.

**Honest scope.**  This does not resolve Uhlig and is not `P ≠ NP`.  It proves the *dichotomy* and pins
the exact threshold — a single full copy of savings — that decides the separation, and shows any
sub-threshold saving already forces superpoly growth.  It sharpens the wall to one number.
-/

namespace PallLean.Paper93.DeepMath.PathB.MassProductionSavings

/-- **No savings ⟹ doubling (proved).**  With `c (d+1) + save d = 2·c d`, zero savings gives the
formula/tree doubling `c (d+1) = 2·c d`. -/
theorem no_saving_doubles (c save : ℕ → ℕ) (hsave : ∀ d, c (d + 1) + save d = 2 * c d)
    (d : ℕ) (h0 : save d = 0) : c (d + 1) = 2 * c d := by
  have := hsave d; omega

/-- **A full copy saved ⟹ flat (proved).**  If mass production saves an entire copy (`save d = c d`),
the cost does not grow: `c (d+1) = c d`.  This is the extreme where mass production wins. -/
theorem full_saving_flat (c save : ℕ → ℕ) (hsave : ∀ d, c (d + 1) + save d = 2 * c d)
    (d : ℕ) (hfull : save d = c d) : c (d + 1) = c d := by
  have := hsave d; omega

/-- **Savings cannot exceed a full copy (proved).**  If the composite computes `composite d` at least
once (`c d ≤ c (d+1)`), then `save d ≤ c d`. -/
theorem saving_le_copy (c save : ℕ → ℕ) (hsave : ∀ d, c (d + 1) + save d = 2 * c d)
    (d : ℕ) (hmono : c d ≤ c (d + 1)) : save d ≤ c d := by
  have := hsave d; omega

/-- **The core: bounded savings compound multiplicatively (proved).**  If the savings leave a growth
ratio of at least `p/q` (`p · c d ≤ q · c (d+1)` at every step), then `p^d · c 0 ≤ q^d · c d`.  For
`p/q > 1` this is geometric blow-up; at `p = 2, q = 1` it is the tree's `2^d`.  Any saving bounded away
from a full copy forces a superpolynomial lower bound. -/
theorem geometric_growth (c : ℕ → ℕ) (p q : ℕ)
    (hstep : ∀ d, p * c d ≤ q * c (d + 1)) (d : ℕ) : p ^ d * c 0 ≤ q ^ d * c d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    calc p ^ d * p * c 0
        = p * (p ^ d * c 0) := by rw [Nat.mul_comm (p ^ d) p, Nat.mul_assoc]
      _ ≤ p * (q ^ d * c d) := Nat.mul_le_mul (Nat.le_refl p) ih
      _ = q ^ d * (p * c d) := by rw [← Nat.mul_assoc, Nat.mul_comm p (q ^ d), Nat.mul_assoc]
      _ ≤ q ^ d * (q * c (d + 1)) := Nat.mul_le_mul (Nat.le_refl (q ^ d)) (hstep d)
      _ = q ^ d * q * c (d + 1) := by rw [← Nat.mul_assoc]

end PallLean.Paper93.DeepMath.PathB.MassProductionSavings

#print axioms PallLean.Paper93.DeepMath.PathB.MassProductionSavings.no_saving_doubles
#print axioms PallLean.Paper93.DeepMath.PathB.MassProductionSavings.full_saving_flat
#print axioms PallLean.Paper93.DeepMath.PathB.MassProductionSavings.saving_le_copy
#print axioms PallLean.Paper93.DeepMath.PathB.MassProductionSavings.geometric_growth
