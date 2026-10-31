import Mathlib

/-!
# Kummer's carry count via factorization — quantitative carry seam (conservative fragments, proved)

Entry 235 (`…ACC0CarryInvariant`) showed *qualitatively* that the field (mod-`p`) observer is blind to p-adic carries.
This file makes the carry layer **quantitative**, via Kummer's theorem: the number of carries when adding `n` and `k`
in base `p` is the `p`-adic valuation of the binomial coefficient `C(n+k, k)` — a genuine **factorization invariant**.
It proves *safe fragment theorems* tying that invariant to the field-observer seam, again **conservatively**: no global
"obstructs exactification" claim.

⚠️ **Scope discipline.**  These quantify and characterise the carry seam (when a carry is invisible mod `p`).  They do
**not** cross the composite-`ACC⁰[m]` barrier (entry 234) and none is a separation result.

## The invariant (Kummer)

`carryCount p n k := padicValNat p (C(n+k, k))` — by Kummer's theorem the number of base-`p` carries in `n + k`.
Mathlib supplies the digit-sum form of Kummer (`sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`); we re-export it
under this name and derive the seam-relevant fragments.

## What is proved (clean axioms, no `sorry`)

* **`carryCount_digits_identity`** (PROVED, Kummer) — `(p-1) · carryCount p n k = S_p(k) + S_p(n) - S_p(n+k)`, where
  `S_p` is the base-`p` digit sum.  Each carry costs `p-1` in digit sum; this is Kummer/Legendre in digit form.
* **`carryCount_eq_zero_iff_digits`** (PROVED) — `carryCount p n k = 0 ↔ S_p(k) + S_p(n) - S_p(n+k) = 0`: no carry iff
  the digit sums add without loss (using `p - 1 ≠ 0`).
* **`carryCount_eq_zero_iff_not_dvd`** (PROVED) — **the field-observer link**: `carryCount p n k = 0 ↔ ¬ p ∣ C(n+k,k)`.
  No carry ⟺ the binomial is a `p`-adic unit ⟺ it survives mod `p` (the field/weighted-`F_p` observer sees it).
* **`carryCount_pos_iff_dvd`** (PROVED) — the quantitative refinement of entry-235 `field_observer_blind_to_carry`:
  `0 < carryCount p n k ↔ p ∣ C(n+k,k)`.  A carry is present ⟺ `p` divides the binomial ⟺ the count contribution is
  **invisible to the mod-`p` observer** — the carry layer the exact count must recover.

## Honest scope

These are **conservative, quantitative** fragments of the carry seam: Kummer's identity (`carryCount_digits_identity`),
its zero characterisation (`carryCount_eq_zero_iff_digits`), and the field-observer link (`carryCount_eq_zero_iff_not_dvd`
/ `carryCount_pos_iff_dvd`) showing a carry is *exactly* a mod-`p`-invisible binomial divisibility.  Together they
sharpen entry 235: the field observer's blindness is measured by `carryCount`, a factorization invariant.  This
**characterises and quantifies** the seam where weighted-`F_p` and exact-unit-count observers diverge; it does **not**
cross the composite-`ACC⁰[m]` barrier (entry 234), which remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Nat

namespace PallLean.Paper93.DeepMath.PathB.ACC0KummerCarry

/-- **Kummer's carry count (factorization invariant).**  `padicValNat p (C(n+k, k))` — the `p`-adic valuation of the
binomial coefficient, which by Kummer's theorem equals the number of carries when adding `n` and `k` in base `p`. -/
def carryCount (p n k : ℕ) : ℕ := padicValNat p (Nat.choose (n + k) k)

/-- **Kummer's identity in digit-sum form (PROVED).**  `(p-1) · carryCount p n k = S_p(k) + S_p(n) - S_p(n+k)`: each
base-`p` carry reduces the digit sum by `p-1`.  Re-export of Mathlib's
`sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`. -/
theorem carryCount_digits_identity (p n k : ℕ) [Fact p.Prime] :
    (p - 1) * carryCount p n k =
      (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum :=
  sub_one_mul_padicValNat_choose_eq_sub_sum_digits'

/-- **No carry ⟺ digit sums add without loss (PROVED).**  `carryCount p n k = 0 ↔ S_p(k) + S_p(n) - S_p(n+k) = 0`,
from Kummer's identity and `p - 1 ≠ 0` (prime `p ≥ 2`). -/
theorem carryCount_eq_zero_iff_digits (p n k : ℕ) [Fact p.Prime] :
    carryCount p n k = 0 ↔
      (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum = 0 := by
  have hid := carryCount_digits_identity p n k
  have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  constructor
  · intro h; rw [h, mul_zero] at hid; exact hid.symm
  · intro h; rw [h] at hid; exact (Nat.mul_eq_zero.mp hid).resolve_left hp1

/-- **The field-observer link (PROVED).**  `carryCount p n k = 0 ↔ ¬ p ∣ C(n+k, k)`: no carry iff the binomial is a
`p`-adic unit, i.e. it survives mod `p` and the field/weighted-`F_p` observer sees the count contribution. -/
theorem carryCount_eq_zero_iff_not_dvd (p n k : ℕ) [Fact p.Prime] :
    carryCount p n k = 0 ↔ ¬ (p ∣ Nat.choose (n + k) k) := by
  unfold carryCount
  constructor
  · intro h hdvd
    have h1 := one_le_padicValNat_of_dvd (Nat.choose_pos (Nat.le_add_left k n)).ne' hdvd
    omega
  · exact padicValNat.eq_zero_of_not_dvd

/-- **Carry present ⟺ mod-`p`-invisible (PROVED).**  `0 < carryCount p n k ↔ p ∣ C(n+k, k)` — the quantitative
refinement of entry-235 `field_observer_blind_to_carry`: a carry exists exactly when `p` divides the binomial, i.e. the
count contribution vanishes under the mod-`p` observer (the carry layer the exact count must recover). -/
theorem carryCount_pos_iff_dvd (p n k : ℕ) [Fact p.Prime] :
    0 < carryCount p n k ↔ p ∣ Nat.choose (n + k) k := by
  rw [Nat.pos_iff_ne_zero, ne_eq, carryCount_eq_zero_iff_not_dvd, not_not]

end PallLean.Paper93.DeepMath.PathB.ACC0KummerCarry

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0KummerCarry.carryCount_digits_identity
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0KummerCarry.carryCount_eq_zero_iff_digits
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0KummerCarry.carryCount_eq_zero_iff_not_dvd
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0KummerCarry.carryCount_pos_iff_dvd
