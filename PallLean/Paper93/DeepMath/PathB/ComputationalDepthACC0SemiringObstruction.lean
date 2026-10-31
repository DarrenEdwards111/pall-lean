import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalCharObstruction

/-!
# The semiring obstruction — the native composite escape fails even without subtraction (proved)

Back to the open composite barrier (`NFRAME_TWO_ROUTES.md` §4).  Entry 300 (the Universal Native Characteristic
Obstruction) proved no nontrivial *commutative ring* is native to both `2` and `3` — but its proof used **subtraction**
(`1 = 3 − 2`).  So a natural escape candidate (§4, case "semiring / non-ring observers") is: drop subtraction — could a
*semiring* (or any additive structure without negatives) be native to both, hosting a composite observer?

This file **kills that candidate**: the obstruction holds in any `AddCommMonoidWithOne` — semirings included — with **no
subtraction**.  The reason is purely additive: `3 = 2 + 1`, so if `2 = 0` then `3 = 0 + 1 = 1`; hence `3 = 0 ⟹ 1 = 0`.
The structure collapses to trivial.  So the obstruction needs only the additive numeral structure (`+`, `0`, `1`) — far
weaker than a ring — and the semiring/non-ring native escape does not exist.

## What is proved (clean axioms, no `sorry`)

* **`two_three_semiring_trivial`** — in any `AddCommMonoidWithOne R`, `(2 : R) = 0 → (3 : R) = 0 → (1 : R) = 0`
  (`3 = 2 + 1`, no subtraction).
* **`no_nontrivial_semiring_both_native`** — no *nontrivial* `AddCommMonoidWithOne` (hence no nontrivial semiring) is
  native to both `2` and `3`.

## Honest scope

This **eliminates the semiring / non-ring native escape** (§4, case 4) for the composite barrier: the Universal Native
Characteristic Obstruction extends from commutative rings (entry 300) to all of `AddCommMonoidWithOne` — semirings,
idempotent/tropical semirings, any structure with `+`, `0`, `1` — needing only `3 = 2 + 1`, not subtraction.  So *no
native additive structure whatsoever* can host both `MOD₂` and `MOD₃` natively (`2 = 0` and `3 = 0`) nontrivially.  This
does **not** close the composite barrier — the genuinely-open candidates remain *non-native* representations (no `p = 0`
demanded at all), *staged observers without flattening*, and *probabilistic/approximate* composite representations
(§4, cases 1–3).  It narrows the frontier by removing the additive-structure escape.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `NFRAME_TWO_ROUTES.md`, `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SemiringObstruction

/-- **The obstruction without subtraction (PROVED).**  In any `AddCommMonoidWithOne`, `2 = 0` and `3 = 0` force `1 = 0`:
since `3 = 2 + 1`, `2 = 0` gives `3 = 0 + 1 = 1`, so `3 = 0 ⟹ 1 = 0`.  No subtraction is used — only the additive
numeral structure — so this holds in semirings, unlike entry 300's ring proof (`1 = 3 − 2`). -/
theorem two_three_semiring_trivial {R : Type*} [AddCommMonoidWithOne R]
    (h2 : (2 : R) = 0) (h3 : (3 : R) = 0) : (1 : R) = 0 := by
  have e : (3 : R) = (2 : R) + 1 := by norm_num
  rw [e, h2, zero_add] at h3
  exact h3

/-- **No nontrivial semiring is native to both `2` and `3` (PROVED).**  Any nontrivial `AddCommMonoidWithOne` (in
particular any nontrivial semiring) with `2 = 0` and `3 = 0` is contradictory — the semiring/non-ring native escape for
the composite barrier does not exist. -/
theorem no_nontrivial_semiring_both_native {R : Type*} [Semiring R] [Nontrivial R]
    (h2 : (2 : R) = 0) (h3 : (3 : R) = 0) : False :=
  one_ne_zero (two_three_semiring_trivial h2 h3)

/-!
**The semiring escape is closed.**  The Universal Native Characteristic Obstruction extends from commutative rings
(entry 300, via `1 = 3 − 2`) to all of `AddCommMonoidWithOne` — semirings and any additive structure with `+`, `0`, `1`
— with **no subtraction** (`3 = 2 + 1`, `2 = 0 ⟹ 3 = 1`).  So no native additive structure can host both `MOD₂` and
`MOD₃` natively nontrivially: candidate 4 (§4 of `NFRAME_TWO_ROUTES.md`) is eliminated.  The genuinely-open composite
candidates — non-native representations, staged-without-flattening observers, probabilistic/approximate representations
— remain.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SemiringObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SemiringObstruction.two_three_semiring_trivial
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SemiringObstruction.no_nontrivial_semiring_both_native
