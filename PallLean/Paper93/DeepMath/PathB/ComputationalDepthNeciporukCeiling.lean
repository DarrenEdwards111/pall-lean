import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRankContextualWidth

/-!
# The Nečiporuk ceiling — why subfunction counting cannot exceed `n²/log n`

The corpus's Nečiporuk arc reaches the `n²/log n` formula‑size bound on an explicit function and stops there
(`NECIPORUK_STATUS.md`).  This file formalizes the *reason* it stops: the **per‑block subfunction count is capped
two ways**, and the two caps peak together at block size `≈ log n`, giving the `n²/log n` ceiling for the whole
method.  So "explicit formula lower bound above `n²/log n` **via subfunction counting**" is provably impossible —
going above requires a fundamentally different technique (shrinkage / random restrictions → `n^{3-o(1)}` for
Andreev's function, a separate method this file does not attempt).

For a block of `b` variables (with `r = n - b` other variables), the **subfunctions** of `f` on the block are the
distinct restrictions `y ↦ f(y, z)` as the other variables `z` range over all assignments.

## What is proved (clean axioms, no `sorry`)

* `subfunctions_card_le_pow_pow` — `#subfunctions ≤ 2^{2^b}`: a subfunction is a Boolean function of the `b` block
  variables.  Hence `log₂ #subfunctions ≤ 2^b` (`log_subfunctions_le_exp`).
* `subfunctions_card_le_pow` — `#subfunctions ≤ 2^{r}`: there are only `2^{n-b}` settings of the other variables.
  Hence `log₂ #subfunctions ≤ r = n - b` (`log_subfunctions_le_rest`).
* `log_subfunctions_le_min` — the per‑block contribution to the Nečiporuk bound is
  `log₂ #subfunctions ≤ min(2^b, n - b)`.

## The ceiling (the two caps cross at `b ≈ log n`)

The Nečiporuk lower bound is `L(f) ≥ c · ∑_i log₂ #subfunctions(block i)`.  Per block the contribution is
`≤ min(2^{b}, n-b)`:

* small blocks (`b < log₂ n`): the `2^b` cap binds — each contributes `< n`, but there are `n/b` of them;
* large blocks (`b > log₂ n`): the `n-b ≤ n` cap binds — each contributes `≤ n`, but there are only `n/b < n/log n`;
* the two caps **cross at `b ≈ log₂ n`**, where each block contributes `≈ n` and there are `n/log n` blocks, for a
  total `n²/log n`.

For any partition, `∑_i min(2^{b_i}, n-b_i)` is maximized at uniform block size `≈ log₂ n` and equals
`Θ(n²/log n)` — the method ceiling, achieved by the corpus's explicit `hardF` (`…NeciporukOptimalBound`).  No
function exceeds it, because **the per‑block count is bounded by `min(2^b, n-b)` regardless of `f`**.  This file
proves that per‑block min‑cap; the cross‑partition optimization to `n²/log n` is the standard convexity argument.

## Honest scope

This is the *barrier* that closes the explicit‑Nečiporuk frontier: subfunction counting provably tops out at
`n²/log n`.  It is a genuine restricted formula‑size ceiling, not a `P ≠ NP` statement, and the path to explicit
super‑`n²/log n` bounds (shrinkage / Andreev `n^{3-o(1)}`) is a different method — recorded here as the named next
target, not attempted.
-/

namespace PallLean.Paper93.DeepMath.PathB.NeciporukCeiling

variable {b r : ℕ}

/-- The **subfunctions** of `f` on a `b`‑variable block: the distinct restrictions `y ↦ f(y, z)` as the other `r`
variables `z` range over all assignments. -/
def subfunctions (f : (Fin b → Bool) × (Fin r → Bool) → Bool) : Finset ((Fin b → Bool) → Bool) :=
  Finset.univ.image (fun z : Fin r → Bool => fun y => f (y, z))

/-- **Cap 1 (proved): `#subfunctions ≤ 2^{2^b}`.**  A subfunction is one of the `2^{2^b}` Boolean functions of the
`b` block variables. -/
theorem subfunctions_card_le_pow_pow (f : (Fin b → Bool) × (Fin r → Bool) → Bool) :
    (subfunctions f).card ≤ 2 ^ (2 ^ b) := by
  unfold subfunctions
  calc (Finset.univ.image (fun z : Fin r → Bool => fun y => f (y, z))).card
      ≤ (Finset.univ : Finset ((Fin b → Bool) → Bool)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = 2 ^ (2 ^ b) := by
        rw [Finset.card_univ]
        simp [Fintype.card_bool, Fintype.card_fin]

/-- **Cap 2 (proved): `#subfunctions ≤ 2^{r}`.**  There are only `2^{n-b}` settings of the other variables. -/
theorem subfunctions_card_le_pow (f : (Fin b → Bool) × (Fin r → Bool) → Bool) :
    (subfunctions f).card ≤ 2 ^ r := by
  unfold subfunctions
  calc (Finset.univ.image (fun z : Fin r → Bool => fun y => f (y, z))).card
      ≤ (Finset.univ : Finset (Fin r → Bool)).card := Finset.card_image_le
    _ = 2 ^ r := by
        rw [Finset.card_univ]
        simp [Fintype.card_bool, Fintype.card_fin]

/-- **`log₂ #subfunctions ≤ 2^b` (proved).** -/
theorem log_subfunctions_le_exp (f : (Fin b → Bool) × (Fin r → Bool) → Bool) :
    Nat.log 2 (subfunctions f).card ≤ 2 ^ b := by
  calc Nat.log 2 (subfunctions f).card
      ≤ Nat.log 2 (2 ^ (2 ^ b)) := Nat.log_mono_right (subfunctions_card_le_pow_pow f)
    _ = 2 ^ b := Nat.log_pow (show (1 : ℕ) < 2 by decide) (2 ^ b)

/-- **`log₂ #subfunctions ≤ n - b` (proved).** -/
theorem log_subfunctions_le_rest (f : (Fin b → Bool) × (Fin r → Bool) → Bool) :
    Nat.log 2 (subfunctions f).card ≤ r := by
  calc Nat.log 2 (subfunctions f).card
      ≤ Nat.log 2 (2 ^ r) := Nat.log_mono_right (subfunctions_card_le_pow f)
    _ = r := Nat.log_pow (show (1 : ℕ) < 2 by decide) r

/-- **The Nečiporuk per‑block ceiling (proved): `log₂ #subfunctions ≤ min(2^b, n-b)`.**  Regardless of `f`, a
block of `b` variables contributes at most `min(2^b, n-b)` to the bound — the two caps that cross at `b ≈ log n`
and force the whole method to `n²/log n`. -/
theorem log_subfunctions_le_min (f : (Fin b → Bool) × (Fin r → Bool) → Bool) :
    Nat.log 2 (subfunctions f).card ≤ min (2 ^ b) r :=
  le_min (log_subfunctions_le_exp f) (log_subfunctions_le_rest f)

end PallLean.Paper93.DeepMath.PathB.NeciporukCeiling

#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCeiling.subfunctions_card_le_pow_pow
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCeiling.subfunctions_card_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCeiling.log_subfunctions_le_min
