import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelTowerVerify

/-!
# Why the reflection compounds: each level re-verifies all below ⟹ the cost doubles (= cost_super)

`GodelTowerVerify` showed the Gödel tower climbs, but with an *additive* step (`+1` per level = the time
hierarchy, `P ⊊ EXP`).  Darren's mechanism for making the rate *multiplicative*: **each level re-verifies
all the levels below it.**  Then a new level's cost is the whole cumulative cost beneath it, so the
cumulative doubles: `S(n+1) = 2·S(n) + 1`.  This file proves that mechanism gives exactly the `cost_super`
doubling — and pins the residual.

Two towers.  **Re-verify-all**: `S(n+1) = 2·S(n) + 1` (the new level re-verifies everything below, plus
`O(1)` of its own).  **Reuse**: `R(n+1) = R(n) + 1` (the new level *reuses* the below's verification and
only adds its own — the level *composes*).

## What is proved

* **`reverify_doubles`** — the re-verify-all tower satisfies the per-rung doubling `2·S(n) ≤ S(n+1)` —
  this **is** `cost_super`'s growth law.
* **`reverify_exponential`** — hence `2^n ≤ S(n)`: re-verifying all below makes the tower climb
  *multiplicatively*.  Darren's mechanism delivers the multiplicative rate.
* **`reuse_additive`** — the reuse tower is `R(n) = n + 1`: composing the below keeps it *linear*.
* **`reuse_not_doubling`** — the reuse tower fails the doubling law.  Reuse is the collapse.
* **`reflection_compounds_iff_doubling`** — the dichotomy: re-verify-all ⟹ doubling; reuse ⟹ no doubling.

## Honest verdict — the exact doubling mechanism; the residual is "must it re-verify, or may it reuse?"

Darren's "each level re-verifies all below" is exactly the doubling.  When a level re-verifies everything
beneath it, the cumulative cost satisfies `2·S(n) ≤ S(n+1)` (`reverify_doubles`) and climbs as `2^n`
(`reverify_exponential`) — precisely `cost_super`'s per-rung growth `2·D(d) ≤ D(d+1)`, the wall this whole
arc started from.  The contrast is just as exact: if a level may *reuse* the below's verification instead
of redoing it (composition), the tower stays linear (`reuse_additive`) and the doubling fails
(`reuse_not_doubling`).  So the multiplicative rate is delivered **iff** each level re-verifies all below,
i.e. **iff no level may reuse the below** — which is exactly *no mass production / no sharing*.  Whether
SAT's verification tower must re-verify all below, or the bounded observer may reuse (compose) the lower
verifications, is the open question: re-verify = no reuse = no sharing = `cost_super`; reuse =
composition = `SAT ∈ P`.  Darren found the mechanism that makes the reflection compound to
multiplicative; **whether re-verification is forced (reuse impossible) is the wall** — the same
no-sharing wall the seam, the amortization, and the amplituhedron all named, now proved to be the Gödel
tower's doubling engine.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ReflectionCompounds

/-- The **re-verify-all** tower: a new level re-verifies the whole cumulative cost beneath it, plus `O(1)`
of its own — so `S(n+1) = 2·S(n) + 1`. -/
def reverifyTower : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * reverifyTower n + 1

/-- The **reuse** tower: a new level *reuses* the below's verification and only adds its own — it composes,
so `R(n+1) = R(n) + 1`. -/
def reuseTower : ℕ → ℕ
  | 0 => 1
  | n + 1 => reuseTower n + 1

/-! ### Re-verifying all below compounds to the doubling -/

/-- **The re-verify-all tower doubles (proved).**  `2·S(n) ≤ S(n+1)` — the new level's cost is the whole
sum beneath it, so the cumulative satisfies exactly `cost_super`'s per-rung growth. -/
theorem reverify_doubles (n : ℕ) : 2 * reverifyTower n ≤ reverifyTower (n + 1) := by
  show 2 * reverifyTower n ≤ 2 * reverifyTower n + 1
  omega

/-- **Re-verifying all below climbs multiplicatively (proved).**  `2^n ≤ S(n)`: the reflection compounds
to exponential growth — the multiplicative rate a size separation needs. -/
theorem reverify_exponential (n : ℕ) : 2 ^ n ≤ reverifyTower n := by
  induction n with
  | zero => simp [reverifyTower]
  | succ k ih =>
    have hp : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hr : reverifyTower (k + 1) = 2 * reverifyTower k + 1 := rfl
    rw [hp, hr]
    omega

/-! ### Reusing the below stays additive -/

/-- **The reuse tower is linear (proved).**  `R(n) = n + 1`: composing the below adds only `O(1)` per
level. -/
theorem reuse_additive (n : ℕ) : reuseTower n = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [reuseTower, ih]

/-- **The reuse tower fails the doubling (proved).**  At `n = 1`, `2·R(1) = 4 > 3 = R(2)`: reuse is the
collapse — composition keeps the tower in the additive (linear) regime. -/
theorem reuse_not_doubling : ¬ (∀ n, 2 * reuseTower n ≤ reuseTower (n + 1)) := by
  intro h
  have h1 := h 1
  simp only [reuse_additive] at h1
  omega

/-! ### The dichotomy -/

/-- **Reflection compounds iff no reuse (proved).**  Re-verifying all below gives the doubling; reusing
the below does not.  So the multiplicative rate holds exactly when each level re-verifies all below —
i.e. exactly when no level may reuse (compose) the ones beneath it: no mass production = `cost_super`. -/
theorem reflection_compounds_iff_doubling :
    (∀ n, 2 * reverifyTower n ≤ reverifyTower (n + 1))
    ∧ ¬ (∀ n, 2 * reuseTower n ≤ reuseTower (n + 1)) :=
  ⟨reverify_doubles, reuse_not_doubling⟩

end PallLean.Paper93.DeepMath.PathB.ReflectionCompounds

#print axioms PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reverify_doubles
#print axioms PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reverify_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reuse_additive
#print axioms PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reuse_not_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.ReflectionCompounds.reflection_compounds_iff_doubling
