import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukCeiling

/-!
# Above `n²/log n` — the Andreev / Håstad shrinkage route (structure, honestly scaffolded)

`…NeciporukCeiling` proved subfunction counting caps at `n²/log n`.  The classical way *above* that ceiling is a
**different method**: Håstad's shrinkage (formula leaf count shrinks by `p^Γ`, `Γ = 2`) applied to **Andreev's
function**, giving formula size `n^{3-o(1)}`.  This file formalizes the *logical structure* of that known route
and proves it strictly exceeds the Nečiporuk ceiling.

**This proves nothing new and nothing open.**  Andreev's `n^{3-o(1)}` bound is a proven theorem (Håstad 1998); its
two deep ingredients are *named cited lemmas*, not re-proved here and not conjectures:

* **Shrinkage (Håstad, `Γ = 2`)** — a good `p`‑restriction shrinks the leaf count by a factor `≥ D ≈ p^{-2}`:
  `leafRestricted · D ≤ leafFull`.  (The deep random‑restriction analysis; cited, not proved here.)
* **Andreev hardness** — after a restriction keeping a variable per block, the function still computes an
  arbitrary `k`‑bit table lookup, needing `≥ H` leaves: `H ≤ leafRestricted`.  (Cited.)

## What is proved (clean axioms, no `sorry`)

* `andreev_leaf_lower_bound` — **the combination**: from shrinkage (`leafRestricted · D ≤ leafFull`) and hardness
  (`H ≤ leafRestricted`), the full formula has `H · D ≤ leafFull`.  Pure arithmetic, no fractions.
* `cube_lt_two_pow` — `k³ < 2^k` for `k ≥ 10` (exp beats cubic).
* `shrinkage_above_neciporuk` — **the payoff**: at balanced Andreev parameters (`H = 2^k`, `D = 2^{2k}`, so the
  shrinkage bound is `H·D = 2^{3k}`), the bound strictly exceeds the Nečiporuk‑ceiling scale
  `k³ · 2^{2k} ≈ n²/log n`: `k³ · 2^{2k} < 2^{3k}`.

## How the scales line up (balanced Andreev: `n = k·m + 2^k`, `m = k·2^k`)

`2^k ≈ n/k²`, `m ≈ n/k`, `log n ≈ k`.  The shrinkage leaf bound `H·D = 2^k·(m/k)² = 2^k·2^{2k} = 2^{3k} ≈
(n/k²)³ = n³/k⁶ = n^{3-o(1)}`.  The Nečiporuk ceiling is `n²/log n ≈ k³·2^{2k}`.  Their ratio is `2^k/k³ → ∞`
(`cube_lt_two_pow`), so the shrinkage route is **`n^{3-o(1)}`, genuinely above `n²/log n`** — by a *different*
method (random restrictions + shrinkage), exactly as the Nečiporuk ceiling note predicted.

## Honest scope

A *characterization of the known route*, not a contribution: the combination arithmetic and the
above‑`n²/log n` comparison are proved; the two deep lemmas (Håstad shrinkage, Andreev hardness) are named cited
theorems, fenced.  It records, formally, that there *is* an explicit method above the Nečiporuk ceiling — and
that it is `n^{3-o(1)}`, still vastly short of any `P ≠ NP`‑relevant (super‑polynomial) bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.AndreevShrinkageRoute

/-- **The shrinkage + hardness combination (proved).**  If a good restriction shrinks the leaf count by a factor
`D` (`leafRestricted · D ≤ leafFull`, the Håstad shrinkage bound) and the restricted function still needs `H`
leaves (`H ≤ leafRestricted`, Andreev hardness), then the full formula has `H · D ≤ leafFull`. -/
theorem andreev_leaf_lower_bound {leafFull leafRestricted D H : ℕ}
    (shrinkage : leafRestricted * D ≤ leafFull) (hard : H ≤ leafRestricted) :
    H * D ≤ leafFull :=
  le_trans (Nat.mul_le_mul hard (le_refl D)) shrinkage

/-- `k³ < 2^k` for `k ≥ 10` (exponential beats cubic). -/
theorem cube_lt_two_pow : ∀ k : ℕ, 10 ≤ k → k ^ 3 < 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have a1 : 10 * k ≤ k * k := Nat.mul_le_mul hk (le_refl k)
    have a2 : 10 * (k * k) ≤ k * (k * k) := Nat.mul_le_mul hk (le_refl (k * k))
    have hstep : (k + 1) ^ 3 ≤ 2 * k ^ 3 := by nlinarith [hk, a1, a2]
    calc (k + 1) ^ 3 ≤ 2 * k ^ 3 := hstep
      _ < 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- **The payoff (proved): the shrinkage route exceeds the Nečiporuk ceiling.**  At balanced Andreev parameters the
shrinkage leaf bound is `2^{3k}`, strictly above the Nečiporuk‑ceiling scale `k³ · 2^{2k} ≈ n²/log n` (for
`k ≥ 10`).  So `n^{3-o(1)}` genuinely beats `n²/log n` — by a different method. -/
theorem shrinkage_above_neciporuk (k : ℕ) (hk : 10 ≤ k) :
    k ^ 3 * 2 ^ (2 * k) < 2 ^ (3 * k) := by
  have hc := cube_lt_two_pow k hk
  have hpos : 0 < 2 ^ (2 * k) := pow_pos (by norm_num) _
  calc k ^ 3 * 2 ^ (2 * k)
      < 2 ^ k * 2 ^ (2 * k) := Nat.mul_lt_mul_of_pos_right hc hpos
    _ = 2 ^ (3 * k) := by rw [← pow_add]; congr 1; ring

/-- **The balanced shrinkage bound is exactly `2^{3k}` (proved): `H · D = 2^k · 2^{2k} = 2^{3k}`.**  Combined with
`andreev_leaf_lower_bound`, a formula for balanced Andreev has `≥ 2^{3k}` leaves; with `shrinkage_above_neciporuk`
that is `> k³·2^{2k} ≈ n²/log n`. -/
theorem balanced_HD_eq (k : ℕ) : 2 ^ k * 2 ^ (2 * k) = 2 ^ (3 * k) := by
  rw [← pow_add]; congr 1; ring

end PallLean.Paper93.DeepMath.PathB.AndreevShrinkageRoute

#print axioms PallLean.Paper93.DeepMath.PathB.AndreevShrinkageRoute.andreev_leaf_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.AndreevShrinkageRoute.cube_lt_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.AndreevShrinkageRoute.shrinkage_above_neciporuk
