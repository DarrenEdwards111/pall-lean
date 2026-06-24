import Mathlib

/-!
# Kleene interpreter project — the measure-monotone config rank (PROVED)

The course-of-values table (`buildTable`) is filled by rank `0,1,2,…`; for the fill to be correct, the rank
must order configurations so that every **sub-configuration ranks strictly lower** (it is computed before its
parents).  The `evaln` dependency is on the measure `(fuel, encode code)` lexicographically (the input is
free), so within the value bounds (`encode c ≤ E`, `n ≤ B` from `config_encode_le`) the flattened rank

  `cfgRank E B k ec n = (k·(E+1) + ec)·(B+1) + n`

is measure-monotone:

  `cfgRank_lt_code` — same fuel, smaller code (`comp`/`pair` subcodes): `ec' < ec ≤ E`, `n' ≤ B` ⇒ lower rank.
  `cfgRank_lt_fuel` — lower fuel (`prec`/`rfind'`): `k' < k`, `ec' ≤ E`, `n' ≤ B` ⇒ lower rank.

So indexing the table by `cfgRank` makes `buildTable` respect the `evalnStep` dependency: the per-cell body
reads every sub-result from an already-filled, strictly-lower cell (via `lookupCode`).

## What is proved (clean axioms, no `sorry`)

* `cfgRank`, `cfgRank_lt_code`, `cfgRank_lt_fuel`.

## Honest scope

The rank + monotonicity (table-indexing foundation).  Decoding rank → `(k, c, n)`, the per-cell body
(`mkDispatch` + `lookupCode` at sub-ranks), the correctness chain, the interpreter, and the runtime remain.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneRank

/-- Measure-monotone rank of a configuration within the value bounds `ec ≤ E`, `n ≤ B`. -/
def cfgRank (E B k ec n : ℕ) : ℕ := (k * (E + 1) + ec) * (B + 1) + n

/-- **Same fuel, smaller code ⇒ strictly lower rank (proved).** -/
theorem cfgRank_lt_code (E B k ec ec' n n' : ℕ) (hec : ec' < ec) (hecE : ec ≤ E) (hn' : n' ≤ B) :
    cfgRank E B k ec' n' < cfgRank E B k ec n := by
  unfold cfgRank; nlinarith [Nat.zero_le n, Nat.zero_le (k * (E + 1))]

/-- **Lower fuel ⇒ strictly lower rank (proved).** -/
theorem cfgRank_lt_fuel (E B k k' ec ec' n n' : ℕ) (hk : k' < k) (hecE : ec' ≤ E) (hn' : n' ≤ B) :
    cfgRank E B k' ec' n' < cfgRank E B k ec n := by
  have hk1 : (k' + 1) * (E + 1) ≤ k * (E + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hk)
  have hmain : k' * (E + 1) + ec' < k * (E + 1) + ec := by nlinarith [hk1, hecE]
  unfold cfgRank
  nlinarith [hmain, hn', Nat.zero_le n, Nat.mul_le_mul_right (B + 1) (Nat.succ_le_of_lt hmain)]

/-!
**Rank monotonicity proved.**  Indexing `buildTable` by `cfgRank` makes the course-of-values fill respect
the `evalnStep` dependency (sub-configs strictly lower).  Decoding, the per-cell body, correctness, the
interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneRank

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneRank.cfgRank_lt_code
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneRank.cfgRank_lt_fuel
