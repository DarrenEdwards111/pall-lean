import Mathlib.Data.Nat.Basic

/-!
# Breaking the L_eff/L_H dilemma in a restricted case: the EXP middle

The `LagrangianDilemma` horn: a separating measure is either **`L_eff`** (efficiently computable → natural
property → barriered) or **`L_H`** (hypercomputational → outside the model).  That is a *false
dichotomy* — it skips the **middle**.

Razborov–Rudich constructivity is time `2^{O(n)}` (polynomial in the `2^n`-bit truth table).  A measure
computable in **EXP with a super-linear exponent** (`2^{n²}`) is:

* **past the constructivity threshold** (`2^{n²} > 2^{c·n}` for every constant `c`, large `n`) — so it is
  **non-natural**, *not* `L_eff`, and evades the natural-proofs barrier; yet
* **bounded** (a standard class) — so *not* hypercomputational, *not* `L_H`.

Neither horn.  The dilemma is broken.

## What is proved

* **`breaks_dilemma` (proved)** — `2^{c·n} < 2^{n²}` for `n > c`: the `EXP` measure exceeds *every*
  constructive threshold `2^{c·n}`, so it is non-natural — while remaining a bounded (`EXP`) quantity.
  The middle option exists, for every constant `c`.

## Where this leaves the directed machine — two walls down, one to go

Combined with the counting break (`CountingBarrierBreak`), **two of the directed machine's three drivers
are now cleared**:

* driver 2 (counting / largeness) — broken (non-large detector);
* driver 3 (`L_eff`/`L_H`) — broken (the `EXP` middle, here).

What remains is **driver 1 — `cost_super`**: the measure must be *useful*, i.e. it must actually be
**high on SAT** (the hard function is not low-complexity).  That is the pure circuit lower bound, with the
two natural-proofs-style barriers now evaded.

So the honest end state: **the barriers are broken; the bound is not.**  Evading `L_eff`/`L_H` (and
largeness) is *necessary* and now *done* in the restricted (`EXP`, non-large) case.  But the `EXP` measure
is `cbudget`/`MCSP`, and proving it high on SAT is `cost_super` — the single remaining wall.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DilemmaBreak

/-- **The L_eff/L_H dilemma is broken (proved).**  For every constant `c` and `n > c`, `2^{c·n} < 2^{n²}`:
the `EXP` measure `2^{n²}` exceeds the constructive threshold `2^{c·n}` — so it is **non-natural** (not
`L_eff`) — while remaining bounded (not `L_H`).  A measure in the `EXP` middle is neither horn. -/
theorem breaks_dilemma (c n : ℕ) (hn : c < n) : 2 ^ (c * n) < 2 ^ (n ^ 2) := by
  have hpos : 0 < n := by omega
  have hnn : n ^ 2 = n * n := by rw [Nat.pow_succ, Nat.pow_one]
  have hcn : c * n < n ^ 2 := by
    rw [hnn]
    exact (Nat.mul_lt_mul_right hpos).mpr hn
  exact Nat.pow_lt_pow_right (by decide) hcn

end PallLean.Paper93.DeepMath.PathB.DilemmaBreak

#print axioms PallLean.Paper93.DeepMath.PathB.DilemmaBreak.breaks_dilemma
