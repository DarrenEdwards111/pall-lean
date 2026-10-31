import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# The dynamic rank through a restriction sequence — the shrinkage engine, and its exact reach

Darren's dynamic `Π★`: the rank **evolves through a restriction sequence** `ρ₁, ρ₂, …`.  That is the
**shrinkage** mechanism: applying a restriction shrinks the circuit's rank by a factor `s`, while the hard
function *retains* its rank; the gap accumulates over the sequence.

Let `crank d` be the circuit's rank after `d` restrictions.  Shrinkage per step:

`s · crank (d+1) ≤ crank d`  — restricting drops the rank by a factor `≥ s`.

## What is proved

* **`dynamic_telescopes` (proved)** — the shrinkage telescopes: `s^d · crank d ≤ crank 0`.  Over `d`
  restrictions the *original* rank is at least `s^d` times the restricted rank.
* **`dynamic_bound` (proved)** — the dynamic lower bound: if after `k` restrictions the (hard) function
  still needs rank `H` (`H ≤ crank k`), then `s^k · H ≤ crank 0` — the full circuit's rank is at least
  `s^k · H`.  The restriction sequence *amplifies* the retained hardness by `s^k`.

## The reach — and where the depth chasm bites

The bound is `s^k · H`: shrinkage factor `s`, number of restrictions `k`, retained hard rank `H`.  Whether
it reaches superpolynomial is exactly whether `s` (the per-restriction shrinkage) is large enough over the
`k` steps.

* For **formulas**, `s` is governed by the shrinkage exponent `Γ` (`s ≈ p^{-Γ}`, `Γ ≤ 2` — Subbotovskaya
  `3/2`, Håstad `2`), which caps the reach at `n^{5/2}`–`n³` (`ShrinkageExponentRung`).
* For **SPDP** under restrictions, `s` is the *SPDP shrinkage rate*.  The question — does SPDP shrink fast
  enough, over a restriction sequence, to amplify `H` to superpoly at **general depth** — is exactly the
  open depth-chasm problem.  If `s^k` reaches superpoly there, `dynamic_bound` cashes it out to a general
  lower bound; that `s^k` is `cost_super` in SPDP-shrinkage language.

**Honest scope.**  Proved: the dynamic restriction-sequence bound `s^k · H ≤ crank 0` — the shrinkage
engine, exactly.  It cashes out *any* per-restriction shrinkage rate `s` to a bound.  The reach is `s^k`,
capped at `n³` for formula shrinkage; whether a *dynamic SPDP* shrinkage rate breaks the depth chasm to
superpoly is the open wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DynamicRestriction

/-- **The shrinkage telescopes (proved).**  With per-restriction shrinkage `s · crank (d+1) ≤ crank d`,
after `d` restrictions `s^d · crank d ≤ crank 0`: the original rank is at least `s^d` times the restricted
rank. -/
theorem dynamic_telescopes (crank : ℕ → ℕ) (s : ℕ)
    (shrink : ∀ d, s * crank (d + 1) ≤ crank d) (d : ℕ) :
    s ^ d * crank d ≤ crank 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc s ^ (d + 1) * crank (d + 1)
        = s ^ d * (s * crank (d + 1)) := by rw [Nat.pow_succ]; ring
      _ ≤ s ^ d * crank d := Nat.mul_le_mul (Nat.le_refl _) (shrink d)
      _ ≤ crank 0 := ih

/-- **The dynamic lower bound (proved).**  If after `k` restrictions the hard function still needs rank
`H` (`H ≤ crank k`), then `s^k · H ≤ crank 0`: the restriction sequence amplifies the retained hardness by
`s^k`.  Cash out any per-restriction shrinkage rate `s` to a circuit lower bound. -/
theorem dynamic_bound (crank : ℕ → ℕ) (s : ℕ)
    (shrink : ∀ d, s * crank (d + 1) ≤ crank d) (k H : ℕ) (hHard : H ≤ crank k) :
    s ^ k * H ≤ crank 0 := by
  calc s ^ k * H ≤ s ^ k * crank k := Nat.mul_le_mul (Nat.le_refl _) hHard
    _ ≤ crank 0 := dynamic_telescopes crank s shrink k

end PallLean.Paper93.DeepMath.PathB.DynamicRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.DynamicRestriction.dynamic_telescopes
#print axioms PallLean.Paper93.DeepMath.PathB.DynamicRestriction.dynamic_bound
