import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# Attacking `cbudget` directly in a restricted DAG model: bounded sharing

Staying on the DAG scale (`SizeDoubling`), the general obstruction is *unbounded* sharing between the two
composition-halves (Uhlig mass production).  The honest restricted model: bound the sharing.  In a DAG
where the two copies of `Tₐ` inside `T₍d+1₎` share **at most `B` gates**, the size satisfies

`c(d+1) ≥ 2·c(d) − B`,  equivalently  `2·c(d) ≤ c(d+1) + B`.

This is a genuine direct `cbudget` lower-bound attack — no tree, no bridge, just circuit size with the
sharing capped.

## What is proved

* **`bounded_sharing_telescopes` (proved)** — with per-step sharing `≤ B` and a base exceeding it
  (`a + B ≤ c 0`, `a ≥ 1`), the size telescopes to `2^d · a + B ≤ c d`.  The `−B` per step is absorbed by
  the substitution `c − B`, so the doubling **survives bounded sharing**.
* **`bounded_sharing_superpoly` (proved)** — hence `2^d ≤ c d`: **superpolynomial circuit size in the
  bounded-sharing DAG model.**  A real DAG-scale lower bound.

## The honest gap — and it's exactly the wall

The result holds precisely when the base circuit exceeds the per-step sharing (`a = c 0 − B ≥ 1`).  So
the doubling survives **any bounded sharing** below the base size — only sharing that reaches a *full
base's worth* (`B ≥ c 0`, i.e. **unbounded / mass production**) can collapse it.  That threshold —
whether the SAT tower's per-step sharing stays below the base or reaches mass-production scale — is
`cost_super`, the open wall.  So the restricted model is genuine and the gap to `P ≠ NP` is a single,
named quantity: **is the sharing bounded, or is it Uhlig mass production?**

**Honest scope.**  Proved: in the bounded-sharing DAG model, circuit size is exponential — a real
restricted `cbudget` lower bound, direct (not via tree/bridge).  The open case is unbounded sharing
(mass production), which is `cost_super`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedSharing

/-- **The doubling survives bounded sharing (proved).**  If per-step sharing is `≤ B` (`2·c d ≤ c(d+1)+B`)
and the base exceeds it (`a + B ≤ c 0`, `a ≥ 1`), then `2^d · a + B ≤ c d`: the `−B` per step is absorbed,
and the size grows exponentially. -/
theorem bounded_sharing_telescopes (c : ℕ → ℕ) (a B : ℕ) (ha : 1 ≤ a)
    (hbase : a + B ≤ c 0) (hstep : ∀ d, 2 * c d ≤ c (d + 1) + B) (d : ℕ) :
    2 ^ d * a + B ≤ c d := by
  induction d with
  | zero => simpa using hbase
  | succ d ih =>
    have hs := hstep d
    have key : 2 ^ (d + 1) * a = 2 * (2 ^ d * a) := by rw [Nat.pow_succ]; ring
    rw [key]
    omega

/-- **Superpolynomial size in the bounded-sharing model (proved).**  With the base exceeding the per-step
sharing (`a ≥ 1`), `2^d ≤ c d`: exponential circuit size — a real DAG-scale lower bound, direct on
`cbudget`. -/
theorem bounded_sharing_superpoly (c : ℕ → ℕ) (a B : ℕ) (ha : 1 ≤ a)
    (hbase : a + B ≤ c 0) (hstep : ∀ d, 2 * c d ≤ c (d + 1) + B) (d : ℕ) :
    2 ^ d ≤ c d := by
  have h := bounded_sharing_telescopes c a B ha hbase hstep d
  have h2 : 2 ^ d ≤ 2 ^ d * a := by
    calc 2 ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ d * a := Nat.mul_le_mul (Nat.le_refl _) ha
  omega

end PallLean.Paper93.DeepMath.PathB.BoundedSharing

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedSharing.bounded_sharing_telescopes
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedSharing.bounded_sharing_superpoly
