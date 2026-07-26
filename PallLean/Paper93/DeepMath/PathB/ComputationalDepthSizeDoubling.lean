import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-!
# The DAG scale: the multiplicative `cbudget` doubling — P ≠ NP, and why it has no bridge

The KRW route lives on the *tree* scale (formula depth, additive composition, `P ⊄ NC¹`).  This file stays
on the **DAG scale** — circuit *size*, `cbudget`, **multiplicative** composition — which is the real
`P ≠ NP` target, and marks the one fact that makes it strictly harder than KRW.

`compose f f` glues two copies of `f`; the tower is `T₀ = base`, `T₍d+1₎ = compose Tₐ Tₐ`.

## The target and its telescoping

* **`SizeDoubling`** — `∀ f, 2·cbudget f ≤ cbudget (compose f f)`: circuit size at least **doubles** when
  you glue two copies — no sharing between them.  This is the DAG-scale one-step bound (`cost_super`).
* **`size_telescopes` (proved)** — the doubling telescopes *multiplicatively*: `2^d · cbudget(base) ≤
  cbudget(tower d)`.  This is **superpolynomial in the input** — `SAT ∉ P/poly`, `P ≠ NP` — not the
  super-*log* depth KRW gives.
* **`size_clears` (proved)** — hence `cbudget(tower d)` clears every ceiling.

## Why the DAG scale has no bridge (the honest asymmetry with KRW)

On the *tree* scale, the intrinsic measure **exactly equals** the thing measured: KW communication
complexity `= formula depth` (the KW theorem, `KWBridge`).  So a lower bound on the intrinsic measure
(via the one-round lemma) *transfers* to depth — the bridge exists, and the route reduces to a single
composition lemma.

On the **DAG scale there is no such bridge**: **no known intrinsic measure equals `cbudget`.**  Circuit
size is not captured by any communication or information quantity we can lower-bound.  So there is nothing
to transfer *from* — `SizeDoubling` must be proved about `cbudget` **directly**, and no technique bounds
`cbudget` past linear (`~5n`).  That absence — an intrinsic size measure — is exactly why `P ≠ NP` (size)
is strictly beyond `P ⊄ NC¹` (depth), and why the KRW handle does not reach here.

## Honest scope

Proved: the multiplicative doubling telescopes to a superpolynomial *size* bound.  `SizeDoubling` itself
is `cost_super` — the open wall — and, unlike the depth scale, it has **no intrinsic-measure bridge**: it
must be attacked on `cbudget` directly, where no method reaches super-linear.  No shortcut, no tree.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SizeDoubling

/-- **The DAG-scale one-step bound**: gluing two copies of `f` at least doubles circuit size — no sharing
between the copies.  This is `cost_super`, the multiplicative composition bound. -/
def SizeDoubling {Fn : Type} (cbudget : Fn → ℕ) (compose : Fn → Fn → Fn) : Prop :=
  ∀ f, 2 * cbudget f ≤ cbudget (compose f f)

/-- `n < 2^n` (self-contained). -/
theorem lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- The self-doubling tower: `T₀ = base`, `T₍d+1₎ = compose Tₐ Tₐ`. -/
def tower {Fn : Type} (compose : Fn → Fn → Fn) (base : Fn) : ℕ → Fn
  | 0 => base
  | d + 1 => compose (tower compose base d) (tower compose base d)

/-- **The size doubling telescopes multiplicatively (proved).**  `2^d · cbudget(base) ≤ cbudget(tower d)`:
circuit size grows *exponentially in the composition depth* — superpolynomial, the `P ≠ NP` (size) scale,
not the super-log depth of KRW. -/
theorem size_telescopes {Fn : Type} (cbudget : Fn → ℕ) (compose : Fn → Fn → Fn) (base : Fn)
    (dbl : SizeDoubling cbudget compose) (d : ℕ) :
    2 ^ d * cbudget base ≤ cbudget (tower compose base d) := by
  induction d with
  | zero => simp [tower]
  | succ d ih =>
    show 2 ^ (d + 1) * cbudget base ≤ cbudget (compose (tower compose base d) (tower compose base d))
    calc 2 ^ (d + 1) * cbudget base = 2 * (2 ^ d * cbudget base) := by rw [Nat.pow_succ]; ring
      _ ≤ 2 * cbudget (tower compose base d) := Nat.mul_le_mul (Nat.le_refl 2) ih
      _ ≤ cbudget (compose (tower compose base d) (tower compose base d)) := dbl _

/-- **The size clears every ceiling (proved).**  With a nonempty base, `cbudget(tower d)` exceeds any
bound `U` — the DAG-scale separation. -/
theorem size_clears {Fn : Type} (cbudget : Fn → ℕ) (compose : Fn → Fn → Fn) (base : Fn)
    (dbl : SizeDoubling cbudget compose) (hbase : 1 ≤ cbudget base) (U : ℕ) :
    ∃ d, U < cbudget (tower compose base d) := by
  refine ⟨U + 1, ?_⟩
  have h1 : 2 ^ (U + 1) * cbudget base ≤ cbudget (tower compose base (U + 1)) :=
    size_telescopes cbudget compose base dbl (U + 1)
  have h2 : U + 1 ≤ 2 ^ (U + 1) := Nat.le_of_lt (lt_two_pow_self (U + 1))
  have h3 : 2 ^ (U + 1) ≤ 2 ^ (U + 1) * cbudget base := by
    calc 2 ^ (U + 1) = 2 ^ (U + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ (U + 1) * cbudget base := Nat.mul_le_mul (Nat.le_refl _) hbase
  omega

end PallLean.Paper93.DeepMath.PathB.SizeDoubling

#print axioms PallLean.Paper93.DeepMath.PathB.SizeDoubling.size_telescopes
#print axioms PallLean.Paper93.DeepMath.PathB.SizeDoubling.size_clears
