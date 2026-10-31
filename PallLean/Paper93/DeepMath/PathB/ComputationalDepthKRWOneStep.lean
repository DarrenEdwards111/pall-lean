import Mathlib.Data.Nat.Basic

/-!
# The KRW one-step bound as a socket — the god's-eye measure surviving one composition step

The lens thread proved counting can't work (`ReusePairTrap`): the measure must be **intrinsic** —
representation-independent, a god's-eye view of the function.  The canonical intrinsic measure is **KW
communication complexity** (`= formula depth`), and the honest frontier is whether it **survives one
composition step**.  That is the **KRW one-round lemma**.  This file names it as a socket and telescopes
it to the separation.

* `kw : Fn → ℕ` — the intrinsic measure (KW complexity / formula depth), representation-independent.
* `compose` — function composition; `tower` iterates it, `T₀ = base`, `T₍d+1₎ = compose Tₐ base`.

## The socket

* **`KWOneStep`** — `∀ f g, kw f + kw g ≤ kw (compose f g)`: KW is (super)additive under composition.
  This is the **KRW one-round lemma** — the god's-eye measure surviving a single step.  It is the open
  wall (repo KRW arc, `KRW1`–`KRW19`; "one-round lemma = the wall").

## What is proved

* **`krw_telescopes`** — the one-step socket telescopes: `(d+1)·kw(base) ≤ kw(tower d)`.  The intrinsic
  measure grows linearly in the composition depth.
* **`krw_depth_lower_bound`** — cash-out: with the KW theorem (`kw ≤ formula depth`, standard) and a
  non-trivial base, `depth(tower d) ≥ d+1`.  For `d = ω(log n)` this is **super-logarithmic depth** —
  `P ⊄ NC¹`.

## Honest scope

The `KWOneStep` socket is **unproven** — it is the KRW one-round lemma, the open composition step.
Telescoping and cash-out are proved; the file is a conditional, `KWOneStep ⟹ P ⊄ NC¹` (given the KW
theorem).  **Ceiling is `P ⊄ NC¹`** (formula *depth*), which is *weaker* than `P ≠ NP` (circuit *size*):
KRW's additive depth gives super-log; the size version needs a *multiplicative* (doubling) composition
bound, harder still.  But this is the real intrinsic-measure frontier — not a counting shortcut.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KRWOneStep

/-- The **KRW one-step socket** (one-round lemma): the intrinsic measure `kw` is superadditive under
composition.  The god's-eye measure surviving a single composition step. -/
def KWOneStep {Fn : Type} (kw : Fn → ℕ) (compose : Fn → Fn → Fn) : Prop :=
  ∀ f g, kw f + kw g ≤ kw (compose f g)

/-- The self-composition tower: `T₀ = base`, `T₍d+1₎ = compose Tₐ base`. -/
def tower {Fn : Type} (compose : Fn → Fn → Fn) (base : Fn) : ℕ → Fn
  | 0 => base
  | d + 1 => compose (tower compose base d) base

/-- **The one-step bound telescopes (proved).**  `KWOneStep` gives `(d+1)·kw(base) ≤ kw(tower d)`: the
intrinsic measure grows linearly in the composition depth. -/
theorem krw_telescopes {Fn : Type} {kw : Fn → ℕ} {compose : Fn → Fn → Fn} (base : Fn)
    (step : KWOneStep kw compose) (d : ℕ) : (d + 1) * kw base ≤ kw (tower compose base d) := by
  induction d with
  | zero =>
    show 1 * kw base ≤ kw base
    simp
  | succ d ih =>
    show (d + 1 + 1) * kw base ≤ kw (compose (tower compose base d) base)
    calc (d + 1 + 1) * kw base = (d + 1) * kw base + kw base := by rw [Nat.succ_mul]
      _ ≤ kw (tower compose base d) + kw base := Nat.add_le_add_right ih _
      _ ≤ kw (compose (tower compose base d) base) := step _ _

/-- **Cash-out to a formula-depth lower bound (proved).**  With the KW theorem (`kw ≤ depth`) and a
non-trivial base (`1 ≤ kw base`), the tower's formula depth is `≥ d+1`.  For `d = ω(log n)` this is
super-logarithmic depth — `P ⊄ NC¹`.  Discharging `KWOneStep` (given the KW theorem) proves it. -/
theorem krw_depth_lower_bound {Fn : Type} {kw depth : Fn → ℕ} {compose : Fn → Fn → Fn} (base : Fn)
    (step : KWOneStep kw compose) (kw_le : ∀ f, kw f ≤ depth f) (hbase : 1 ≤ kw base) (d : ℕ) :
    d + 1 ≤ depth (tower compose base d) := by
  have h1 := krw_telescopes base step d
  have h2 : d + 1 ≤ (d + 1) * kw base := by
    calc d + 1 = (d + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (d + 1) * kw base := Nat.mul_le_mul (Nat.le_refl _) hbase
  exact le_trans h2 (le_trans h1 (kw_le _))

end PallLean.Paper93.DeepMath.PathB.KRWOneStep

#print axioms PallLean.Paper93.DeepMath.PathB.KRWOneStep.krw_telescopes
#print axioms PallLean.Paper93.DeepMath.PathB.KRWOneStep.krw_depth_lower_bound
