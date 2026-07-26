import Mathlib.Data.Nat.Basic

/-!
# Holography is batching — but which direction? Compression defeats the bound; the *limit* is the bound

Darren's identification is exact: the holographic principle **is** batching — the bulk (`2^d`
information) encoded in a compressed boundary.  This file pins the *direction*, honestly.

There are two holographic statements, and they point opposite ways:

* **Compression** — the bulk squeezes into a small boundary (`dagCost` stays bounded).  This is batching
  *winning*.
* **Incompressibility** — the Bekenstein bound: the boundary area *caps* the bulk information, so it
  *cannot* be squeezed below `2^d`.  This is batching *failing* — a hard limit on compression.

For `P ≠ NP` you need the **second**.  The first defeats the lower bound.

## What is proved

* **`compression_no_separation` (proved)** — if holographic batching compresses `dagCost` to a fixed
  boundary `B`, the DAG never clears a ceiling above `B`: cost stays small, `cost_super` fails, the tower
  does **not** separate.  **Compression winning is the wrong direction.**
* **`incompressible_separates` (proved)** — the opposite: if `dagCost` is *incompressible* (`≥ 2^d`), it
  clears every ceiling — the separation.  The lower bound is the **Bekenstein limit on batching**, not
  batching itself.

## The honest catch

So holography, followed correctly, lands back on the same wall — from the incompressibility side.  The
statement that proves `P ≠ NP` is "the bulk **cannot** be batched below `2^d`" (incompressibility) — and
that is a **counting** argument (entropy ≤ area), which in complexity is exactly a natural property:
**barriered by Razborov–Rudich** (`HolographicIncompressibility`, commit `75fa26dd`, machine-checks that
an efficient incompressibility detector breaks cryptography).

An *asymmetric* holographic gauge — compress the easy part, prove the hard part incompressible — is the
God-Move `Π★`, which by `DischargePiStar` / `GodMoveFace` must be **non-natural** (the far shore).

**Honest scope.**  Proved: compression defeats the bound, incompressibility is the bound.  Holography is
a faithful *description* of the wall from both sides — compression (no bound) and Bekenstein
incompressibility (the bound, but barriered).  It does not supply the incompressibility proof, and
nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolographicDirection

/-- `n < 2^n` (self-contained). -/
theorem lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- **Holographic compression**: the DAG cost stays bounded by a fixed boundary "area" `B`, however deep
the tower — the bulk `2^d` batched into a small boundary.  This is batching *winning*. -/
def Compresses (dagCost : ℕ → ℕ) (B : ℕ) : Prop := ∀ d, dagCost d ≤ B

/-- **Incompressibility** (the Bekenstein side): the DAG cost cannot be squeezed below `2^d`.  This is
batching *failing* — the hard limit that a lower bound needs. -/
def Incompressible (dagCost : ℕ → ℕ) : Prop := ∀ d, 2 ^ d ≤ dagCost d

/-- **Compression is the wrong direction (proved).**  If holographic batching compresses `dagCost` to a
fixed boundary `B`, the DAG never clears a ceiling above `B`: the cost stays small, `cost_super` fails,
and the tower does **not** separate.  Batching winning defeats the lower bound. -/
theorem compression_no_separation (dagCost : ℕ → ℕ) (B : ℕ) (hcomp : Compresses dagCost B) :
    ¬ ∀ U, ∃ d, U < dagCost d := by
  intro hclear
  obtain ⟨d, hd⟩ := hclear B
  exact absurd (hcomp d) (Nat.not_le.mpr hd)

/-- **Incompressibility is the separation (proved).**  If `dagCost` is incompressible (`≥ 2^d`), it
clears every ceiling — the DAG superpoly bound, i.e. the separation.  The lower bound is the Bekenstein
*limit* on batching, not batching itself. -/
theorem incompressible_separates (dagCost : ℕ → ℕ) (hinc : Incompressible dagCost) (U : ℕ) :
    ∃ d, U < dagCost d :=
  ⟨U + 1, lt_of_lt_of_le
      (lt_of_lt_of_le (Nat.lt_succ_self U) (Nat.le_of_lt (lt_two_pow_self (U + 1))))
      (hinc (U + 1))⟩

end PallLean.Paper93.DeepMath.PathB.HolographicDirection

#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDirection.compression_no_separation
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicDirection.incompressible_separates
