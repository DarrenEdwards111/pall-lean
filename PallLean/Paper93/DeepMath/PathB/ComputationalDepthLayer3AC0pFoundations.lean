import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Parity
import Mathlib.Data.ZMod.Basic

/-!
# Layer 3 — AC⁰[p] / Razborov–Smolensky: first foundation brick

The first harmless foundations for the polynomial-method (Razborov–Smolensky) attack on AC⁰[p] lower
bounds (see `SCOPE_LAYER3_AC0p.md`).  **Definitions + one tiny `ZMod p` fact only — no lower bound, no
capstone, no assumption.**

The AC⁰[p] *circuit model* already exists (`BoolCircuitSyntax` with `modGate` + `IsAC0pSyntax`,
`ComputationalDepthRung4CircuitReal.lean`); this file does **not** redefine it.  It pins:

* `boolToZMod p : Bool → ZMod p` — the `{0,1}` embedding the polynomial representation lives over, with
  its idempotence `x² = x` (the algebraic fact that makes `{0,1}` the natural domain).
* `modCountFn q r` — the `MOD_q` target function (`#true ≡ r mod q`), generalising the existing
  `parity`; `parity = modCountFn 2 1` ties it to the already-proven Layer-2 parity API.

Layer 3 is a higher circuit-lower-bound layer (AC⁰[p], strictly above AC⁰), **far below P vs NP**; this
file claims nothing beyond the two definitions and the idempotence/parity facts.  Clean, no `sorry`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open PallLean.Paper93.DeepMath.PathB.Depth3.DTree

variable {n : ℕ}

/-- Embed a Boolean into `ZMod p`: `false ↦ 0`, `true ↦ 1`.  The image `{0,1}` is the domain over which
the Razborov–Smolensky polynomial representation operates. -/
def boolToZMod (p : ℕ) (b : Bool) : ZMod p := if b then 1 else 0

@[simp] theorem boolToZMod_false (p : ℕ) : boolToZMod p false = 0 := rfl

@[simp] theorem boolToZMod_true (p : ℕ) : boolToZMod p true = 1 := rfl

/-- The embedding lands in `{0,1}`. -/
theorem boolToZMod_mem (p : ℕ) (b : Bool) : boolToZMod p b = 0 ∨ boolToZMod p b = 1 := by
  cases b <;> simp

/-- **Idempotence on `{0,1}`:** `(boolToZMod p b)² = boolToZMod p b`.  This is the algebraic identity
that makes `{0,1} ⊆ ZMod p` the right input domain for the polynomial method (it lets multilinearisation
be lossless on Boolean inputs). -/
theorem boolToZMod_sq (p : ℕ) (b : Bool) : (boolToZMod p b) ^ 2 = boolToZMod p b := by
  cases b <;> simp

/-- The `MOD_q` target function: is the Hamming weight `≡ r (mod q)`?  Generalises `parity` (the case
`q = 2, r = 1`).  This is the family Razborov–Smolensky separates from `AC⁰[p]` for primes `q ≠ p`. -/
def modCountFn (q r : ℕ) (x : Fin n → Bool) : Bool := decide (trueCount x % q = r)

/-- Parity is the `MOD₂` (`r = 1`) instance — ties the new target to the proven `parity`/`trueCount`
API.  (Reminder: parity is *easy* for `AC⁰[2]`; the genuine Layer-3 target is `MOD_q`, `q ≠ p`.) -/
theorem parity_eq_modCountFn (x : Fin n → Bool) : parity x = modCountFn 2 1 x := by
  simp [parity, modCountFn, Nat.odd_iff]

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.boolToZMod_sq
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.parity_eq_modCountFn
