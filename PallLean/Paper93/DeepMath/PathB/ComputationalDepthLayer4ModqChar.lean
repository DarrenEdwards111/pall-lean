import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Layer 4 (foundation) — the `q`-ary weight character

This is the first, deliberately *harmless* brick toward the general `MOD_q ∉ AC⁰[p]` lower bound
(`SCOPE_LAYER4_MODq_GENERALIZATION.md`).  It is the exact `q`-ary generalisation of Layer 3's
`χ_univ = ∏ᵢ pmOne(xᵢ) = (-1)^{#ones}`:

Given a ring element `ζ` (intended to be a primitive `q`-th root of unity in `F_{p^k}`), the **weight
character** encodes a Boolean input by `ζ` raised to its Hamming weight:
\[
  \texttt{weightChar}\,\zeta\,x \;=\; \prod_i \bigl(1 + (\zeta-1)\cdot x_i\bigr) \;=\; \zeta^{\,\#\{i : x_i\}}.
\]
When `ζ^q = 1` this depends only on the weight **mod `q`** (`weightChar_eq_pow_mod`) — the property that
makes `MOD_q` the relevant hard function.  Specialising `ζ = -1` recovers the Layer-3 parity sign.

Everything here is ring-general and field-independent; no finite-field, root-of-unity, or unproved
content.  The genuinely new mathematics (the extension field `F_{p^k}`, the existence of `ζ`, and above
all the `q`-ary degree-reduction replacing the parity `y²=1` involution) is deferred — see §3 of the
scope document; **it must not be faked.**
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset

/-- The **`q`-ary weight character**: each Boolean coordinate `xᵢ` contributes `ζ^{xᵢ}` (i.e. `ζ` if
`xᵢ`, else `1`), encoded as the degree-1 factor `1 + (ζ-1)·xᵢ`. -/
def weightChar {R : Type*} [CommRing R] (ζ : R) {n : ℕ} (x : Fin n → Bool) : R :=
  ∏ i, (1 + (ζ - 1) * (if x i then 1 else 0))

/-- Each factor is `ζ` on a true coordinate and `1` on a false one. -/
theorem weightChar_factor {R : Type*} [CommRing R] (ζ : R) (b : Bool) :
    (1 + (ζ - 1) * (if b then (1 : R) else 0)) = if b then ζ else 1 := by
  cases b
  · show (1 : R) + (ζ - 1) * 0 = 1; ring
  · show (1 : R) + (ζ - 1) * 1 = ζ; ring

/-- **The weight character is `ζ` to the Hamming weight:** `weightChar ζ x = ζ^{#ones}`.  This is the
`q`-ary generalisation of `prod_pmOne` (`∏ pmOne(xᵢ) = (-1)^{#ones}`). -/
theorem weightChar_eq_pow {R : Type*} [CommRing R] (ζ : R) {n : ℕ} (x : Fin n → Bool) :
    weightChar ζ x = ζ ^ (Finset.univ.filter (fun i => x i = true)).card := by
  rw [weightChar]
  simp only [weightChar_factor]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

/-- **Weight is read mod `q`** when `ζ` is a `q`-th root of unity: `weightChar ζ x = ζ^{#ones mod q}`.
This is what makes the character detect `MOD_q` — its value depends only on the Hamming weight modulo
`q`. -/
theorem weightChar_eq_pow_mod {R : Type*} [CommRing R] {ζ : R} {q : ℕ} (hζ : ζ ^ q = 1)
    {n : ℕ} (x : Fin n → Bool) :
    weightChar ζ x = ζ ^ ((Finset.univ.filter (fun i => x i = true)).card % q) := by
  rw [weightChar_eq_pow]
  conv_lhs => rw [← Nat.div_add_mod (Finset.univ.filter (fun i => x i = true)).card q]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

/-- **Parity specialisation.**  With `ζ = -1` (the 2nd root of unity, in `ZMod p` for every `p`) the
weight character is the Layer-3 parity sign `(-1)^{#ones}` — confirming Layer 4 generalises Layer 3. -/
theorem weightChar_neg_one {p n : ℕ} (x : Fin n → Bool) :
    weightChar (-1 : ZMod p) x = (-1 : ZMod p) ^ (Finset.univ.filter (fun i => x i = true)).card :=
  weightChar_eq_pow (-1) x

/-- **The `MOD_q` indicator.**  For a primitive `q`-th root of unity `ζ`, the weight character equals `1`
exactly when the Hamming weight is divisible by `q`:
`weightChar ζ x = 1 ↔ q ∣ #ones`.  This connects the character (`ComputationalDepthLayer4ModqChar`) to the
literal `MOD_q` predicate — the hard function of Layer 4 (brick (C2) of the §3-C decision note). -/
theorem weightChar_eq_one_iff {R : Type*} [CommRing R] {ζ : R} {q : ℕ} (hζ : IsPrimitiveRoot ζ q)
    {n : ℕ} (x : Fin n → Bool) :
    weightChar ζ x = 1 ↔ q ∣ (Finset.univ.filter (fun i => x i = true)).card := by
  rw [weightChar_eq_pow]; exact hζ.pow_eq_one_iff_dvd _

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.weightChar_eq_pow
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.weightChar_eq_pow_mod
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.weightChar_neg_one
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.weightChar_eq_one_iff
