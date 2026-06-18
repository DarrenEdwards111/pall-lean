import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AndGateApprox

/-!
# The `MOD_p` gate — exact native degree-`(p-1)` representation, and the native/non-native dichotomy

The single-gate polynomial method (entries 266–269) covered `AND`/`OR`.  The third `AC⁰[p]` gate is the **counting gate**
`MOD_p`, the `SYM` of the Beigel–Tarui `SYM∘AND` form.  This file proves its *exact* representation over its **own**
field `F_p` — degree `p-1`, independent of the number of inputs — via the Fermat indicator (entry 266), and frames the
native/non-native dichotomy that *is* the Razborov–Smolensky wall.

**The gate.**  `modpGate p x` fires iff the number of `true` inputs is `≡ 0 mod p`, i.e. iff `∑ᵢ xᵢ = 0` in `F_p`.

**Native representation (exact, degree `p-1`).**  By the Fermat indicator `y^{p-1} = [y ≠ 0]`,
`1 − (∑ᵢ xᵢ)^{p-1} = [∑ᵢ xᵢ = 0]` over `F_p` — an *exact* polynomial for `MOD_p`, of degree `p-1` **regardless of the
fan-in**.  So `MOD_p` is *easy* over `F_p`: constant native degree.

**The dichotomy (the wall).**  Over a *different* field `F_ℓ` (`ℓ ≠ p`), `MOD_p` has *high* non-native degree — it cannot
be approximated by low-degree `F_ℓ`-polynomials.  That non-native lower bound is the Razborov–Smolensky obstruction
(entry-264 `algExpander_forces_high_degree` is its dimension/rank mechanism); for *composite* modulus it is the open
`ACC⁰[composite]` wall (entry-238 `CarryRefinementCrossing`).

## What is proved (clean axioms, no `sorry`)

* **`linSum_eq_count`** (PROVED) — `∑ᵢ (if xᵢ then 1 else 0) = ↑#{i : xᵢ}` in `F_p` (`Finset.sum_boole`): the clause
  sum is the cast Hamming weight.
* **`modp_native_repr`** (PROVED) — `1 − (∑ᵢ xᵢ)^{p-1} = if modpGate p x then 1 else 0`: the exact degree-`(p-1)`
  native `F_p` representation of `MOD_p` (via `fermat_indicator`).
* **`modpGate_fires_iff`** (PROVED) — `modpGate p x ↔ p ∣ #{i : xᵢ}` (`ZMod.natCast_eq_zero_iff`): `MOD_p` is the
  divisibility of the Hamming weight — the `SYM`/cross-field-count object (entry 251).

## The non-native lower bound (named socket)

* **`ModpNonNativeHardOverOtherField`** — `MOD_p` requires high degree over `F_ℓ` (`ℓ ≠ p`): the Razborov–Smolensky
  obstruction.  Its mechanism is the proved `algExpander_forces_high_degree` (264); for composite modulus it is the open
  wall (238).

## Honest scope

This proves the exact *native* (`F_p`) representation of `MOD_p` — degree `p-1`, fan-in-free — and identifies `MOD_p`
with weight-divisibility (the `SYM`/cross-field object).  The native side is *easy* (constant degree); the *non-native*
lower bound (`MOD_p` over `F_ℓ`, `ℓ ≠ p`) is the Razborov–Smolensky wall, left as the named socket
`ModpNonNativeHardOverOtherField`.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

open Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModpGate

/-- **The clause sum** `∑ᵢ xᵢ ∈ F_p` (the Hamming weight cast into `F_p`). -/
def linSum (p : ℕ) {n : ℕ} (x : Fin n → Bool) : ZMod p :=
  ∑ i, (if x i then (1 : ZMod p) else 0)

/-- **The `MOD_p` gate** — fires iff the number of `true` inputs is `≡ 0 mod p`. -/
def modpGate (p : ℕ) {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide (linSum p x = 0)

/-- **The native `F_p` polynomial** `1 − (∑ᵢ xᵢ)^{p-1}` for `MOD_p` (degree `p-1`, fan-in-free). -/
def modpPoly (p : ℕ) {n : ℕ} (x : Fin n → Bool) : ZMod p :=
  1 - (linSum p x) ^ (p - 1)

/-- **The clause sum is the cast Hamming weight (PROVED).**  `∑ᵢ (if xᵢ then 1 else 0) = ↑#{i : xᵢ}` in `F_p`. -/
theorem linSum_eq_count {p n : ℕ} (x : Fin n → Bool) :
    linSum p x = ((Finset.univ.filter (fun i => x i = true)).card : ZMod p) := by
  unfold linSum
  rw [Finset.sum_boole]

/-- **The exact native representation of `MOD_p` (PROVED).**  `1 − (∑ᵢ xᵢ)^{p-1} = if modpGate p x then 1 else 0`
over `F_p`: an *exact* degree-`(p-1)` polynomial computing `MOD_p`, independent of the fan-in (via `fermat_indicator`). -/
theorem modp_native_repr {p : ℕ} [Fact p.Prime] {n : ℕ} (x : Fin n → Bool) :
    modpPoly p x = if modpGate p x then 1 else 0 := by
  unfold modpPoly modpGate
  rw [ACC0AndGateApprox.fermat_indicator]
  by_cases h : linSum p x = 0
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- **`MOD_p` is weight-divisibility (PROVED).**  `modpGate p x` fires iff `p ∣ #{i : xᵢ}` — i.e. `MOD_p` is the
`mod-p` count of firing inputs, the `SYM` gate / cross-field-count object (entry 251). -/
theorem modpGate_fires_iff {p n : ℕ} (x : Fin n → Bool) :
    modpGate p x = true ↔ p ∣ (Finset.univ.filter (fun i => x i = true)).card := by
  unfold modpGate
  rw [decide_eq_true_eq, linSum_eq_count, ZMod.natCast_eq_zero_iff]

/-- **The non-native lower bound (Razborov–Smolensky, NOT proved here).**  Over a field `F` of characteristic `ℓ ≠ p`,
`MOD_p` requires high degree — no low-degree `F`-polynomial approximates it.  The dimension/rank mechanism is the proved
`algExpander_forces_high_degree` (entry 264); for *composite* modulus this is the open `ACC⁰[composite]` wall
(entry-238 `CarryRefinementCrossing`). -/
def ModpNonNativeHardOverOtherField (HighNonNativeDegree : Prop) : Prop :=
  HighNonNativeDegree

/-!
**The dichotomy.**  `MOD_p` is *exactly* representable over `F_p` at degree `p-1`, fan-in-free
(`modp_native_repr`) — the native case is easy.  Over `F_ℓ` (`ℓ ≠ p`) it has high non-native degree — the
Razborov–Smolensky obstruction (`ModpNonNativeHardOverOtherField`), whose mechanism is the proved counting/rank engine
(`algExpander_forces_high_degree`, 264) and whose *composite-modulus* form is the open wall (238).  `MOD_p` is the
weight-divisibility / `SYM` gate (`modpGate_fires_iff`), the cross-field-count object of entry 251.  Not faked, not a
separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModpGate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpGate.linSum_eq_count
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpGate.modp_native_repr
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpGate.modpGate_fires_iff
