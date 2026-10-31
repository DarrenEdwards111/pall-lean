import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqFourier

/-!
# Hard math (composite `MOD_m`, prime-power multiplicity) — root-of-unity representation for any `m` (proved)

The prime-power multiplicity case for *composite* moduli.  The squarefree CRT assembly (`modm_squarefree_and`) reduced
squarefree `MOD_m` to prime gates, but a composite `m = ∏ p_i^{a_i}` with `a_i ≥ 2` needs the prime-power factors directly.
The discrete-Fourier / root-of-unity representation handles this with **no dependence on the factorization**: over a field
`F_ℓ` containing a primitive `m`-th root of unity `ζ` (a prime `ℓ ≡ 1 mod m`, `ℓ ∤ m`),

  `bv(MOD_m x) = m⁻¹ · ∑_{j < m} charWt(ζʲ) x`   (`modm_charSum`),

instantiating the proved `modq_fourier` at `q = m` — for *any* `m`, including prime-power-multiplicity composites.  The
concrete instance `mod12_charSum` (`m = 12 = 2²·3`, multiplicity `2` on the prime `2`) is over `F_13` with `ζ = 2` (a
primitive 12-th root).

## What is proved (clean axioms, no `sorry`)

* **`modm_charSum`** (PROVED) — the root-of-unity representation of `MOD_m` over `F_ℓ`, for *any* `m`.
* **`mod12_charSum`** (PROVED) — concrete `MOD_{12}` (= `MOD_{2²·3}`) over `F_13`, `ζ = 2`.

## Honest scope

This is the exact root-of-unity representation of composite `MOD_m` (any factorization, any prime-power multiplicity) over a
field with a primitive `m`-th root.  The low-`SYM∘AND`-count consequence for composition is the Beigel–Tarui count argument
(established for `MOD_p`-circuits); the unconditional `NEXP ⊄ ACC⁰` is P≠NP-strength.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeMultiplicity

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn)
open PallLean.Paper93.DeepMath.PathB.ACC0CharWitness (charWt)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqFourier (modq_fourier)

/-- **The composite `MOD_m` root-of-unity representation, for any `m` (PROVED).**  Over a field `F_ℓ` with a primitive
`m`-th root of unity `ζ` (`ℓ` prime, `m ∣ ℓ−1`, `ℓ ∤ m`), `MOD_m` is the character sum `m⁻¹ ∑_{j<m} charWt(ζʲ)` — for any
`m`, regardless of prime-power multiplicities. -/
theorem modm_charSum {n : ℕ} (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ)
    (hq : ((m : ℕ) : ZMod ℓ) ≠ 0) (ζ : ZMod ℓ) (hord : orderOf ζ = m) (x : Fin n → Bool) :
    (bv (modqFn m x) : ZMod ℓ) = ((m : ℕ) : ZMod ℓ)⁻¹ * ∑ j ∈ Finset.range m, charWt (ζ ^ j) x :=
  modq_fourier m hq ζ hord x

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Concrete prime-power-multiplicity composite: `MOD_{12} = MOD_{2²·3}` over `F_13` with `ζ = 2` (PROVED).**  `2` is a
primitive 12-th root of unity in `F_13`, so `MOD_{12}` has the root-of-unity representation over `F_13`. -/
theorem mod12_charSum {n : ℕ} (x : Fin n → Bool) :
    (bv (modqFn 12 x) : ZMod 13)
      = ((12 : ℕ) : ZMod 13)⁻¹ * ∑ j ∈ Finset.range 12, charWt ((2 : ZMod 13) ^ j) x := by
  have hord : orderOf (2 : ZMod 13) = 12 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
    intro q hq hdvd
    have hle : q ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ≤ q := hq.two_le
    interval_cases q <;> revert hdvd <;> decide
  have := modm_charSum (n := n) 13 12 (by decide) (2 : ZMod 13) hord x
  simpa using this

/-!
**Composite `MOD_m`, prime-power multiplicity, proved.**  Any `MOD_m` (any factorization, any multiplicity) has the exact
root-of-unity representation over a field with a primitive `m`-th root — covering the prime-power-multiplicity composite case
seamlessly.  Remaining (open, not faked): the `SYM∘AND` count for composition and the unconditional `NEXP ⊄ ACC⁰`.  Not
`NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeMultiplicity

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMultiplicity.modm_charSum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMultiplicity.mod12_charSum
