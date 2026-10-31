import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqFourier

/-!
# Hard math (prime-power Toda lifting) — `MOD_{p^e}` via the root-of-unity representation (proved)

The genuine prime-power rung of the Toda/Beigel–Tarui `MOD` representation.  As `ACC0PrimePowerMOD` documents honestly, the
prime case's *Fermat* `F_p` low-degree polynomial does **not** lift to `MOD_{p^e}` for `e ≥ 2` (RS barrier) — the Beigel–Tarui
method uses a *different* representation.  That representation is the **discrete-Fourier / root-of-unity** one, which lifts
seamlessly to any modulus: over a field `F_ℓ` containing a primitive `(p^e)`-th root of unity `ζ` (a prime `ℓ ≡ 1 mod p^e`,
`ℓ ≠ p`), the `MOD_{p^e}` indicator is the character sum

  `bv(MOD_{p^e} x) = (p^e)⁻¹ · ∑_{j < p^e} charWt(ζʲ) x`   (`primePowerMod_charSum`),

instantiating the proved `modq_fourier` at `q = p^e`.  This is the Toda integer/root-of-unity representation of the
prime-power `MOD` gate — what the prime-power case genuinely needs, in contrast to the non-existent low-degree `F_p` form.

## What is proved (clean axioms, no `sorry`)

* **`primePowerMod_charSum`** (PROVED) — the root-of-unity character-sum representation of `MOD_{p^e}` over `F_ℓ`.
* **`mod4_charSum`** (PROVED) — the concrete instance `MOD_4 = MOD_{2²}` over `F_5` with `ζ = 2` (`orderOf 2 = 4` in `F_5`).

## Honest scope

This is the *exact root-of-unity (Toda integer) representation* of `MOD_{p^e}` — the lift the prime-power case needs, where
the Fermat `F_p` polynomial fails.  It is an exact representation over a field with the right root of unity; the
low-monomial-count (`SYM∘AND` size) consequence for *composition* is the separate Beigel–Tarui count argument
(`compositeBT_representation`).  Unconditional `NEXP ⊄ ACC⁰` is P≠NP-strength.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerToda

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness (modqFn)
open PallLean.Paper93.DeepMath.PathB.ACC0CharWitness (charWt)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqFourier (modq_fourier)

/-- **The prime-power `MOD_{p^e}` root-of-unity (Toda integer) representation (PROVED).**  Over a field `F_ℓ` with a
primitive `(p^e)`-th root of unity `ζ`, `MOD_{p^e}` is the character sum `(p^e)⁻¹ ∑_{j<p^e} charWt(ζʲ)` — the representation
that lifts the prime case to prime powers (where the Fermat `F_p` polynomial fails). -/
theorem primePowerMod_charSum {n : ℕ} (ℓ : ℕ) [Fact ℓ.Prime] (p e : ℕ)
    (hq : ((p ^ e : ℕ) : ZMod ℓ) ≠ 0) (ζ : ZMod ℓ) (hord : orderOf ζ = p ^ e) (x : Fin n → Bool) :
    (bv (modqFn (p ^ e) x) : ZMod ℓ)
      = ((p ^ e : ℕ) : ZMod ℓ)⁻¹ * ∑ j ∈ Finset.range (p ^ e), charWt (ζ ^ j) x :=
  modq_fourier (p ^ e) hq ζ hord x

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- **Concrete instance: `MOD_4 = MOD_{2²}` over `F_5` with `ζ = 2` (PROVED).**  `2` is a primitive 4th root of unity in
`F_5` (`orderOf 2 = 4`), so `MOD_4` has the root-of-unity representation over `F_5`. -/
theorem mod4_charSum {n : ℕ} (x : Fin n → Bool) :
    (bv (modqFn 4 x) : ZMod 5)
      = ((4 : ℕ) : ZMod 5)⁻¹ * ∑ j ∈ Finset.range 4, charWt ((2 : ZMod 5) ^ j) x := by
  have hord : orderOf (2 : ZMod 5) = 2 ^ 2 := orderOf_eq_prime_pow (by decide) (by decide)
  have := primePowerMod_charSum (n := n) 5 2 2 (by decide) (2 : ZMod 5) hord x
  simpa using this

/-!
**Prime-power Toda lifting, proved.**  `MOD_{p^e}` has the exact root-of-unity (Toda integer) representation over a field with
a primitive `(p^e)`-th root — the lift the prime-power case needs, where the Fermat `F_p` polynomial fails (`e ≥ 2`).
Remaining (open, not faked): the `SYM∘AND` count consequence for composition (Beigel–Tarui) and the unconditional
`NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerToda

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerToda.primePowerMod_charSum
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerToda.mod4_charSum
