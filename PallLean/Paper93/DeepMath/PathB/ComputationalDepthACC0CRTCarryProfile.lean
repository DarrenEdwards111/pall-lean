import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0KummerCarry

/-!
# The CRT carry profile — per-prime Kummer carries assembled into a composite-modulus observer (conservative)

Entry 236 (`…ACC0KummerCarry`) gave the per-prime carry count `carryCount p n k = padicValNat p (C(n+k,k))`.  For a
*composite* modulus `m = ∏ pᵢ^{eᵢ}`, the natural N-Frame object is the **carry profile**: the tuple of per-prime carry
counts over the prime factors of `m`.  This file assembles that profile and proves *safe fragment theorems*
characterising it, again **conservatively**: no global "obstructs exactification" claim.

⚠️ **Scope discipline.**  These characterise the composite-modulus carry profile (when the mod-`m` observer sees the
full count vs. when a prime layer is invisible) and its CRT/multiplicative structure.  They do **not** cross the
composite-`ACC⁰[m]` barrier (entry 234); none is a separation result.

## The object

`CarryProfileTrivial m n k := ∀ p ∈ m.primeFactors, carryCount p n k = 0` — the composite-modulus carry profile is
*trivial* (no carries at any prime layer of `m`).  This is the joint per-prime Kummer data of entry 236, read across the
prime factorisation of `m`.

## What is proved (clean axioms, no `sorry`)

* **`carryProfileTrivial_iff_no_prime_dvd`** (PROVED) — `CarryProfileTrivial m n k ↔ ∀ p ∈ m.primeFactors, ¬ p ∣
  C(n+k,k)`: the profile is trivial iff *no prime layer of `m`* divides the binomial (per-prime, via entry-236
  `carryCount_eq_zero_iff_not_dvd`).
* **`carryProfileTrivial_iff_coprime`** (PROVED) — `CarryProfileTrivial m n k ↔ Nat.Coprime m (C(n+k,k))` (for `m ≠ 0`):
  the composite-modulus observer sees the full count (trivial profile) iff `m` is coprime to the binomial.  Via
  `Nat.disjoint_primeFactors` (coprimality ⟺ disjoint prime factors).
* **`carryProfile_mul`** (PROVED) — the **CRT decomposition**: for coprime-or-not factors `a, b ≠ 0`,
  `CarryProfileTrivial (a·b) n k ↔ CarryProfileTrivial a n k ∧ CarryProfileTrivial b n k` (via `Nat.primeFactors_mul`):
  the composite carry profile is the *join* of the per-factor profiles — the profile factors through the modulus exactly
  as the CRT residue observer (entry-235 `crt_residue_observer_suffices`) factors `ZMod (a·b) ≃ ZMod a × ZMod b`.

## Honest scope

These conservative fragments assemble the per-prime Kummer carry counts into a **composite-modulus observer profile**
and prove its characterisations: trivial ⟺ no prime layer divides the binomial ⟺ `m` coprime to it
(`carryProfileTrivial_iff_no_prime_dvd` / `_iff_coprime`), and the profile decomposes multiplicatively over the
factorisation (`carryProfile_mul`), matching the CRT residue split.  This **characterises** the composite-modulus carry
seam — *which* prime layers the mod-`m` observer is blind to — and exhibits the CRT structure of the profile.  It does
**not** cross the composite-`ACC⁰[m]` barrier (entry 234): nothing here forces exactification for composite `m`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Nat

namespace PallLean.Paper93.DeepMath.PathB.ACC0CRTCarryProfile

open PallLean.Paper93.DeepMath.PathB.ACC0KummerCarry (carryCount carryCount_eq_zero_iff_not_dvd)

/-- **The composite-modulus carry profile is trivial.**  No base-`p` carry occurs at *any* prime layer `p` of `m`:
`∀ p ∈ m.primeFactors, carryCount p n k = 0`.  The joint per-prime Kummer data (entry 236) across `m`'s factorisation. -/
def CarryProfileTrivial (m n k : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, carryCount p n k = 0

/-- **Trivial profile ⟺ no prime layer divides the binomial (PROVED).**  `CarryProfileTrivial m n k ↔ ∀ p ∈
m.primeFactors, ¬ p ∣ C(n+k,k)` — by the entry-236 field-observer link `carryCount_eq_zero_iff_not_dvd` applied at each
prime factor (`Fact p.Prime` from `Nat.mem_primeFactors`). -/
theorem carryProfileTrivial_iff_no_prime_dvd (m n k : ℕ) :
    CarryProfileTrivial m n k ↔ ∀ p ∈ m.primeFactors, ¬ p ∣ Nat.choose (n + k) k := by
  unfold CarryProfileTrivial
  constructor <;> intro h p hp <;>
    · have hpp := (Nat.mem_primeFactors.mp hp).1
      haveI : Fact p.Prime := ⟨hpp⟩
      first
        | exact (carryCount_eq_zero_iff_not_dvd p n k).mp (h p hp)
        | exact (carryCount_eq_zero_iff_not_dvd p n k).mpr (h p hp)

/-- **Trivial profile ⟺ `m` coprime to the binomial (PROVED).**  For `m ≠ 0`, `CarryProfileTrivial m n k ↔
Nat.Coprime m (C(n+k,k))`: the composite-modulus observer sees the full count (no carry layer) iff `m` is coprime to the
binomial.  Via `Nat.disjoint_primeFactors` (coprimality ⟺ disjoint prime-factor sets) and
`carryProfileTrivial_iff_no_prime_dvd`. -/
theorem carryProfileTrivial_iff_coprime (m n k : ℕ) (hm : m ≠ 0) :
    CarryProfileTrivial m n k ↔ Nat.Coprime m (Nat.choose (n + k) k) := by
  have hc : Nat.choose (n + k) k ≠ 0 := (Nat.choose_pos (Nat.le_add_left k n)).ne'
  rw [carryProfileTrivial_iff_no_prime_dvd, ← Nat.disjoint_primeFactors hm hc,
    Finset.disjoint_left]
  constructor
  · intro h p hp hpc
    exact h p hp ((Nat.mem_primeFactors.mp hpc).2.1)
  · intro h p hp hpc
    exact h hp (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1, hpc, hc⟩)

/-- **CRT decomposition of the carry profile (PROVED).**  For factors `a, b ≠ 0`, `CarryProfileTrivial (a·b) n k ↔
CarryProfileTrivial a n k ∧ CarryProfileTrivial b n k` — the composite carry profile is the *join* of the per-factor
profiles (`Nat.primeFactors_mul`).  This is the carry profile factoring through the modulus exactly as the CRT residue
observer (entry-235 `crt_residue_observer_suffices`) splits `ZMod (a·b) ≃+* ZMod a × ZMod b`. -/
theorem carryProfile_mul (a b n k : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    CarryProfileTrivial (a * b) n k ↔ CarryProfileTrivial a n k ∧ CarryProfileTrivial b n k := by
  unfold CarryProfileTrivial
  rw [Nat.primeFactors_mul ha hb]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Finset.mem_union_left _ hp),
      fun p hp => h p (Finset.mem_union_right _ hp)⟩
  · rintro ⟨h1, h2⟩ p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact h1 p hp
    · exact h2 p hp

end PallLean.Paper93.DeepMath.PathB.ACC0CRTCarryProfile

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTCarryProfile.carryProfileTrivial_iff_no_prime_dvd
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTCarryProfile.carryProfileTrivial_iff_coprime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTCarryProfile.carryProfile_mul
