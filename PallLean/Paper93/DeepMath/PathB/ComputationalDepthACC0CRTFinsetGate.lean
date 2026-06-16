import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CRTGatePolys

/-!
# CRT over a `Finset` of primes — arbitrary squarefree composite `MOD` gate

Iterating the two-prime CRT composition (`…ACC0CRTGatePolys.modPQGate_decides`) to an arbitrary `Finset` of distinct
primes: for `S` a finset of primes, the family of prime gate polynomials `{modPGate p}_{p∈S}` all fire iff
`(∏_{p∈S} p) ∣ s` — i.e. they decide `MOD_m` for any squarefree modulus `m = ∏ S`.

## What is proved (clean axioms, no `sorry`)

* **`prod_primes_dvd_iff`** — `(∏ p ∈ S, p) ∣ s ↔ ∀ p ∈ S, p ∣ s` for a finset `S` of primes (distinct primes are
  coprime, so the product divides iff each prime does; `Finset.prod_primes_dvd` + `dvd_prod_of_mem`).
* **`modGateProd_decides`** — the squarefree composite `MOD` gate: `(∀ p ∈ S, modPGate p fires at s mod p) ↔
  (∏ p ∈ S, p) ∣ s`.  The whole family of exact low-degree prime gate polynomials decides `MOD_{∏S}`.

## Honest scope

The squarefree composite modulus case is now complete: any `m` that is a product of distinct primes has a family of
exact, low-degree (`p−1`) local gate polynomials over the product-residue observer `∏ F_p`, deciding `MOD_m`.  Remaining
for fully arbitrary `m = ∏ pᵢ^{eᵢ}`: the prime-*power* components `p^e` (`ZMod p^e` is not a field, so the Fermat
indicator does not apply), and the `AND`-layer + feeding into `compositeBT_representation`.  This builds the
squarefree-composite gate; it does not assemble a full circuit representation.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CRTFinsetGate

open scoped BigOperators
open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys (modPGate modPGate_decides_dvd)

/-- **CRT divisibility over a finset of primes (proved): `(∏ p ∈ S, p) ∣ s ↔ ∀ p ∈ S, p ∣ s`.** -/
theorem prod_primes_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (s : ℕ) :
    (∏ p ∈ S, p) ∣ s ↔ ∀ p ∈ S, p ∣ s := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun i => i) hp) h
  · intro h
    exact Finset.prod_primes_dvd s (fun p hp => (hS p hp).prime) h

/-- **The squarefree composite `MOD` gate (proved): the prime gate family decides `MOD_{∏S}`.**  For a finset `S` of
primes, all the gate polynomials `modPGate p` fire (at `s mod p`) iff `(∏ p ∈ S, p) ∣ s`. -/
theorem modGateProd_decides (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (s : ℕ) :
    (∀ p ∈ S, eval (fun _ => (s : ZMod p)) (modPGate p) = 1) ↔ (∏ p ∈ S, p) ∣ s := by
  rw [prod_primes_dvd_iff S hS s]
  refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · haveI : Fact p.Prime := ⟨hS p hp⟩
    exact (modPGate_decides_dvd p s).mp (h p hp)
  · haveI : Fact p.Prime := ⟨hS p hp⟩
    exact (modPGate_decides_dvd p s).mpr (h p hp)

end PallLean.Paper93.DeepMath.PathB.ACC0CRTFinsetGate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTFinsetGate.prod_primes_dvd_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTFinsetGate.modGateProd_decides
