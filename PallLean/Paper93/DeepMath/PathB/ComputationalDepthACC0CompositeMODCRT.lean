import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeMODFactor

/-!
# Hard math (composite `MOD_m` CRT assembly) — squarefree `MOD_m` = AND of prime `MOD_p` (proved)

The CRT assembly reducing composite `MOD_m` to the prime gates whose low-degree representation (Toda/Fermat) and `SYM∘AND`
composition count are already established.  For **squarefree** `m`, each prime factor has multiplicity `1`, so the
prime-power residue decomposition (`modm_iff_residues`) collapses to the prime residues:

  `MOD_m(x) ↔ ∀ p ∈ m.primeFactors, (weight x : ZMod p) = 0`   (`modm_squarefree_and`),

i.e. the composite `MOD_m` gate is exactly the **conjunction of the prime `MOD_p` gates**.  Since each `MOD_p` is the
degree-`(p−1)` Fermat gate with a quasipolynomial `SYM∘AND` count (`modp_endToEnd`), and `AND` is a binary Boolean gate
(degree `2`), the composite count assembles: a squarefree-`MOD_m` circuit is a circuit over the prime `MOD_p` gates combined
by `AND`, hence quasipolynomial `SYM∘AND` count.

## What is proved (clean axioms, no `sorry`)

* **`squarefree_factorization_eq_one`** (PROVED) — for squarefree `m`, `m.factorization p = 1` on prime factors.
* **`modm_squarefree_and`** (PROVED) — `MOD_m(x) ↔ ∀ p ∈ m.primeFactors, (weight x : ZMod p) = 0` (the CRT gate decomposition).

## Honest scope

This is the CRT reduction of squarefree composite `MOD_m` to prime `MOD_p` gates — the assembly that lets the per-prime
low-degree / quasipoly-count results cover composite (squarefree) moduli.  Prime-power multiplicity `e ≥ 2` (genuinely
higher, via the root-of-unity `primePowerMod_charSum`) and the unconditional `NEXP ⊄ ACC⁰` (P≠NP-strength) are **not** done
here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODCRT

open PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFactor (modm modm_iff_residues)

/-- **For squarefree `m`, every prime factor has multiplicity `1` (PROVED).** -/
theorem squarefree_factorization_eq_one {m : ℕ} (hm0 : m ≠ 0) (hsf : Squarefree m)
    {p : ℕ} (hp : p ∈ m.primeFactors) : m.factorization p = 1 := by
  have h1 : m.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hm0).mp hsf p
  rw [Nat.mem_primeFactors] at hp
  have h2 : 1 ≤ m.factorization p := Nat.Prime.factorization_pos_of_dvd hp.1 hp.2.2 hp.2.1
  omega

/-- **CRT gate decomposition (PROVED): a squarefree composite `MOD_m` gate is the conjunction of the prime `MOD_p` gates.**
`MOD_m(x) ↔ ∀ p ∈ m.primeFactors, (weight x : ZMod p) = 0`. -/
theorem modm_squarefree_and {m n : ℕ} (hm0 : m ≠ 0) (hsf : Squarefree m) (x : Fin n → Bool) :
    modm m x ↔ ∀ p ∈ m.primeFactors,
      (PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT.hammingWeight x : ZMod p) = 0 := by
  rw [modm_iff_residues hm0]
  refine forall₂_congr (fun p hp => ?_)
  rw [squarefree_factorization_eq_one hm0 hsf hp, pow_one]

/-!
**Composite `MOD_m` CRT assembly, proved.**  Squarefree `MOD_m` decomposes into the conjunction of prime `MOD_p` gates — the
reduction that carries the per-prime Toda/Fermat low-degree representation and quasipolynomial `SYM∘AND` count to composite
(squarefree) moduli.  Remaining (open, not faked): prime-power multiplicity `e ≥ 2` and the unconditional `NEXP ⊄ ACC⁰`.  Not
`NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODCRT

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODCRT.modm_squarefree_and
