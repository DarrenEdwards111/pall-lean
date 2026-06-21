import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimeMODLowDegree

/-!
# Brick A.2b — squarefree composite-`MOD_m` as a product of degree-`(p-1)` `F_p` polynomials (proved)

Assembling Brick A.1 (CRT residue decomposition) and Brick A.2 (single prime-`MOD` Fermat representation): for a
**squarefree** modulus `m` (every prime factor to the first power — e.g. `MOD₆`, `MOD₃₀`, `MOD₁₀₅`), the `MOD_m` gate is
*exactly* the conjunction, over the prime factors `p` of `m`, of the degree-`(p-1)` conditions `(∑ᵢ [xᵢ])^{p-1} = 0` over
`F_p`.  This is a fully low-degree `SYM`-product representation of an entire family of composite-`MOD` gates — the regime
where the single-field method was proven dead (A.1) but the product observer + Fermat succeed.

## What is proved (clean axioms, no `sorry`)

* **`squarefree_dvd_primeFactors`** (PROVED) — `m ≠ 0 → Squarefree m → (m ∣ k ↔ ∀ p ∈ m.primeFactors, p ∣ k)`.
* **`modm_squarefree_fermat`** (PROVED) — `m ≠ 0 → Squarefree m → (modm m x ↔ ∀ p ∈ m.primeFactors, (∑ i, if x i then
  (1:ZMod p) else 0)^{p-1} = 0)` — the squarefree composite gate as a product of degree-`(p-1)` `F_p` polynomials.

## Honest scope

This is the **squarefree** composite case, fully assembled.  It does **not** cover prime-power factors `e ≥ 2` (Toda
lifting), a formal `MvPolynomial` degree-membership, the quasipoly `SYM∘AND` packaging, nor degree-additive depth
composition — i.e. general YBT / `composite_BT_degree` remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SquarefreeMOD

open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (hammingWeight)
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFactor (modm dvd_iff_primePow_residues)
open PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODLowDegree (modp_iff_fermat)

/-- **Squarefree divisibility factors through the prime factors (PROVED).** -/
theorem squarefree_dvd_primeFactors {m : ℕ} (hm : m ≠ 0) (hsq : Squarefree m) (k : ℕ) :
    m ∣ k ↔ ∀ p ∈ m.primeFactors, p ∣ k := by
  rw [dvd_iff_primePow_residues hm]
  refine forall_congr' (fun p => imp_congr_right (fun hp => ?_))
  have hfac : m.factorization p = 1 := by
    have hle := (Nat.squarefree_iff_factorization_le_one hm).mp hsq p
    have hge : 1 ≤ m.factorization p := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp; omega
    omega
  rw [hfac, pow_one]

/-- **Squarefree composite-`MOD_m` as a product of degree-`(p-1)` `F_p` polynomials (PROVED).** -/
theorem modm_squarefree_fermat {m n : ℕ} (hm : m ≠ 0) (hsq : Squarefree m) (x : Fin n → Bool) :
    modm m x ↔ ∀ p ∈ m.primeFactors, (∑ i, (if x i then (1 : ZMod p) else 0)) ^ (p - 1) = 0 := by
  show m ∣ hammingWeight x ↔ _
  rw [squarefree_dvd_primeFactors hm hsq]
  refine forall_congr' (fun p => imp_congr_right (fun hp => ?_))
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hp'⟩
  haveI : NeZero p := ⟨hp'.pos.ne'⟩
  exact (ZMod.natCast_eq_zero_iff (hammingWeight x) p).symm.trans (modp_iff_fermat p x)

/-!
**The squarefree composite representation, proved.**  Squarefree `MOD_m` is exactly a product of degree-`(p-1)` `F_p`
indicators — A.1 (CRT) ∘ A.2 (Fermat), an entire family of composite-`MOD` gates made low-degree.  Next: prime-power
`e≥2` Toda lifting, then degree-additive depth composition — the remaining content of general YBT.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0SquarefreeMOD

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SquarefreeMOD.modm_squarefree_fermat
