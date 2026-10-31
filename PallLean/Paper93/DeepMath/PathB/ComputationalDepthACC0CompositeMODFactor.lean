import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTTarget

/-!
# Brick A.1 — general composite-`MOD_m` CRT residue decomposition (proved)

The Beigel–Tarui route to a composite-`MOD_m` `ACC⁰` gate goes through the integer/multi-prime (CRT) observer, not a single
prime field (the single-field method provably fails — `no_injective_ringHom_zmod6_to_prime_field`, `CompositeBTTarget`).  The
tree discharged the smallest case `MOD₆ ↔ (mod 2) ∧ (mod 3)`.  This file generalises that to **arbitrary** modulus `m`: the
`MOD_m` gate equals the conjunction, over the prime-power factors `p^{e_p}` of `m`, of the residue conditions `weight ≡ 0
(mod p^{e_p})` — read by the product observer `ZMod m ≃ ∏ ZMod (p^{e_p})`.

This is the **CRT-reduction half** of Brick A (single composite gate): it reduces a composite-`MOD` gate to a conjunction of
prime-power-`MOD` gates.  The remaining half — the *polylog-degree* representation of each prime-power gate (Toda/RS
symmetrization) and its quasipolynomial `SYM∘AND` packaging — is named below as the open sub-brick, **not** discharged here.

## What is proved (clean axioms, no `sorry`)

* **`modm m x`** — the general `MOD_m` gate (`m ∣ hammingWeight x`).
* **`dvd_iff_primePow_residues`** (PROVED) — `m ≠ 0 → (m ∣ k ↔ ∀ p ∈ m.primeFactors, p^{m.factorization p} ∣ k)`.
* **`modm_iff_residues`** (PROVED) — `m ≠ 0 → (modm m x ↔ ∀ p ∈ m.primeFactors, (hammingWeight x : ZMod (p^{m.factorization
  p})) = 0)` — the general CRT residue decomposition.

## Honest scope

This is the **CRT reduction** (composite → prime powers), fully general.  It does **not** prove the per-prime-power
polylog-degree representation (Toda/RS), the quasipoly `SYM∘AND` packaging, nor general YBT / `composite_BT_degree` — those
remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFactor

open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (hammingWeight)

/-- **The general `MOD_m` gate:** the Hamming weight is divisible by `m`. -/
def modm (m : ℕ) {n : ℕ} (x : Fin n → Bool) : Prop := m ∣ hammingWeight x

/-- **Divisibility by `m` factors through its maximal prime powers (PROVED).** -/
theorem dvd_iff_primePow_residues {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    m ∣ k ↔ ∀ p ∈ m.primeFactors, p ^ m.factorization p ∣ k := by
  constructor
  · intro hmk p _
    exact dvd_trans (Nat.ordProj_dvd m p) hmk
  · intro h
    rcases eq_or_ne k 0 with hk | hk
    · simp [hk]
    · rw [← Nat.factorization_le_iff_dvd hm hk, Finsupp.le_def]
      intro p
      rcases Nat.eq_zero_or_pos (m.factorization p) with h0 | hpos
      · simp [h0]
      · have hpmem : p ∈ m.primeFactors := by
          rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
        have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
        exact (Nat.Prime.pow_dvd_iff_le_factorization hp hk).mp (h p hpmem)

/-- **General CRT residue decomposition of `MOD_m` (PROVED).** -/
theorem modm_iff_residues {m n : ℕ} (hm : m ≠ 0) (x : Fin n → Bool) :
    modm m x ↔ ∀ p ∈ m.primeFactors, (hammingWeight x : ZMod (p ^ m.factorization p)) = 0 := by
  show m ∣ hammingWeight x ↔ _
  rw [dvd_iff_primePow_residues hm]
  refine forall_congr' (fun p => imp_congr_right (fun hp => ?_))
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : NeZero (p ^ m.factorization p) := ⟨pow_ne_zero _ hp'.pos.ne'⟩
  exact (ZMod.natCast_eq_zero_iff (hammingWeight x) (p ^ m.factorization p)).symm

/-!
**The CRT reduction, proved.**  A composite-`MOD_m` gate is exactly the conjunction of its prime-power residue gates, via
the product observer — the integer/multi-prime move generalised from `MOD₆` to all `m`.  Next sub-brick: the polylog-degree
representation of a single prime-power-`MOD` gate (Toda/RS symmetrization) and its quasipoly `SYM∘AND` packaging — the
content of `composite_BT_degree`, still open.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFactor

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFactor.dvd_iff_primePow_residues
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFactor.modm_iff_residues
