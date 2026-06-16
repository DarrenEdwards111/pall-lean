import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndComposition

/-!
# CRT generalisation — the prime-modulus gate polynomial, and composite `MOD` via coprime CRT

`MOD₆`'s two gate polynomials (`1+X` over `F₂`, `1−X²` over `F₃`) are both instances of one general form: over the prime
field `F_p`, the `MOD_p` indicator is `1 − X^{p−1}` (Fermat: `a^{p−1} = 1` for `a ≠ 0`), degree `p−1`.  This file builds
that **general prime-modulus gate polynomial** and composes distinct primes via coprime CRT (`p·q ∣ s ↔ p ∣ s ∧ q ∣ s`),
generalising `MOD₆` (`p=2, q=3`) to arbitrary squarefree composite modulus.

## What is proved (clean axioms, no `sorry`)

* **`modP_indicator`** — the Fermat indicator: `1 − a^{p−1} = [a = 0]` over `F_p` (`p` prime).
* **`modPGate p = 1 − X^{p−1}`** — the prime-modulus gate polynomial; **`modPGate_apply`** (computes the indicator),
  **`modPGate_degree` (≤ p−1)**, **`modPGate_eq_one`** (fires iff `a = 0`).
* **`modPGate_decides_dvd`** — the gate computes `MOD_p`: `eval (s) = 1 ↔ p ∣ s`.
* **`modPQGate_decides`** — composite via CRT: for *distinct* primes `p ≠ q`, both gates fire iff `p·q ∣ s` —
  arbitrary squarefree two-prime composite `MOD`.

## Honest scope

The prime-modulus gate polynomial (the general form of `MOD₆`'s components) is exact and low-degree, with evaluation,
degree, and `MOD_p` correctness proved; distinct primes compose via coprime CRT.  This generalises the `MOD₆` gate to
arbitrary primes and squarefree products.  Remaining: prime *powers* `p^e` (no field structure — needs a different
indicator), the full `Finset`-of-primes product, and the `AND`-layer + feed into `compositeBT_representation`.  This
builds the composite-`MOD` gate polynomials up to squarefree modulus; it does not assemble a full circuit
representation.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition (residue_observer_compose_coprime)

/-- **The Fermat indicator (proved): `1 − a^{p−1} = [a = 0]` over `F_p`.** -/
theorem modP_indicator (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    1 - a ^ (p - 1) = if a = 0 then 1 else 0 := by
  split
  · rename_i h
    rw [h, zero_pow (by have := (Fact.out : p.Prime).two_le; omega), sub_zero]
  · rename_i h
    rw [ZMod.pow_card_sub_one_eq_one h, sub_self]

/-- The prime-modulus gate polynomial over `F_p`: `1 − X^{p−1}` (degree `p−1`). -/
noncomputable def modPGate (p : ℕ) : MvPolynomial (Fin 1) (ZMod p) := C 1 - (X 0) ^ (p - 1)

/-- **`modPGate` computes the `MOD_p` indicator (proved): `eval a = [a = 0]`.** -/
theorem modPGate_apply (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    eval (fun _ => a) (modPGate p) = if a = 0 then 1 else 0 := by
  simp only [modPGate, map_sub, map_pow, eval_C, eval_X]
  exact modP_indicator p a

/-- **`modPGate` is degree `≤ p−1` (proved).** -/
theorem modPGate_degree (p : ℕ) [Fact p.Prime] : (modPGate p).totalDegree ≤ p - 1 := by
  refine le_trans (totalDegree_sub _ _) (max_le (by simp [totalDegree_C]) ?_)
  refine le_trans (totalDegree_pow _ _) ?_
  simp [totalDegree_X]

/-- **`modPGate` fires iff `a = 0` (proved).** -/
theorem modPGate_eq_one (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    eval (fun _ => a) (modPGate p) = 1 ↔ a = 0 := by
  rw [modPGate_apply]
  constructor
  · intro h; by_contra ha; rw [if_neg ha] at h; exact absurd h zero_ne_one
  · intro h; rw [if_pos h]

/-- **`modPGate` computes `MOD_p` of the count (proved): `eval (s) = 1 ↔ p ∣ s`.** -/
theorem modPGate_decides_dvd (p : ℕ) [Fact p.Prime] (s : ℕ) :
    eval (fun _ => (s : ZMod p)) (modPGate p) = 1 ↔ p ∣ s := by
  rw [modPGate_eq_one, ZMod.natCast_eq_zero_iff]

/-- **Composite `MOD` via CRT (proved): distinct primes compose.**  For primes `p ≠ q`, both gate polynomials fire iff
`p·q ∣ s` — arbitrary squarefree two-prime composite `MOD` (the `MOD₆` case is `p=2, q=3`). -/
theorem modPQGate_decides (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (s : ℕ) :
    (eval (fun _ => (s : ZMod p)) (modPGate p) = 1 ∧ eval (fun _ => (s : ZMod q)) (modPGate q) = 1)
      ↔ (p * q) ∣ s := by
  rw [modPGate_decides_dvd, modPGate_decides_dvd]
  exact (residue_observer_compose_coprime ((Nat.coprime_primes Fact.out Fact.out).mpr hpq) s).symm

end PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys.modP_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys.modPGate_apply
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys.modPGate_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys.modPGate_decides_dvd
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CRTGatePolys.modPQGate_decides
