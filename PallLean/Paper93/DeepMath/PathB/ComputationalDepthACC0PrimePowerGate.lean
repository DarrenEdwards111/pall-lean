import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndComposition

/-!
# Prime-power `MOD` — the CRT divisibility generalises, the low-degree field gate polynomial does **not**

Extending the composite-`MOD` gate to prime-power modulus `p^e` hits the genuine `ACC⁰[composite]` obstruction.  Two
things separate cleanly:

* **What generalises (proved here).**  The CRT divisibility: coprime prime powers compose, so `MOD_{p^a · q^b}` is
  decided by `(p^a ∣ s ∧ q^b ∣ s)`; and the *ring-level* residue observer `(s : ZMod (p^e)) = 0 ↔ p^e ∣ s` decides
  `MOD_{p^e}` over the ring `ZMod (p^e)`.

* **What does NOT generalise (the obstruction).**  The *low-degree field* gate polynomial.  For a prime `p`, the
  `MOD_p` indicator is `1 − X^{p−1}` over the **field** `F_p` (Fermat).  For a prime *power* `p^e` (`e ≥ 2`),
  `ZMod (p^e)` is **not a field** — `p` is a zero divisor, `a^k` does not collapse to `{0,1}`, and there is no
  Fermat-style low-degree indicator over a field.  This is exactly why the polynomial method gives `MOD_p` (`AC⁰[p]`)
  lower bounds but `ACC⁰[m]` for composite `m` (which contains prime-power and mixed structure) is open.  The
  squarefree case (`…ACC0CRTFinsetGate`) succeeded precisely because it avoids prime powers (distinct primes → a
  *product of fields*, Fermat per prime).

We prove the parts that generalise and record the obstruction; we do **not** fabricate a low-degree prime-power gate
polynomial (that would amount to the open lower bound).

## What is proved (clean axioms, no `sorry`)

* **`primePower_coprime`** — distinct prime powers are coprime.
* **`primePowerDvd_iff`** — `(p^a · q^b) ∣ s ↔ (p^a ∣ s ∧ q^b ∣ s)` (CRT divisibility for prime powers).
* **`modPrimePower_observer_decides`** — `(s : ZMod (p^e)) = 0 ↔ p^e ∣ s` (the ring-level residue observer for
  `MOD_{p^e}`).

## Honest scope

The CRT divisibility and the ring residue observer for prime powers are proved.  The low-degree *field* gate
polynomial — the ingredient the composite-BT pipeline needs to get a quasipolynomial representation — does **not**
exist for prime powers, and constructing one is equivalent to the open `ACC⁰[composite]` lower bound.  This is the
honest boundary of the algebraic-observer route.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerGate

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition (residue_observer_compose_coprime)

/-- **Distinct prime powers are coprime (proved).** -/
theorem primePower_coprime (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime (p ^ a) (q ^ b) :=
  Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)

/-- **CRT divisibility for prime powers (proved): `(p^a · q^b) ∣ s ↔ (p^a ∣ s ∧ q^b ∣ s)`.**  Coprime prime powers
compose — the divisibility side of the residue observer generalises to prime powers (unlike the low-degree
polynomial). -/
theorem primePowerDvd_iff (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (s : ℕ) :
    (p ^ a * q ^ b) ∣ s ↔ (p ^ a ∣ s ∧ q ^ b ∣ s) :=
  residue_observer_compose_coprime (primePower_coprime p q a b hp hq hpq) s

/-- **The ring-level residue observer decides `MOD_{p^e}` (proved): `(s : ZMod (p^e)) = 0 ↔ p^e ∣ s`.**  The residue of
the count in the ring `ZMod (p^e)` decides `MOD_{p^e}` — but `ZMod (p^e)` is not a field, so this carries *no*
low-degree field gate polynomial (the obstruction). -/
theorem modPrimePower_observer_decides (p e s : ℕ) :
    ((s : ZMod (p ^ e)) = 0) ↔ p ^ e ∣ s :=
  ZMod.natCast_eq_zero_iff s (p ^ e)

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerGate

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerGate.primePower_coprime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerGate.primePowerDvd_iff
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerGate.modPrimePower_observer_decides
