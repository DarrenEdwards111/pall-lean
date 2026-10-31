import Mathlib

/-!
# A p-adic / carry invariant at the `ApproxToExactCount` seam (conservative fragments, proved)

Entry 234 isolated **`ApproxToExactCount`** — the weighted-`F_p`-span → exact-unit-count conversion — as the
composite-`ACC⁰[m]` barrier.  This file begins the N-Frame **invariant search** at that seam, conservatively: it
formalises the **field power-indicator** `y^e = [y ≠ 0]` (the algebraic primitive that turns a weighted "this `AND` is
satisfied" bit into an *exact* `0/1` count) and proves *safe fragment theorems* about where it exists and where carries
force observer refinement.  It deliberately does **not** claim a global "obstructs exactification" result — only the
fragment properties that characterise the prime / prime-power / composite seam.

⚠️ **Scope discipline.**  These are diagnostic fragments about a candidate invariant.  They *characterise* the carry
seam (which observer can see what); they do **not** cross the barrier, and none of them is a separation result.

## The candidate invariant

`PowerIndicator m := ∃ e ≥ 1, ∀ y : ZMod m, y^e = if y = 0 then 0 else 1` — an exponent making the `e`-th power the
exact `0/1` indicator of "nonzero".  This is the primitive the polynomial method uses to read a satisfied gate as a
count contribution.

## What is proved (clean axioms, no `sorry`)

* **`powerIndicator_of_prime`** (PROVED) — **MOD_p: no carry obstruction.**  Over a prime field `ZMod p` the indicator
  exists (`e = p - 1`, Fermat: `y^(p-1) = 1` for `y ≠ 0`, `0^(p-1) = 0`).
* **`not_powerIndicator_of_zeroDivisor`** (PROVED) — the obstruction primitive: a zero-divisor `z` (`z ≠ 0`, `z·w = 0`,
  `w ≠ 0`) kills the indicator (it would force `z^e = 1`, making `z·(stuff) = 1`, so `w = z^{e-1}·z·w = 0`).
* **`not_powerIndicator_primePow`** (PROVED) — **MOD_{p^e}: carry profile nontrivial.**  Over `ZMod (p^e)` for `e ≥ 2`
  the `ZMod`-level indicator *fails* (`p` is a zero-divisor: `p · p^{e-1} = p^e = 0`).  RS recovers `p^e` only via the
  *extension field* `GF(p^e) ≠ ZMod (p^e)` — i.e. the prime-power case genuinely needs the carry/field layer.
* **`field_observer_blind_to_carry`** (PROVED) — **field observer cannot distinguish a p-adic carry.**  `k = 0` and
  `k' = p` agree under the mod-`p` (field) observer but differ under the refined mod-`p^2` observer: the weighted-`F_p`
  view ignores the carry layer that the exact count must see.
* **`crt_residue_observer_suffices`** (PROVED) — **squarefree m: CRT residue observer suffices.**  For coprime `a, b`,
  `ZMod (a·b) ≃+* ZMod a × ZMod b` — the residue profile determines the value, *no carry layer* (contrast prime-power).

## Honest scope

These are **conservative fragment theorems** characterising a candidate carry/CRT invariant: the field power-indicator
exists for primes (`powerIndicator_of_prime`), the prime-power layer carries nontrivial structure invisible at the
`ZMod`-level field indicator (`not_powerIndicator_primePow`), the field observer is blind to p-adic carries
(`field_observer_blind_to_carry`), and squarefree moduli factor cleanly via CRT residues
(`crt_residue_observer_suffices`).  Together they pinpoint *where* the weighted-`F_p` observer and the exact-unit-count
observer must diverge — the **N-Frame "boundary forces observer refinement"** picture at the `ApproxToExactCount` seam.
This is a **characterisation of the seam**, not a crossing of it: no claim here forces exactification for composite `m`,
which remains the open `ACC⁰[m]` barrier (entry 234).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant

/-- **The field power-indicator (candidate invariant).**  An exponent `e ≥ 1` making `y^e` the exact `0/1` indicator of
"`y ≠ 0`" over `ZMod m`.  This is the algebraic primitive that converts a weighted "`AND` satisfied" bit into an exact
count contribution; its existence is the field-route precondition of the RS/BT exactification. -/
def PowerIndicator (m : ℕ) : Prop :=
  ∃ e, 1 ≤ e ∧ ∀ y : ZMod m, y ^ e = if y = 0 then 0 else 1

/-- **MOD_p: no carry obstruction (PROVED).**  Over a prime field the power-indicator exists, with `e = p - 1`: for
`y ≠ 0`, `y^(p-1) = 1` (Fermat's little theorem); for `y = 0`, `0^(p-1) = 0`. -/
theorem powerIndicator_of_prime (p : ℕ) [Fact p.Prime] : PowerIndicator p := by
  refine ⟨p - 1, ?_, ?_⟩
  · have := (Fact.out : p.Prime).two_le; omega
  · intro y
    by_cases hy : y = 0
    · subst hy
      simp [zero_pow (by have := (Fact.out : p.Prime).two_le; omega : p - 1 ≠ 0)]
    · rw [if_neg hy, ZMod.pow_card_sub_one_eq_one hy]

/-- **The obstruction primitive (PROVED).**  A zero-divisor `z` (`z ≠ 0`, `z·w = 0` with `w ≠ 0`) destroys the
power-indicator: the indicator would force `z^e = 1`, whence `w = (z^{e-1}·z)·w = z^{e-1}·(z·w) = 0`, contradicting
`w ≠ 0`. -/
theorem not_powerIndicator_of_zeroDivisor (m : ℕ) (z w : ZMod m) (hz : z ≠ 0)
    (hw : w ≠ 0) (hzw : z * w = 0) : ¬ PowerIndicator m := by
  rintro ⟨e, he, hind⟩
  have hz1 : z ^ e = 1 := by rw [hind z, if_neg hz]
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hu : z ^ e' * z = 1 := by rw [← pow_succ]; exact hz1
  apply hw
  calc w = (z ^ e' * z) * w := by rw [hu, one_mul]
    _ = z ^ e' * (z * w) := by ring
    _ = 0 := by rw [hzw, mul_zero]

/-- **MOD_{p^e}: carry profile nontrivial (PROVED).**  Over `ZMod (p^e)` for `e ≥ 2`, the `ZMod`-level power-indicator
*fails*: `p` is a zero-divisor (`p · p^{e-1} = p^e = 0`, with `p ≠ 0` and `p^{e-1} ≠ 0` since `p, p^{e-1} < p^e`).  So
the prime-power case is not handled at the `ZMod (p^e)` level — RS recovers it only via the extension field `GF(p^e)`,
i.e. the carry/field layer is genuinely needed. -/
theorem not_powerIndicator_primePow (p e : ℕ) [Fact p.Prime] (he : 2 ≤ e) :
    ¬ PowerIndicator (p ^ e) := by
  have hp2 := (Fact.out : p.Prime).two_le
  refine not_powerIndicator_of_zeroDivisor (p ^ e) (p : ZMod (p ^ e))
    ((p : ZMod (p ^ e)) ^ (e - 1)) ?_ ?_ ?_
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h1 : p ^ e ≤ p := Nat.le_of_dvd (by omega) hdvd
    have h2 : p < p ^ e := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ e := Nat.pow_lt_pow_right hp2 (by omega)
    omega
  · rw [← Nat.cast_pow, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h1 : p ^ e ≤ p ^ (e - 1) := Nat.le_of_dvd (pow_pos (by omega : 0 < p) _) hdvd
    have h2 : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp2 (by omega)
    omega
  · rw [← Nat.cast_pow, ← Nat.cast_mul]
    have hpe : p * p ^ (e - 1) = p ^ e := by rw [← pow_succ']; congr 1; omega
    rw [hpe, ZMod.natCast_self]

/-- **Field observer cannot distinguish a p-adic carry (PROVED).**  The mod-`p` (field) observer collapses `k = 0` and
`k' = p` (both `≡ 0`), but the refined mod-`p^2` observer separates them (`0 ≠ p` in `ZMod (p^2)`, since `p < p^2`).
Equivalently: **the unit-count observer changes under carry refinement** — the weighted-`F_p` view ignores the carry
layer that the exact count must respect. -/
theorem field_observer_blind_to_carry (p : ℕ) [Fact p.Prime] :
    ∃ k k' : ℕ, (k : ZMod p) = (k' : ZMod p) ∧ (k : ZMod (p ^ 2)) ≠ (k' : ZMod (p ^ 2)) := by
  refine ⟨0, p, ?_, ?_⟩
  · simp
  · simp only [Nat.cast_zero]
    rw [ne_comm, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hp2 := (Fact.out : p.Prime).two_le
    have h1 : p ^ 2 ≤ p := Nat.le_of_dvd (by omega) hdvd
    have h2 : p < p ^ 2 := by nlinarith
    omega

/-- **Squarefree m: CRT residue observer suffices (PROVED).**  For coprime `a, b`, the Chinese Remainder isomorphism
`ZMod (a·b) ≃+* ZMod a × ZMod b` shows the residue *profile* `(· mod a, · mod b)` determines the value mod `a·b` — no
carry layer.  Iterating over distinct prime factors, the residue observer suffices for squarefree moduli (contrast the
prime-power case, where carries are nontrivial by `not_powerIndicator_primePow`). -/
theorem crt_residue_observer_suffices (a b : ℕ) (h : Nat.Coprime a b) :
    Nonempty (ZMod (a * b) ≃+* ZMod a × ZMod b) :=
  ⟨ZMod.chineseRemainder h⟩

end PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant.powerIndicator_of_prime
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant.not_powerIndicator_primePow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant.field_observer_blind_to_carry
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant.crt_residue_observer_suffices
