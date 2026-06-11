import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Layer 4 (foundation) — `q`-th roots of unity in a finite field

Brick (2) of `SCOPE_LAYER4_MODq_GENERALIZATION.md`.  The `MOD_q` argument needs a primitive `q`-th root
of unity `ζ`, the value the weight character `ζ^{#ones}` (`ComputationalDepthLayer4ModqChar`) runs over.
For `q > 2` such a `ζ` is **not** in `F_p`; it lives in the extension `F_{p^k}`.  Here:

* `exists_isPrimitiveRoot_of_dvd` — in **any** finite field `F`, a primitive `q`-th root exists whenever
  `q ∣ |F| − 1` (the multiplicative group `Fˣ` is cyclic of order `|F|−1`, so it has an element of order
  `q`; `IsCyclic.card_orderOf_eq_totient` makes the count `totient q > 0`).
* `dvd_pow_sub_one` — Fermat: for primes `p, q` with `q ∤ p`, `q ∣ p^{q-1} − 1`.
* `exists_primitiveRoot_galoisField` — combining the two: `GaloisField p (q-1) = F_{p^{q-1}}` contains a
  primitive `q`-th root of unity (for distinct primes `p, q`).

This pins down the field and the element `ζ`.  The genuinely new mathematics — the `q`-ary
degree-reduction replacing parity's `y²=1` (scope §3 C) — is still deferred and must not be faked.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open Finset

/-- **Primitive `q`-th root from `q ∣ |F| − 1`.**  Any finite field whose order is `≡ 1 (mod q)` contains
a primitive `q`-th root of unity, since `Fˣ` is cyclic of order `|F|−1` (number of order-`q` elements is
`totient q > 0`). -/
theorem exists_isPrimitiveRoot_of_dvd {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}
    (hq0 : 0 < q) (hq : q ∣ Fintype.card F - 1) : ∃ ζ : F, IsPrimitiveRoot ζ q := by
  have hqu : q ∣ Fintype.card Fˣ := by rw [Fintype.card_units]; exact hq
  have hcount := IsCyclic.card_orderOf_eq_totient (α := Fˣ) hqu
  have hpos : 0 < (Finset.univ.filter (fun u : Fˣ => orderOf u = q)).card := by
    rw [hcount]; exact Nat.totient_pos.mpr hq0
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hu
  exact ⟨(u : F), by rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hu.2]⟩

/-- **Fermat divisibility.**  For a prime `q` with `q ∤ p`, `q ∣ p^{q-1} − 1` (Fermat's little theorem:
`p^{q-1} ≡ 1 (mod q)`).  So `F_{p^{q-1}}` has order `≡ 1 (mod q)`. -/
theorem dvd_pow_sub_one {p q : ℕ} [Fact q.Prime] (hpq : ¬ q ∣ p) : q ∣ p ^ (q - 1) - 1 := by
  have hp0 : p ≠ 0 := fun h => hpq (h ▸ dvd_zero q)
  have hne : (p : ZMod q) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpq
  have hmod : p ^ (q - 1) ≡ 1 [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast; exact ZMod.pow_card_sub_one_eq_one hne
  exact (Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp0))).mp hmod.symm

/-- **The field and the root for `MOD_q`.**  For distinct primes `p, q` (`q ∤ p`), the Galois field
`F_{p^{q-1}} = GaloisField p (q-1)` contains a primitive `q`-th root of unity — the `ζ` over which the
weight character `ζ^{#ones}` of `ComputationalDepthLayer4ModqChar` detects the Hamming weight mod `q`. -/
theorem exists_primitiveRoot_galoisField {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p) :
    ∃ ζ : GaloisField p (q - 1), IsPrimitiveRoot ζ q := by
  classical
  have hq2 : 2 ≤ q := (Fact.out (p := q.Prime)).two_le
  haveI : Fintype (GaloisField p (q - 1)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p (q - 1)) = p ^ (q - 1) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p (q - 1) (by omega)]
  exact exists_isPrimitiveRoot_of_dvd (by omega) (by rw [hcard]; exact dvd_pow_sub_one hpq)

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.exists_isPrimitiveRoot_of_dvd
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.dvd_pow_sub_one
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.exists_primitiveRoot_galoisField
