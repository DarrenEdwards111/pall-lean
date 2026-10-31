import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerGate
import Mathlib.Algebra.Polynomial.Roots

/-!
# Route 1 — non-field low-degree theory: why the prime-power indicator resists a low-degree representation

The observer scorecard (`…ACC0PrimePowerObserverCandidates`, `…Tower…`, `…Digit…`) showed every observer that *sees*
`MOD_{p^e}` is non-field (the ring `ZMod p^e`, the valuation, the tower, the digits — all information-equivalent, none
a field).  The open `ACC⁰[composite]` crux is whether such a non-field observer admits a *quasipolynomial low-degree
sparse* representation.  This file tests that question honestly and proves the two facts that bound it.

* **Over a field, the prime-power indicator needs HIGH degree.**  The `MOD_{p^e}` indicator (on the count `s`) rejects
  the `p^e - 1` consecutive non-multiples `1, 2, …, p^e-1`.  In a field of characteristic `0` (or `> p^e-1`) these are
  distinct, so any nonzero polynomial vanishing on them has degree `≥ p^e - 1` (root counting).  Hence a *field*
  representation of `MOD_{p^e}` has degree `≥ p^e - 1` — exponential in `e`, useless for the polynomial method, which
  needs polylog degree.  This is why the field route gives `MOD_p` (collapse mod `p` to `{0,…,p-1}`, degree `p-1`) but
  cannot reach `p^e` without reducing mod `p^e` — which leaves the category of fields.

* **Over the ring `ZMod p^e`, the root-counting machinery FAILS.**  `C(p^{e-1})·X` has natDegree `≤ 1` yet two distinct
  roots `0` and `p` (because `p^{e-1}·p = p^e = 0` in the ring).  So the very lemma that forces high degree over a
  field is *false* over the ring — there is no degree/root obstruction to lean on.  This is exactly why no low-degree
  lower bound is available over the non-field observer, and why constructing a low-degree representation there (or
  ruling one out) is the open problem rather than a corollary of root counting.

## What is proved (clean axioms, no `sorry`)

* **`field_root_card_le_natDegree`** — over a field, a nonzero polynomial vanishing on a finset of size `k` has
  `natDegree ≥ k` (the root bound).
* **`modPrimePower_field_indicator_high_degree`** — a char-`0` field polynomial vanishing on `{1,…,p^e-1}` has
  `natDegree ≥ p^e - 1` (the field representation of `MOD_{p^e}` is high degree).
* **`ring_root_count_fails`** — over `ZMod (p^e)` (`e ≥ 2`) there is a natDegree-`≤ 1` nonzero polynomial with two
  distinct roots `0 ≠ p`; the field root bound is false over the ring.

## Honest scope

This is the honest verdict on Route 1: the field route is *quantitatively* blocked (degree `≥ p^e - 1`), and the only
observers that escape are non-field, where the degree-bounding machinery itself collapses.  We do **not** construct a
low-degree sparse representation over a non-field observer, and we do **not** prove one cannot exist — either would be
the open `ACC⁰[composite]` lower bound.  What is established is *why* the question is genuinely open and not reducible
to root counting: the obstruction is the absence of a field, not a missing computation.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NonFieldObserverTheory

open Polynomial

/-- **The field root bound (proved): a nonzero polynomial vanishing on a finset of size `k` has `natDegree ≥ k`.**
Over a field (no zero divisors) the distinct roots inject into `g.roots`, whose multiset cardinality is `≤ natDegree`. -/
theorem field_root_card_le_natDegree {F : Type*} [Field F] (g : Polynomial F) (s : Finset F)
    (hg : g ≠ 0) (h : ∀ x ∈ s, g.eval x = 0) : s.card ≤ g.natDegree := by
  classical
  have hsub : s ⊆ g.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hg]
    exact h x hx
  calc s.card ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := card_roots' g

/-- **The field representation of `MOD_{p^e}` is high degree (proved): `natDegree ≥ p^e - 1`.**  `MOD_{p^e}` rejects the
`p^e - 1` consecutive non-multiples `1, …, p^e-1`; in a characteristic-`0` field these are distinct, so any nonzero
polynomial vanishing on them has degree `≥ p^e - 1`.  Exponential in `e` — the field route cannot give the polylog
degree the polynomial method needs. -/
theorem modPrimePower_field_indicator_high_degree {F : Type*} [Field F] [CharZero F]
    (p e : ℕ) (g : Polynomial F) (hg : g ≠ 0)
    (hrej : ∀ k : ℕ, 1 ≤ k → k ≤ p ^ e - 1 → g.eval (k : F) = 0) :
    p ^ e - 1 ≤ g.natDegree := by
  classical
  set s : Finset F := (Finset.Icc 1 (p ^ e - 1)).image (fun k : ℕ => (k : F)) with hs
  have hcard : s.card = p ^ e - 1 := by
    rw [hs, Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
    omega
  have hroots : ∀ x ∈ s, g.eval x = 0 := by
    intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_Icc] at hk
    exact hrej k hk.1 hk.2
  calc p ^ e - 1 = s.card := hcard.symm
    _ ≤ g.natDegree := field_root_card_le_natDegree g s hg hroots

/-- **The root bound FAILS over the ring `ZMod (p^e)` (proved).**  `C(p^{e-1})·X` has `natDegree ≤ 1` and is nonzero,
yet it vanishes at the two distinct points `0` and `p` (since `p^{e-1}·p = p^e = 0` in `ZMod (p^e)`).  So a degree-`≤1`
polynomial has `≥ 2` roots — the field lemma `field_root_card_le_natDegree` is false over the non-field ring.  The
degree-bounding machinery that blocks the field route has no analogue here, which is why the non-field low-degree
question is genuinely open. -/
theorem ring_root_count_fails (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    ∃ g : Polynomial (ZMod (p ^ e)),
      g.natDegree ≤ 1 ∧ g ≠ 0 ∧
      ((0 : ZMod (p ^ e)) ≠ (p : ZMod (p ^ e))) ∧
      g.eval 0 = 0 ∧ g.eval (p : ZMod (p ^ e)) = 0 := by
  haveI : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
  have hane : ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (pow_pos hp.pos (e - 1)) h
    have : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  have hpne : ((p : ℕ) : ZMod (p ^ e)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd hp.pos h
    have : p < p ^ e := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  refine ⟨C ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) * X, ?_, ?_, ?_, ?_, ?_⟩
  · calc (C ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) * X).natDegree
        ≤ (C ((p ^ (e - 1) : ℕ) : ZMod (p ^ e))).natDegree + X.natDegree := natDegree_mul_le
      _ ≤ 1 := by rw [natDegree_C, natDegree_X]
  · intro hz
    have hco : (C ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) * X).coeff 1
        = ((p ^ (e - 1) : ℕ) : ZMod (p ^ e)) := by rw [coeff_C_mul, coeff_X_one, mul_one]
    rw [hz, coeff_zero] at hco
    exact hane hco.symm
  · exact fun h => hpne h.symm
  · simp
  · rw [eval_mul, eval_C, eval_X, ← Nat.cast_mul,
        show p ^ (e - 1) * p = p ^ e by rw [← pow_succ]; congr 1; omega]
    exact ZMod.natCast_self (p ^ e)

end PallLean.Paper93.DeepMath.PathB.ACC0NonFieldObserverTheory

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonFieldObserverTheory.field_root_card_le_natDegree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonFieldObserverTheory.modPrimePower_field_indicator_high_degree
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NonFieldObserverTheory.ring_root_count_fails
