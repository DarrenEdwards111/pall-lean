import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPoly
import Mathlib.FieldTheory.Finite.Basic

/-!
# Layer 3 — the MOD-gate case of the circuit → polynomial representation

Extends the exact representation `toPoly` to the `MOD_p` gate (completing `IsAC0pSyntax`), via the
**Fermat indicator**: over a prime field `ZMod p`, `1 - y^(p-1) = [y = 0]` (`ZMod.pow_card_sub_one_eq_one`).
A `MOD_p` gate `# true ≡ r (mod p)` becomes the field condition `(∑ embed) - r = 0`, whose indicator is
that degree-`(p-1)` polynomial.

* `fermat_indicator` — `1 - y^(p-1) = if y = 0 then 1 else 0` (prime `p`).
* `eval_sum_toPolyList` / `boolToZMod_sum_list` — `∑ embed = (#true : ZMod p)`.
* `toPoly_modGate_eval` — the `MOD_p`-gate case of correctness (given the per-child identities), so the
  representation is exact at MOD gates too.

No lower bound, no capstone.  AC⁰[p] is a higher circuit-lower-bound layer; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open PallLean.Paper93.DeepMath.PathB
open MvPolynomial

variable {n : ℕ}

/-- **The Fermat indicator over a prime field.**  `1 - y^(p-1) = [y = 0]`. -/
theorem fermat_indicator (p : ℕ) [Fact p.Prime] (y : ZMod p) :
    1 - y ^ (p - 1) = if y = 0 then 1 else 0 := by
  by_cases hy : y = 0
  · subst hy
    have hp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    rw [if_pos rfl, zero_pow hp, sub_zero]
  · rw [if_neg hy, ZMod.pow_card_sub_one_eq_one hy, sub_self]

/-- Evaluating `∑ toPolyList` factors through the per-circuit evaluation (the sum analog of
`eval_prod_toPolyList`). -/
theorem eval_sum_toPolyList (p : ℕ) (x : Fin n → Bool) {f : BoolCircuitSyntax n → ZMod p}
    (cs : List (BoolCircuitSyntax n))
    (hf : ∀ c ∈ cs, MvPolynomial.eval (embed p x) (toPoly p c) = f c) :
    MvPolynomial.eval (embed p x) (toPolyList p cs).sum = (cs.map f).sum := by
  induction cs with
  | nil => simp [toPolyList]
  | cons c cs ih =>
      rw [toPolyList, List.sum_cons, map_add, hf c (by simp),
        ih (fun c' hc' => hf c' (by simp [hc'])), List.map_cons, List.sum_cons]

/-- The `{0,1}`-sum over `ZMod p` is the count of `true`s. -/
theorem boolToZMod_sum_list (p : ℕ) (L : List Bool) :
    (L.map (boolToZMod p)).sum = ((L.filter id).length : ZMod p) := by
  induction L with
  | nil => simp
  | cons b L ih =>
      rw [List.map_cons, List.sum_cons, ih]
      cases b <;> simp [boolToZMod, List.filter_cons] <;> push_cast <;> ring

/-- **The `MOD_p`-gate case of the representation correctness.**  Given the per-child identities, the
representing polynomial of a `MOD_p` gate (modulus `= p`) evaluates to the gate's `{0,1}` output. -/
theorem toPoly_modGate_eval (p : ℕ) [Fact p.Prime] (x : Fin n → Bool) (r : ℕ)
    (cs : List (BoolCircuitSyntax n))
    (hcs : ∀ c ∈ cs, MvPolynomial.eval (embed p x) (toPoly p c) = boolToZMod p (c.eval x)) :
    MvPolynomial.eval (embed p x) (toPoly p (.modGate p r cs))
      = boolToZMod p ((BoolCircuitSyntax.modGate p r cs).eval x) := by
  have hsum : MvPolynomial.eval (embed p x) (toPolyList p cs).sum
      = (((cs.map (fun c => c.eval x)).filter id).length : ZMod p) := by
    rw [eval_sum_toPolyList p x cs hcs, ← boolToZMod_sum_list p (cs.map (fun c => c.eval x)),
      List.map_map]
    rfl
  simp only [toPoly, BoolCircuitSyntax.eval, map_sub, map_one, map_pow, MvPolynomial.eval_C, hsum]
  rw [fermat_indicator]
  by_cases hc0 : (((cs.map (fun c => c.eval x)).filter id).length : ZMod p) - (r : ZMod p) = 0
  · have hmod : ((cs.map (fun c => c.eval x)).filter id).length % p = r % p := by
      have := (sub_eq_zero.mp hc0)
      rwa [ZMod.natCast_eq_natCast_iff] at this
    rw [if_pos hc0]; simp [boolToZMod, hmod]
  · have hmod : ¬ (((cs.map (fun c => c.eval x)).filter id).length % p = r % p) := by
      intro h
      exact hc0 (by rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]; exact h)
    rw [if_neg hc0]; simp [boolToZMod, hmod]

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.fermat_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toPoly_modGate_eval
