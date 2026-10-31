import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Pivoting the dynamic-SPDP candidate to `F_p`-degree

The MOD-recurrence attack (`NFrameMODRankRecurrence`) killed the ℚ-communication-rank candidate: it is bounded
(`≤ m`) on an isolated MOD gate but exponential on the depth-2 `AC⁰[2]` circuit `IP`, and — crucially — it is
**blind to the prime/composite distinction** (rank `≤ m` for every `m`).  The Razborov–Smolensky measure that
*does* see the distinction is **`F_p`-polynomial degree**.

This file establishes the degree-dual of the rank bound: the **"prime is controlled"** core.

## Result

`modp_low_degree_representation` — over `F_p = ZMod p` (`p` prime), the gate `MOD_p` (fires iff the number of
`1`s is `≡ 0 mod p`) is computed on Boolean inputs by a polynomial of **total degree `≤ p - 1`**, namely
`1 - (Σᵢ xᵢ)^{p-1}` (Fermat's little theorem: `s^{p-1} = [s ≠ 0]` over `F_p`).

So a `MOD_p` gate has `F_p`-degree `≤ p - 1` — bounded, independent of `n` and fan-in, the exact degree-analogue
of the rank-`≤ m` bound.  But unlike ℚ-rank, this is **specific to the matching prime**: the same construction
gives *no* low-degree polynomial for `MOD_q` with `q ≠ p` (the `(p-1)`-power trick collapses only the residue
mod `p`).  That gap — `MOD_p` low `F_p`-degree, `MOD_q` high `F_p`-degree — is what a degree dynamic-SPDP tracks
and communication rank cannot.

## Where the route continues, and where it walls

`F_p`-degree is a genuine candidate: over `F_p` the AND/OR gates admit low *approximate* (probabilistic) degree
(the repo's `approximable_exists` Razborov–Smolensky arc), NOT preserves it, and `MOD_p` is exactly degree
`≤ p - 1` (proved here).  So the ACC-upper side works for `AC⁰[p]` (a single prime).  The undischarged wall is
exactly `MOD_q` for `q ≠ p` and **composite / mixed moduli**: no single field gives them low degree ("Wall 1").
This file proves only the positive `MOD_p` half; the composite-MOD degree lower bound is the open obstruction.

## Honest scope

The exact low-degree `F_p` representation of the `MOD_p` gate (Fermat).  It shows `F_p`-degree is bounded on the
matching-prime MOD gate — the reason the measure fits `AC⁰[p]`.  No composite-MOD lower bound, no ACC⁰ lower
bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFpDegree

open MvPolynomial

/-- Hamming weight: number of `true` coordinates. -/
def weight {k : Nat} (z : Fin k → Bool) : Nat :=
  (Finset.univ.filter (fun i => z i)).card

section
variable (p : Nat) [Fact p.Prime]

/-- Embed a bit into `F_p`. -/
def boolToZMod (b : Bool) : ZMod p := if b then 1 else 0

/-- The `MOD_p` gate: fires iff the weight is `≡ 0 (mod p)`. -/
def MODp {k : Nat} (z : Fin k → Bool) : Bool := decide (weight z % p = 0)

/-- The candidate polynomial `1 - (Σᵢ Xᵢ)^{p-1}` over `F_p`. -/
noncomputable def modpPoly (k : Nat) : MvPolynomial (Fin k) (ZMod p) :=
  1 - (∑ i, MvPolynomial.X i) ^ (p - 1)

/-- **Degree bound.**  `modpPoly` has total degree `≤ p - 1`. -/
theorem modpPoly_totalDegree_le (k : Nat) : (modpPoly p k).totalDegree ≤ p - 1 := by
  have hsum : (∑ i : Fin k, MvPolynomial.X i : MvPolynomial (Fin k) (ZMod p)).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
    intro i _
    exact le_of_eq (MvPolynomial.totalDegree_X i)
  have hpow : ((∑ i : Fin k, MvPolynomial.X i : MvPolynomial (Fin k) (ZMod p)) ^ (p - 1)).totalDegree
      ≤ p - 1 := by
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    calc (p - 1) * (∑ i : Fin k, MvPolynomial.X i : MvPolynomial (Fin k) (ZMod p)).totalDegree
        ≤ (p - 1) * 1 := Nat.mul_le_mul (le_refl _) hsum
      _ = p - 1 := Nat.mul_one _
  rw [modpPoly]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ hpow)
  rw [MvPolynomial.totalDegree_one]
  exact Nat.zero_le _

/-- The sum of the embedded bits is the weight, cast into `F_p`. -/
theorem sum_boolToZMod {k : Nat} (z : Fin k → Bool) :
    (∑ i, boolToZMod p (z i)) = (weight z : ZMod p) := by
  simp only [boolToZMod, weight]
  rw [Finset.sum_boole]

/-- **`MOD_p` is computed by `modpPoly` on Boolean inputs** (Fermat's little theorem). -/
theorem modpPoly_eval {k : Nat} (z : Fin k → Bool) :
    MvPolynomial.eval (fun i => boolToZMod p (z i)) (modpPoly p k) = boolToZMod p (MODp p z) := by
  rw [modpPoly, map_sub, map_one, map_pow, map_sum]
  simp only [MvPolynomial.eval_X]
  rw [sum_boolToZMod]
  have hp2 : 2 ≤ p := Nat.Prime.two_le Fact.out
  by_cases hz : weight z % p = 0
  · have hw0 : (weight z : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.dvd_of_mod_eq_zero hz
    have hpm : p - 1 ≠ 0 := by omega
    have hmod : MODp p z = true := by unfold MODp; rw [decide_eq_true_eq]; exact hz
    rw [hw0, zero_pow hpm, sub_zero, hmod]
    rfl
  · have hwne : (weight z : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hz (Nat.mod_eq_zero_of_dvd h0)
    have hmod : MODp p z = false := by unfold MODp; rw [decide_eq_false_iff_not]; exact hz
    rw [ZMod.pow_card_sub_one_eq_one hwne, sub_self, hmod]
    rfl

/-- **The prime case is controlled.**  `MOD_p` has an exact `F_p`-polynomial representation of total degree
`≤ p - 1` — the degree-dual of the rank-`≤ m` bound, and (unlike ℚ-rank) specific to the matching prime. -/
theorem modp_low_degree_representation (k : Nat) :
    ∃ P : MvPolynomial (Fin k) (ZMod p), P.totalDegree ≤ p - 1 ∧
      ∀ z : Fin k → Bool, MvPolynomial.eval (fun i => boolToZMod p (z i)) P = boolToZMod p (MODp p z) :=
  ⟨modpPoly p k, modpPoly_totalDegree_le p k, fun z => modpPoly_eval p z⟩

end

end PallLean.Paper93.DeepMath.PathB.NFrameFpDegree

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpDegree.modpPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpDegree.modpPoly_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpDegree.modp_low_degree_representation
