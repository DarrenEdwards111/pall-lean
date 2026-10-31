import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitRepr
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTwoGateCorrelation

/-!
# Brick (AC⁰[p] repr) — recursive faithful representation of AC⁰[p] circuits over `F_p` (proved)

The recursive faithful circuit representation for the Razborov–Smolensky setting: `AC⁰[p]` circuits — binary `AND`/`OR`/`NOT`
plus `MOD_p` gates (modulus equal to the field characteristic).  By structural recursion, every such circuit `C` is
represented *exactly* by a polynomial `reprP C` over `F_p` with `eval (bv ∘ x) (reprP C) = bv (eval C x)` on **all** Boolean
inputs, of total degree `≤ reprDegP C`.  The `MOD_p` gate `[∑_{i∈S} xᵢ ≡ t]` is the Fermat indicator
`1 - (∑_{i∈S} Xᵢ - t)^{p-1}` (degree `p-1`).

Because the `AND`/`OR` gates are *binary*, no probabilistic approximation is needed — the representation is exact, and for
constant depth the degree is constant.  This is the recursive faithful representation in full for the `AC⁰[p]` class; it is
the object whose existence, combined with `MOD_q` (`q ≠ p`) having *no* low-degree `F_p` representation, is the Razborov–
Smolensky separation `MOD_q ∉ AC⁰[p]`.

## What is proved (clean axioms, no `sorry`)

* **`ModpOnly`**, **`reprP`**, **`reprDegP`** — the predicate (mod gates have modulus `p`), the representation, its degree.
* **`reprP_eval`** (PROVED) — `ModpOnly p C → eval (bv ∘ x) (reprP C) = bv (ACC0CircuitModel.eval C x)`.
* **`reprP_totalDegree_le`** (PROVED) — `(reprP C).totalDegree ≤ reprDegP C`.

## Honest scope

The exact recursive representation of `AC⁰[p]` (binary `AND`/`OR`/`NOT` + `MOD_p`).  It does **not** represent `MOD_q` gates
with `q ≠ p` (RS: no low-degree `F_p` representation — this is the *content* of the lower bound, *not* a gap to fill), the
`q = p^e` prime-power case (A.3 obstruction), large-fan-in approximation, nor the `composite_BT_degree` cash-out.  General YBT
remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv bv_not bv_and bv_or)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)

variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- An `AC⁰[p]` circuit: every `mod` gate has modulus `p`. -/
def ModpOnly (p : ℕ) : ACC0Circuit n → Prop
  | .const _ => True
  | .var _ => True
  | .not c => ModpOnly p c
  | .and a b => ModpOnly p a ∧ ModpOnly p b
  | .or a b => ModpOnly p a ∧ ModpOnly p b
  | .mod q _ _ => q = p

/-- Exact polynomial representation of an `AC⁰[p]` circuit over `F_p`. -/
noncomputable def reprP (p : ℕ) : ACC0Circuit n → MvPolynomial (Fin n) (ZMod p)
  | .const b => if b then 1 else 0
  | .var i => X i
  | .not c => 1 - reprP p c
  | .and a b => reprP p a * reprP p b
  | .or a b => reprP p a + reprP p b - reprP p a * reprP p b
  | .mod _ S t => 1 - (∑ i ∈ S, X i - C (ZMod.cast t)) ^ (p - 1)

/-- Degree measure for `reprP`. -/
def reprDegP (p : ℕ) : ACC0Circuit n → ℕ
  | .const _ => 0
  | .var _ => 1
  | .not c => reprDegP p c
  | .and a b => reprDegP p a + reprDegP p b
  | .or a b => reprDegP p a + reprDegP p b
  | .mod _ _ _ => p - 1

/-- The Hamming weight over a support, cast to `F_p`, is the sum of the bit embeddings. -/
theorem weight_cast (S : Finset (Fin n)) (x : Fin n → Bool) :
    ∑ i ∈ S, (bv (x i) : ZMod p) = (weightOn S x : ZMod p) := by
  rw [weightOn, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [bv]; by_cases h : x i = true <;> simp [h]

/-- **Faithfulness (PROVED): `reprP` computes the `AC⁰[p]` circuit exactly on Boolean inputs.** -/
theorem reprP_eval (C : ACC0Circuit n) (x : Fin n → Bool) :
    ModpOnly p C →
      eval (fun i => (bv (x i) : ZMod p)) (reprP p C) = bv (ACC0CircuitModel.eval C x) := by
  induction C with
  | const b => intro _; cases b <;> simp [reprP, ACC0CircuitModel.eval, bv]
  | var i => intro _; simp [reprP, ACC0CircuitModel.eval, bv]
  | not c ih =>
      intro h; simp only [ModpOnly] at h
      simp only [reprP, ACC0CircuitModel.eval, map_sub, map_one]
      rw [ih h, bv_not]
  | and a b iha ihb =>
      intro h; simp only [ModpOnly] at h
      simp only [reprP, ACC0CircuitModel.eval, map_mul]
      rw [iha h.1, ihb h.2, bv_and]
  | or a b iha ihb =>
      intro h; simp only [ModpOnly] at h
      simp only [reprP, ACC0CircuitModel.eval, map_sub, map_add, map_mul]
      rw [iha h.1, ihb h.2, bv_or]
  | mod q S t =>
      intro h; simp only [ModpOnly] at h; subst q
      simp only [reprP, ACC0CircuitModel.eval, modQStatOn, map_sub, map_one, map_pow, map_sum,
        eval_X, eval_C, ZMod.cast_id]
      rw [weight_cast]
      by_cases hwt : (weightOn S x : ZMod p) = t
      · have hd : decide ((weightOn S x : ZMod p) = t) = true := by simp [hwt]
        rw [hd, hwt, sub_self, zero_pow (by have := (Fact.out : p.Prime).two_le; omega), sub_zero]
        simp [bv]
      · have hd : decide ((weightOn S x : ZMod p) = t) = false := by simp [hwt]
        rw [hd, ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hwt), sub_self]
        simp [bv]

/-- **Degree bound (PROVED): `reprP C` has total degree at most `reprDegP C`.** -/
theorem reprP_totalDegree_le (C : ACC0Circuit n) :
    (reprP p C).totalDegree ≤ reprDegP p C := by
  induction C with
  | const b => cases b <;> simp [reprP, reprDegP]
  | var i => simp [reprP, reprDegP, MvPolynomial.totalDegree_X]
  | not c ih =>
      simp only [reprP, reprDegP]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ih)
      rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _
  | and a b iha ihb =>
      simp only [reprP, reprDegP]
      exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add iha ihb)
  | or a b iha ihb =>
      simp only [reprP, reprDegP]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · exact le_trans (MvPolynomial.totalDegree_add _ _)
          (max_le (le_trans iha (Nat.le_add_right _ _)) (le_trans ihb (Nat.le_add_left _ _)))
      · exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add iha ihb)
  | mod q S t =>
      simp only [reprP, reprDegP]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _
      · refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
        have hsum : (∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p)) - C (ZMod.cast t)).totalDegree ≤ 1 := by
          refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
          · refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le (fun i _ => ?_))
            rw [MvPolynomial.totalDegree_X]
          · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
        calc (p - 1) * (∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p)) - C (ZMod.cast t)).totalDegree
            ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ hsum
          _ = p - 1 := Nat.mul_one _

/-!
**The AC⁰[p] recursive faithful representation, proved.**  Every `AC⁰[p]` circuit is *exactly* a polynomial over `F_p`
(`reprP_eval`) of degree `≤ reprDegP` (`reprP_totalDegree_le`).  This is the object the Razborov–Smolensky separation runs
on; the matching half (`MOD_q`, `q ≠ p`, has *no* such representation) is the lower bound's content, not a gap.  Remaining
(open, not faked): prime-power composition, large-fan-in approximation wiring, `composite_BT_degree`.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP.reprP_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP.reprP_totalDegree_le
