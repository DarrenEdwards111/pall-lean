import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameFpDegree

/-!
# The AND/OR approximate-degree gate recurrence over `F_p`

`NFrameFpDegree` proved the MOD_p gate has exact `F_p`-degree `≤ p - 1`.  The other `AC⁰[p]` gates — unbounded
fan-in AND/OR — have *exact* multilinear degree equal to their fan-in (AND `= ∏ zᵢ`), so exact degree is
useless for them.  The Razborov–Smolensky fix is the **probabilistic polynomial**: an OR/AND gate is computed by
a single linear form raised to the `(p-1)`, `(Σᵢ wᵢ zᵢ)^{p-1}`, whose degree is `p - 1` **independent of the
fan-in** (Fermat: `s^{p-1} = [s ≠ 0]`, so the power detects "some input nonzero" = OR).

This file formalises the **gate recurrence** that this yields: composing an OR (or AND) gate over child
polynomials of degree `≤ d` gives a polynomial of degree `≤ (p-1)·d`, and it computes the gate correctly on any
input where the linear form does not vanish.

## Results

* `zmod_pow_eq` — `s^{p-1} = if s = 0 then 0 else 1` over `F_p` (the Fermat detector).
* `orComp` / `orComp_totalDegree_le` / `orComp_eval_eq` — the **OR gate recurrence**: `((Σᵢ C(wᵢ)·Pᵢ)^{p-1})`
  has degree `≤ (p-1)·d` when each `Pᵢ` has degree `≤ d`, and evaluates to `OR` of the child values wherever the
  form is nonzero.  Degree grows by a factor `≤ p-1` per gate — **independent of fan-in**.
* `andComp` / `andComp_totalDegree_le` / `andComp_eval_eq` — the **AND gate recurrence** (dual, via the "some
  input is `0`" form `Σᵢ wᵢ(1 - Pᵢ)`).
* `exists_good_weight_or` — for every input there is a weight vector making the form nonzero, so per input the
  OR gate is computed at degree `≤ (p-1)·d`.

Together with `NFrameFpDegree.modp_low_degree_representation` (MOD_p, degree `≤ p-1`), every `AC⁰[p]` gate
multiplies the degree by a factor `≤ p - 1`, so a depth-`d` circuit has degree `≤ (p-1)^d` — quasi-polynomial
for constant depth.  This is the ACC-upper side of the degree dynamic-SPDP, for a single prime `p`.

## What remains — the wall

The correctness here is **conditional on the linear form not vanishing**; making it hold on a `1 - p^{-t}`
fraction of inputs (the actual approximation) needs the averaging/amplification over `t` random weight vectors
(the repo's `approximable_exists`).  And this whole degree method works only for a *single prime* `p`: composite
/ mixed `MOD_m` has no low-degree representation over any single field ("Wall 1"), the genuine ACC⁰ obstruction,
untouched here.

## Honest scope

The exact `F_p` gate recurrence for AND/OR (degree `× (p-1)` per gate, fan-in-independent) with per-input
correctness — the Razborov–Smolensky polynomial step.  No approximation error bound, no composite-MOD lower
bound, no ACC⁰ lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.NFrameFpDegree

section
variable (p : Nat) [Fact p.Prime]

theorem p_sub_one_ne_zero : p - 1 ≠ 0 := by
  have := Nat.Prime.two_le (Fact.out : p.Prime); omega

/-- **The Fermat detector.**  Over `F_p`, `s^{p-1}` is `0` if `s = 0` and `1` otherwise. -/
theorem zmod_pow_eq (s : ZMod p) : s ^ (p - 1) = if s = 0 then 0 else 1 := by
  by_cases h : s = 0
  · rw [if_pos h, h, zero_pow (p_sub_one_ne_zero p)]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one h]

/-- Complement of a bit under the `F_p` embedding. -/
theorem boolToZMod_not (b : Bool) : (1 : ZMod p) - boolToZMod p b = boolToZMod p (!b) := by
  cases b <;> simp [boolToZMod]

/-! ## OR gate -/

/-- OR of a Boolean vector. -/
def ORb {k : Nat} (b : Fin k → Bool) : Bool := decide (∃ i, b i = true)

theorem forall_false_of_ORb_false {k : Nat} (b : Fin k → Bool) (h : ORb b = false) :
    ∀ i, b i = false := by
  intro i
  cases hb : b i
  · rfl
  · exfalso
    have : ORb b = true := by simp only [ORb, decide_eq_true_eq]; exact ⟨i, hb⟩
    rw [this] at h
    exact Bool.noConfusion h

/-- The OR-composed polynomial: `(Σᵢ C(wᵢ)·Pᵢ)^{p-1}`. -/
noncomputable def orComp {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  (∑ i, C (w i) * Pi i) ^ (p - 1)

/-- **OR gate degree recurrence.**  If each child has degree `≤ d`, the OR composition has degree `≤ (p-1)·d`. -/
theorem orComp_totalDegree_le {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) (d : Nat) (hd : ∀ i, (Pi i).totalDegree ≤ d) :
    (orComp p Pi w).totalDegree ≤ (p - 1) * d := by
  rw [orComp]
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  have hs : (∑ i, C (w i) * Pi i).totalDegree ≤ d := by
    refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
    intro i _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hd i
  exact Nat.mul_le_mul (le_refl _) hs

/-- Evaluation of the OR composition: the child values enter through a single linear form. -/
theorem orComp_eval {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) (v : Fin n → ZMod p) :
    eval v (orComp p Pi w) = (∑ i, w i * eval v (Pi i)) ^ (p - 1) := by
  simp only [orComp, map_pow, map_sum, map_mul, MvPolynomial.eval_C]

/-- **OR gate correctness.**  If the children evaluate to Boolean values `bᵢ` at `v` and the linear form is
nonzero whenever some `bᵢ` is `true`, then the OR composition evaluates to `OR b`. -/
theorem orComp_eval_eq {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) (v : Fin n → ZMod p) (b : Fin k → Bool)
    (hbool : ∀ i, eval v (Pi i) = boolToZMod p (b i))
    (hgood : ORb b = true → (∑ i, w i * boolToZMod p (b i)) ≠ 0) :
    eval v (orComp p Pi w) = boolToZMod p (ORb b) := by
  rw [orComp_eval]
  simp only [hbool]
  rw [zmod_pow_eq]
  by_cases hor : ORb b = true
  · rw [if_neg (hgood hor), hor]; simp [boolToZMod]
  · have hbf : ORb b = false := by
      cases h : ORb b
      · rfl
      · exact absurd h hor
    have hsum0 : (∑ i, w i * boolToZMod p (b i)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [forall_false_of_ORb_false b hbf i]
      simp [boolToZMod]
    rw [if_pos hsum0, hbf]
    simp [boolToZMod]

/-- **Fan-in independence, per input.**  For every input there is a weight vector making the OR gate correct at
degree `≤ (p-1)·d` — the degree does not grow with the fan-in `k`. -/
theorem exists_good_weight_or {k : Nat} (b : Fin k → Bool) :
    ∃ w : Fin k → ZMod p, (ORb b = true → (∑ i, w i * boolToZMod p (b i)) ≠ 0) := by
  by_cases hor : ORb b = true
  · obtain ⟨j, hj⟩ : ∃ i, b i = true := by simpa only [ORb, decide_eq_true_eq] using hor
    refine ⟨fun i => if i = j then 1 else 0, fun _ => ?_⟩
    have : (∑ i, (if i = j then (1 : ZMod p) else 0) * boolToZMod p (b i))
        = boolToZMod p (b j) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [hij]
      · intro hj'; exact absurd (Finset.mem_univ j) hj'
    rw [this, hj, boolToZMod]
    simp
  · exact ⟨fun _ => 0, fun h => absurd h hor⟩

/-! ## AND gate (dual) -/

/-- AND of a Boolean vector. -/
def ANDb {k : Nat} (b : Fin k → Bool) : Bool := decide (∀ i, b i = true)

/-- The AND-composed polynomial: `1 - (Σᵢ C(wᵢ)·(1 - Pᵢ))^{p-1}` (the power detects "some input is `0`"). -/
noncomputable def andComp {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  1 - (∑ i, C (w i) * (1 - Pi i)) ^ (p - 1)

/-- **AND gate degree recurrence.**  Degree `≤ (p-1)·d`, dual to OR. -/
theorem andComp_totalDegree_le {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) (d : Nat) (hd : ∀ i, (Pi i).totalDegree ≤ d) :
    (andComp p Pi w).totalDegree ≤ (p - 1) * d := by
  rw [andComp]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  have hs : (∑ i, C (w i) * (1 - Pi i)).totalDegree ≤ d := by
    refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
    intro i _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact le_trans (MvPolynomial.totalDegree_sub _ _)
      (max_le (by rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _) (hd i))
  exact Nat.mul_le_mul (le_refl _) hs

theorem andComp_eval {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) (v : Fin n → ZMod p) :
    eval v (andComp p Pi w) = 1 - (∑ i, w i * (1 - eval v (Pi i))) ^ (p - 1) := by
  simp only [andComp, map_sub, map_one, map_pow, map_sum, map_mul, MvPolynomial.eval_C]

theorem not_ANDb_iff {k : Nat} (b : Fin k → Bool) : ANDb b = false ↔ ∃ i, b i = false := by
  simp only [ANDb, decide_eq_false_iff_not, not_forall, Bool.not_eq_true]

/-- **AND gate correctness.**  If the children evaluate to Boolean values `bᵢ` and the "some input is `0`"
form is nonzero whenever some `bᵢ` is `false`, the AND composition evaluates to `AND b`. -/
theorem andComp_eval_eq {n k : Nat} (Pi : Fin k → MvPolynomial (Fin n) (ZMod p))
    (w : Fin k → ZMod p) (v : Fin n → ZMod p) (b : Fin k → Bool)
    (hbool : ∀ i, eval v (Pi i) = boolToZMod p (b i))
    (hgood : ANDb b = false → (∑ i, w i * (1 - boolToZMod p (b i))) ≠ 0) :
    eval v (andComp p Pi w) = boolToZMod p (ANDb b) := by
  rw [andComp_eval]
  simp only [hbool]
  rw [zmod_pow_eq]
  by_cases hand : ANDb b = true
  · have hall : ∀ i, b i = true := by
      simpa only [ANDb, decide_eq_true_eq] using hand
    have hsum0 : (∑ i, w i * (1 - boolToZMod p (b i))) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [hall i]
      simp [boolToZMod]
    rw [if_pos hsum0, hand, sub_zero]
    simp [boolToZMod]
  · have hbf : ANDb b = false := by
      cases h : ANDb b
      · rfl
      · exact absurd h hand
    obtain ⟨j, hj⟩ := (not_ANDb_iff b).mp hbf
    rw [if_neg (hgood hbf), hbf]
    simp [boolToZMod]

end

end PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR.orComp_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR.orComp_eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR.andComp_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR.andComp_eval_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR.exists_good_weight_or
