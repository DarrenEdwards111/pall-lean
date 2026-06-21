import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityWitness
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0LowDegreeBarrier

/-!
# Brick (parity barrier) — `MOD_2 ∉` bounded-degree `AC⁰[p]` for odd `p` (proved)

The concrete separation-flavoured statement: the Boolean parity function `MOD_2` (odd-weight indicator) is **not** computed by
any `AC⁰[p]` circuit of bounded degree (`reprDegP ≤ D < n`), for odd `p`.  This packages the explicit sign witness (Brick
parity witness) into the low-degree barrier (Brick low-degree barrier) via the affine identity `signWt = (−1)^{weight} = 1 −
2·parity`: a low-degree representation of parity would give one of `signWt` (degree preserved under the affine transform),
contradicting `signWt_no_lowdeg_repr`.

This is the genuine in-framework Razborov–Smolensky separation for `q = 2`: `AC⁰[p]` is exactly low-degree over `F_p` (Brick
AC⁰[p] repr), while `MOD_2` is not (this brick) — so `MOD_2 ∉` bounded-degree `AC⁰[p]`.

## What is proved (clean axioms, no `sorry`)

* **`parityFn`** — the Boolean `MOD_2` function (odd Hamming weight).
* **`signWt_eq_pow`**, **`signWt_affine`** (PROVED) — `signWt = (−1)^{weight} = 1 − 2·(bv∘parityFn)`.
* **`parityFn_no_lowdeg`** (PROVED) — `MOD_2` has no degree-`≤D` `F_p` representation (`p≠2`, `D<n`).
* **`parityFn_not_acc0p`** (PROVED) — `¬∃ C, ModpOnly p C ∧ reprDegP p C ≤ D ∧ eval C = MOD_2` — `MOD_2 ∉` bounded-degree `AC⁰[p]`.

## Honest scope

The `q = 2` Razborov–Smolensky separation against *bounded-degree* `AC⁰[p]`.  It does **not** cover general `MOD_q` (`q > 2`),
relate `reprDegP ≤ D` to actual circuit depth/size (so it is "bounded representation degree", not yet "constant depth, any
size" — that needs the depth→degree blow-up bound), nor the Williams cash-out.  General YBT and `NEXP ⊄ ACC⁰` remain open.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprP reprDegP ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness (signWt hsign signWt_sq signWt_no_lowdeg_repr)
open PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeBarrier (not_acc0p_of_no_lowdeg_repr)

variable {n p : ℕ} [Fact p.Prime]

/-- The Hamming weight of a Boolean input. -/
def wt (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i => x i = true)).card

/-- The Boolean `MOD_2` (parity) function: odd Hamming weight. -/
def parityFn {n : ℕ} (x : Fin n → Bool) : Bool := decide (Odd (wt x))

/-- **`signWt = (−1)^{weight}` (PROVED).** -/
theorem signWt_eq_pow (x : Fin n → Bool) : signWt p x = (-1 : ZMod p) ^ (wt x) := by
  unfold signWt hsign wt
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]

/-- **`signWt = 1 − 2·(bv∘parityFn)` (PROVED).** -/
theorem signWt_affine (x : Fin n → Bool) :
    signWt p x = 1 - 2 * (bv (parityFn x) : ZMod p) := by
  have hbv : (bv (parityFn x) : ZMod p) = if Odd (wt x) then 1 else 0 := by
    simp [bv, parityFn]
  rw [signWt_eq_pow, hbv]
  by_cases ho : Odd (wt x)
  · rw [Odd.neg_one_pow ho, if_pos ho]; ring
  · rw [Even.neg_one_pow (Nat.not_odd_iff_even.mp ho), if_neg ho]; ring

/-- **`MOD_2` has no low-degree `F_p` representation (PROVED).** -/
theorem parityFn_no_lowdeg (hp2 : p ≠ 2) {D : ℕ} (hn : D < n) :
    ¬ ∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = bv (parityFn x) := by
  rintro ⟨P, hdeg, hP⟩
  refine signWt_no_lowdeg_repr hp2 hn ⟨C 1 - C 2 * P, ?_, ?_⟩
  · refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      rw [MvPolynomial.totalDegree_C, zero_add]; exact hdeg
  · intro x
    rw [map_sub, map_mul, eval_C, eval_C, hP x]
    exact (signWt_affine x).symm

/-- **`MOD_2 ∉` bounded-degree `AC⁰[p]` for odd `p` (PROVED).** -/
theorem parityFn_not_acc0p (hp2 : p ≠ 2) {D : ℕ} (hn : D < n) :
    ¬ ∃ C : ACC0Circuit n,
        ModpOnly p C ∧ reprDegP p C ≤ D ∧ ACC0CircuitModel.eval C = parityFn :=
  not_acc0p_of_no_lowdeg_repr parityFn D (parityFn_no_lowdeg hp2 hn)

/-!
**The `q = 2` separation, proved.**  `MOD_2 ∉` bounded-degree `AC⁰[p]` for odd `p` — the two RS halves (`AC⁰[p]` is
low-degree; `MOD_2` is not) assembled into a concrete in-framework separation.  Remaining (open, not faked): general `MOD_q`
(`q>2`), the `reprDegP ≤ D` → constant-depth/any-size strengthening, and the Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier.parityFn_not_acc0p
