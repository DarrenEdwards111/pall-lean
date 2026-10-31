import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CharWitness
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityBarrier
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthDegreeBound

/-!
# Brick (MOD_q indicator) — the Boolean `MOD_q` indicator vs low degree (proved, conditional)

The Boolean `MOD_q` indicator `modqFn q x = [q ∣ weight(x)]`.  The general principle `no_lowdeg_of_Dsign_ne` says: any
function `f` with nonzero sign-functional `Dsign f = ∑ₓ signWt(x)·f(x)` has no degree-`<n` `F_p` representation (since `Dsign`
kills low-degree).  Applied to `modqFn`, this gives `MOD_q ∉` (bounded-degree, then constant-depth) `AC⁰[p]` **whenever**
`Dsign(MOD_q) ≠ 0` — the genuine top-coefficient condition.

Honest note: unlike parity (`q=2`), `Dsign(MOD_q) = (1/q)∑ⱼ(1−ζ^j)^n` can *vanish* for some `n` (the unconditional `q>2` lower
bound is the harder Razborov–Smolensky rank argument).  So the witness here is *conditional* on `Dsign(MOD_q) ≠ 0`, which is a
real number-theoretic condition (e.g. it holds at `n=1`, where `MOD_q = ¬`).

## What is proved (clean axioms, no `sorry`)

* **`no_lowdeg_of_Dsign_ne`** (PROVED) — `Dsign f ≠ 0 → D<n → ¬∃ P, P.totalDegree ≤ D ∧ ∀ x, eval(bv∘x) P = f x`.
* **`modqFn_no_lowdeg`** (PROVED) — `Dsign(bv∘MOD_q) ≠ 0 → D<n → MOD_q` has no degree-`≤D` rep.
* **`modq_not_acc0p_depth`** (PROVED) — `Dsign(bv∘MOD_q) ≠ 0, (p−1)·2^d < n → MOD_q ∉` depth-`d` `AC⁰[p]`.

## Honest scope

The Boolean `MOD_q` witness/separation, **conditional** on `Dsign(MOD_q) ≠ 0`.  The unconditional `q>2` bound (for all large
`n`) is the full RS rank argument (tree's `Layer4`), *not* proved here.  Williams cash-out still open.  Nothing here is `NEXP ⊄
ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness

open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprDegP ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityWitness (signWt)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (wt)
open PallLean.Paper93.DeepMath.PathB.ACC0CharWitness (Dsign_eval_zero)
open PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeBarrier (not_acc0p_of_no_lowdeg_repr)
open PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound (reprDegP_le_depth)

variable {n p : ℕ} [Fact p.Prime]

/-- The Boolean `MOD_q` indicator: `q` divides the Hamming weight. -/
def modqFn (q : ℕ) {n : ℕ} (x : Fin n → Bool) : Bool := decide (q ∣ wt x)

/-- **The sign-functional detects non-low-degree (PROVED).** -/
theorem no_lowdeg_of_Dsign_ne (hp2 : p ≠ 2) (f : (Fin n → Bool) → ZMod p)
    (hf : (∑ x : Fin n → Bool, signWt p x * f x) ≠ 0) {D : ℕ} (hn : D < n) :
    ¬ ∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = f x := by
  rintro ⟨P, hdeg, hP⟩
  refine hf ?_
  rw [show (∑ x, signWt p x * f x)
        = ∑ x, signWt p x * eval (fun i => (bv (x i) : ZMod p)) P from
      Finset.sum_congr rfl (fun x _ => by rw [hP x])]
  exact Dsign_eval_zero hp2 P hdeg hn

/-- **The Boolean `MOD_q` indicator has no low-degree rep when `Dsign(MOD_q) ≠ 0` (PROVED).** -/
theorem modqFn_no_lowdeg (hp2 : p ≠ 2) (q : ℕ)
    (hq : (∑ x : Fin n → Bool, signWt p x * (bv (modqFn q x) : ZMod p)) ≠ 0) {D : ℕ} (hn : D < n) :
    ¬ ∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = bv (modqFn q x) :=
  no_lowdeg_of_Dsign_ne hp2 (fun x => bv (modqFn q x)) hq hn

/-- **`MOD_q ∉` constant-depth `AC⁰[p]` when `Dsign(MOD_q) ≠ 0` (PROVED).** -/
theorem modq_not_acc0p_depth (hp2 : p ≠ 2) (q : ℕ)
    (hq : (∑ x : Fin n → Bool, signWt p x * (bv (modqFn q x) : ZMod p)) ≠ 0) {d : ℕ}
    (hd : (p - 1) * 2 ^ d < n) :
    ¬ ∃ C : ACC0Circuit n, ModpOnly p C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = modqFn q := by
  rintro ⟨C, hmod, hdep, hev⟩
  have hbound : reprDegP p C ≤ (p - 1) * 2 ^ d :=
    le_trans (reprDegP_le_depth C) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hdep))
  exact not_acc0p_of_no_lowdeg_repr (modqFn q) (reprDegP p C)
    (modqFn_no_lowdeg hp2 q hq (lt_of_le_of_lt hbound hd)) ⟨C, hmod, le_refl _, hev⟩

/-!
**The Boolean `MOD_q` indicator, handled conditionally.**  `MOD_q ∉` constant-depth `AC⁰[p]` whenever `Dsign(MOD_q) ≠ 0` —
the genuine top-coefficient condition (always true for `q=2`; for `q>2` it holds for many `n` but can fail, where the
unconditional bound needs the RS rank argument).  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness.no_lowdeg_of_Dsign_ne
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqWitness.modq_not_acc0p_depth
