import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitReprP

/-!
# Brick (low-degree barrier) — the Razborov–Smolensky barrier from the AC⁰[p] representation (proved)

Turning the `AC⁰[p]` representation into the lower-bound direction.  Brick AC⁰[p] repr shows every `AC⁰[p]` circuit `C` is
*exactly* a polynomial `reprP C` over `F_p` of degree `≤ reprDegP C`.  Contrapositively, any Boolean function with **no**
low-degree `F_p` representation cannot be computed by a bounded-degree `AC⁰[p]` circuit — the Razborov–Smolensky low-degree
barrier, as a clean consequence of the representation.

To get a concrete separation `g ∉ AC⁰[p]` one feeds in the matching half — that `g` (e.g. `MOD_q`, `q ≠ p`) has no low-degree
`F_p` representation — which is the genuine RS lower bound (the tree's RS polynomial layer / `MOD_q ∉ AC⁰[p]` work), supplied
here as the hypothesis `hno`, *not* re-proved.

## What is proved (clean axioms, no `sorry`)

* **`acc0p_low_degree_repr`** (PROVED) — `ModpOnly p C → ∃ P, P.totalDegree ≤ reprDegP p C ∧ ∀ x, eval(bv∘x) P = bv(eval C x)`.
* **`not_acc0p_of_no_lowdeg_repr`** (PROVED) — if `f` has no degree-`≤D` `F_p` representation, then no `ModpOnly` `AC⁰[p]`
  circuit with `reprDegP ≤ D` computes `f`.

## Honest scope

This is the barrier *direction* (AC⁰[p] ⊆ low-degree, contrapositive).  It does **not** supply the not-low-degree witness for
any concrete `g` (the RS lower bound itself — `hno` is a hypothesis), handle `MOD_q`(`q≠p`)/prime-power gates inside the
circuit, nor the Williams cash-out.  General YBT and `NEXP ⊄ ACC⁰` remain open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeBarrier

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitRepr (bv)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprP reprDegP ModpOnly reprP_eval reprP_totalDegree_le)

variable {n p : ℕ} [Fact p.Prime]

/-- **AC⁰[p] is low-degree representable over `F_p` (PROVED).** -/
theorem acc0p_low_degree_repr (C : ACC0Circuit n) (h : ModpOnly p C) :
    ∃ P : MvPolynomial (Fin n) (ZMod p),
      P.totalDegree ≤ reprDegP p C ∧
      ∀ x : Fin n → Bool, eval (fun i => (bv (x i) : ZMod p)) P = bv (ACC0CircuitModel.eval C x) :=
  ⟨reprP p C, reprP_totalDegree_le C, fun x => reprP_eval C x h⟩

/-- **The Razborov–Smolensky low-degree barrier (PROVED): a function with no low-degree `F_p` representation escapes
bounded-degree `AC⁰[p]`.** -/
theorem not_acc0p_of_no_lowdeg_repr (f : (Fin n → Bool) → Bool) (D : ℕ)
    (hno : ¬ ∃ P : MvPolynomial (Fin n) (ZMod p),
        P.totalDegree ≤ D ∧ ∀ x, eval (fun i => (bv (x i) : ZMod p)) P = bv (f x)) :
    ¬ ∃ C : ACC0Circuit n, ModpOnly p C ∧ reprDegP p C ≤ D ∧ ACC0CircuitModel.eval C = f := by
  rintro ⟨C, hmod, hdeg, hf⟩
  refine hno ⟨reprP p C, le_trans (reprP_totalDegree_le C) hdeg, fun x => ?_⟩
  rw [reprP_eval C x hmod, hf]

/-!
**The low-degree barrier, proved.**  `AC⁰[p]` is low-degree over `F_p` (`acc0p_low_degree_repr`), so any function lacking a
low-degree `F_p` representation is not a bounded-degree `AC⁰[p]` circuit (`not_acc0p_of_no_lowdeg_repr`) — the RS barrier as a
consequence of the representation.  Feeding in the not-low-degree witness for a concrete `g` (the RS lower bound) yields `g ∉
AC⁰[p]`.  Remaining (open, not faked): that witness, `MOD_q`/prime-power gates, the Williams cash-out.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeBarrier.acc0p_low_degree_repr
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0LowDegreeBarrier.not_acc0p_of_no_lowdeg_repr
