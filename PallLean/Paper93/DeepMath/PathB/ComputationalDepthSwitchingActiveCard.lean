import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActivePath

/-!
# The selected-set fold: per-step characterization + cardinality budget

**STATUS: REAL.  THE MEASURE-SIDE BRICKS FOR THE TIGHT COUNT (DECODER SPEC).**

`actSel cs σ k` is the set of coordinates the faithful path fixes in its first `k`
steps.  These lemmas pin down its structure — exactly what the canonical decoder
must invert:

* `actSel_succ_some` / `actSel_succ_none`: one step adds the active literal's
  variable (or nothing, once the path stalls) — so `actSel` is the union over steps
  of the per-step selected variable;
* `actSel_card_le`: at most one coordinate is added per step, so
  `(actSel cs σ k).card ≤ k`.

The cardinality bound is the star-budget the tight count consumes (`Short` =
restrictions with `≥ s` more fixed coordinates).  The remaining hard core —
recovering the *set itself* from the shortened restriction plus a `(2w)^s`-bounded
label (Håstad's canonical decoding, the active-clause traversal inverted) — is the
`hrec` hypothesis of `card_bad_le_pathlabel`, not reducible to a smaller lemma.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- One step where the path is still active adds exactly the active literal's
variable to the selected set. -/
theorem actSel_succ_some {cs : List (Clause n)} {σ : Restriction n} {k : ℕ}
    {ℓ : Rung4Literal n} (h : activeLit cs (actPath cs σ k) = some ℓ) :
    actSel cs σ (k + 1) = insert (litVar ℓ) (actSel cs σ k) := by
  rw [actSel, h]
  ext x
  simp [Finset.mem_insert, or_comm]

/-- One step where the path has stalled (no active literal) adds nothing. -/
theorem actSel_succ_none {cs : List (Clause n)} {σ : Restriction n} {k : ℕ}
    (h : activeLit cs (actPath cs σ k) = none) :
    actSel cs σ (k + 1) = actSel cs σ k := by
  rw [actSel, h]
  simp

/-- **Star budget.**  At most one coordinate is fixed per step, so the selected set
after `k` steps has at most `k` elements. -/
theorem actSel_card_le (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    (actSel cs σ k).card ≤ k := by
  induction k with
  | zero => simp [actSel]
  | succ k ih =>
    cases h : activeLit cs (actPath cs σ k) with
    | none => rw [actSel_succ_none h]; omega
    | some ℓ =>
      rw [actSel_succ_some h]
      exact le_trans (Finset.card_insert_le _ _) (by omega)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.actSel_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.actSel_succ_some
