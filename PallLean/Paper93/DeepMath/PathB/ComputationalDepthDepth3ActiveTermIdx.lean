import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad

/-!
# Tight switching, step 26: the active-*term* witness index (branch `razborov-recoverRho-wip`)

The witness index for the **deepest-path** machinery.  Brick 64's `activeIdx` is for `activeClause`
(predicate `¬clauseSatisfied ∧ has-free-lit`); but the tight count's deepest branch (`deepestSel`,
`deepestEnd`) descends via `activeTerm` (predicate `¬termFalsified ∧ has-free-lit`).  So the witness encode
for `deepestSel` needs an `activeTerm`-indexed witness, built here in parallel to brick 64.

When `anyTermSat` is false (which holds all along the active descent) `activeTerm = cs.find? (termActivePred)`
(`activeTerm_eq_find`), so the same `List.findIdx`/`find?` recovery applies: the index is in range
(`activeTermIdx_lt`) and points back to the active term (`getElem_activeTermIdx`).  This is exactly the
per-step clause-witness the deepest-branch encode records, recovered by the decoder with no scanning and no
`hnf`.

* `termActivePred`, `activeTermIdx` — the deepest-path active-term predicate and its index.
* `activeTermIdx_lt`, `getElem_activeTermIdx` — the witness is in range and recovers the active term.

## Honest scope

This is the `activeTerm` analogue of brick 64, completing the witness-extraction ingredient for the
deepest-path (`deepestSel`) encode.  Assembling the full `WitnessReconstructionCorrect` instance (per-step
position + this index along the deepest branch, with the satisfy-step handling) remains the last mile.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The deepest-path active-term predicate: unfalsified, with a free literal. -/
def termActivePred (σ : Restriction n) (T : Clause n) : Bool :=
  !termFalsified σ T && decide (0 < (freeLits σ T).length)

/-- The active term's **index** — the deepest-path per-step witness. -/
def activeTermIdx (cs : List (Clause n)) (σ : Restriction n) : ℕ :=
  cs.findIdx (termActivePred σ)

/-- When a term is active, it is the `find?` of `termActivePred`. -/
theorem activeTerm_eq_findPred {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) : cs.find? (termActivePred σ) = some T :=
  (activeTerm_eq_find (activeTerm_anyTermSat_false h)).symm.trans h

/-- When a term is active, the witness index is in range. -/
theorem activeTermIdx_lt {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) : activeTermIdx cs σ < cs.length := by
  have hf := activeTerm_eq_findPred h
  rw [activeTermIdx, List.findIdx_lt_length]
  exact ⟨T, List.mem_of_find?_eq_some hf, List.find?_some hf⟩

/-- The witness index points back to the active term: the decoder recovers it with no scan, no `hnf`. -/
theorem getElem_activeTermIdx {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    (h : activeTerm cs σ = some T) :
    cs[activeTermIdx cs σ]'(activeTermIdx_lt h) = T := by
  have hf := activeTerm_eq_findPred h
  rw [List.find?_eq_some_iff_getElem] at hf
  obtain ⟨hp, i, hi, hget, hmin⟩ := hf
  have hidx : activeTermIdx cs σ = i := by
    rw [activeTermIdx, List.findIdx_eq hi]
    refine ⟨hget ▸ hp, fun j hj => ?_⟩
    have := hmin j hj
    simpa using this
  have key : cs[activeTermIdx cs σ]? = some T := by
    rw [hidx, List.getElem?_eq_getElem hi, hget]
  rw [List.getElem?_eq_getElem (activeTermIdx_lt h), Option.some_inj] at key
  exact key

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.getElem_activeTermIdx
