import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ActiveTermIdx

/-!
# Tight switching, step 27: the free-literal position witness (branch `razborov-recoverRho-wip`)

The second half of the per-step witness recovery.  Brick 66 recovers the active *term* from its index;
this recovers the selected *literal* from its position within that term.  The deepest branch selects
`litVar ℓ` where `ℓ = (freeLits σ T).head?` is the first free literal of the active term `T`.  Since
`freeLits σ T = T.lits.filter (litFree σ)`, the head of the filter is `T.lits.find? (litFree σ)`
(`List.head?_filter`), so the same `findIdx`/`find?` recovery as bricks 64/66 gives the position
`freeLitPos σ T = T.lits.findIdx (litFree σ)` and `T.lits[freeLitPos σ T] = ℓ`.

Composing with brick 66 (`cs[activeTermIdx cs σ] = T`): the selected variable is
`litVar (cs[activeTermIdx cs σ].lits[freeLitPos σ T])` — fully recovered from the `(clause-index,
position)` witness, with **no scan and no `hnf`**.  This is the per-step correctness core of the
witnessed decoder.

* `freeLitPos`, `freeLitPos_lt`, `getElem_freeLitPos` — the position witness and its recovery.

## Honest scope

With bricks 66 + 67 the per-step witness fully recovers the selected variable, `hnf`-free.  Assembling the
recursive deepest-branch encode (the witness sequence, its length `= depth`, the `Fin w`/`Fin m` bounds, the
conversion to `WitLabel`, and the `decode ∘ encode = deepestSel` induction) into the
`WitnessReconstructionCorrect` instance — and thereby discharging `deepest_count_of_witness` — is the final
recursive glue.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The position of the active term's first free literal within its literal list — the per-step
position witness (resolves the `Fin w` index of the path step). -/
def freeLitPos (σ : Restriction n) (T : Clause n) : ℕ :=
  T.lits.findIdx (litFree σ)

theorem freeLits_head?_eq_find (σ : Restriction n) (T : Clause n) :
    (freeLits σ T).head? = T.lits.find? (litFree σ) := by
  rw [freeLits, List.head?_filter]

/-- When the active term has a free literal, the position witness is in range. -/
theorem freeLitPos_lt {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (h : (freeLits σ T).head? = some ℓ) : freeLitPos σ T < T.lits.length := by
  have h' : T.lits.find? (litFree σ) = some ℓ := by rw [← freeLits_head?_eq_find]; exact h
  rw [freeLitPos, List.findIdx_lt_length]
  exact ⟨ℓ, List.mem_of_find?_eq_some h', List.find?_some h'⟩

/-- The position witness points back to the selected literal: `T.lits[freeLitPos σ T] = ℓ`. -/
theorem getElem_freeLitPos {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (h : (freeLits σ T).head? = some ℓ) :
    T.lits[freeLitPos σ T]'(freeLitPos_lt h) = ℓ := by
  have h' : T.lits.find? (litFree σ) = some ℓ := by rw [← freeLits_head?_eq_find]; exact h
  rw [List.find?_eq_some_iff_getElem] at h'
  obtain ⟨hp, i, hi, hget, hmin⟩ := h'
  have hidx : freeLitPos σ T = i := by
    rw [freeLitPos, List.findIdx_eq hi]
    refine ⟨hget ▸ hp, fun j hj => ?_⟩
    have := hmin j hj
    simpa using this
  have key : T.lits[freeLitPos σ T]? = some ℓ := by
    rw [hidx, List.getElem?_eq_getElem hi, hget]
  rw [List.getElem?_eq_getElem (freeLitPos_lt h), Option.some_inj] at key
  exact key

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.getElem_freeLitPos
