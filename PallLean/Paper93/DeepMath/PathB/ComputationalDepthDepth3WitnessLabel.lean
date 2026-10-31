import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActive

/-!
# Tight switching, step 24: the witness-augmented label, `F`-independent (branch `razborov-recoverRho-wip`)

Encoding the live-clause witness of step 23 into the label, keeping the count `F`-independent.  The
live-witness decoder (`decodedSel_filter_eq_replaySel`) recovers the path from the live sublist `cs'`; to
make that a true encoding the decoder must be *handed* the witness identifying the active clause at each
step.  The witness is one clause index per step (`Fin m`, `m` a bound on the clause count), recorded
alongside the `(Fin w × Bool)` path step.

So the augmented label is `WitLabel w s m := Fin s → (Fin w × Bool × Fin m)`, with

```
  |WitLabel w s m| = (2 · w · m)^s,
```

still **independent of the fuel `F`** — the `(Cw)^s` shape (here `C = m`, the clause-count bound), *not*
the crude `(4^w+1)^F`.  Feeding `(2wm)^s` into `card_bad_le_of_label_bound` gives the witness-augmented
switching count.

The per-step witness is the active clause's *index* `activeIdx cs σ = cs.findIdx (activePred σ)`; when a
clause is active (`activeClause cs σ = some C`) the index is in range and points back to it
(`activeIdx_lt`, `getElem_activeIdx`), so the decoder reconstructs the active clause — skipping dead ones —
from the witness alone.

* `WitLabel`, `card_witStepLabel`, `card_witLabels`, `card_witLabels_le` — the `F`-independent label space.
* `activeIdx`, `activeIdx_lt`, `getElem_activeIdx` — the active-clause-index witness and its recovery.

## Honest scope

This is the label space and the witness extraction/recovery; assembling the actual injection
`Bad → Short × WitLabel` (encode each bad `ρ` as its path label plus per-step active-clause index, decode via
step 23) and dropping `hnf` from the tight count is the next step.  The count stays `F`-independent — the
expander/Ramanujan selector is needed only if a constant-overhead witness (`m` independent of clause count)
is ever required.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- One augmented step: the path step `(Fin w × Bool)` plus the active-clause witness `Fin m`. -/
abbrev WitStepLabel (w m : ℕ) : Type := Fin w × Bool × Fin m

/-- A witness-augmented label of length `s`: a path step plus an active-clause index per step. -/
abbrev WitLabel (w s m : ℕ) : Type := Fin s → WitStepLabel w m

/-- Each augmented step has `2 · w · m` possibilities. -/
theorem card_witStepLabel (w m : ℕ) : Fintype.card (WitStepLabel w m) = 2 * w * m := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_fin]
  ring

/-- **The witness-augmented label count is `F`-independent:** `(2·w·m)^s`, the `(Cw)^s` shape with the
clause-count bound `m`, not the fuel-dependent `(4^w+1)^F`. -/
theorem card_witLabels (w s m : ℕ) : Fintype.card (WitLabel w s m) = (2 * w * m) ^ s := by
  rw [Fintype.card_fun, card_witStepLabel, Fintype.card_fin]

/-- The witness-label bound in the form the switching count consumes. -/
theorem card_witLabels_le (w s m : ℕ) : Fintype.card (WitLabel w s m) ≤ (2 * w * m) ^ s :=
  le_of_eq (card_witLabels w s m)

/-- The predicate selecting the active clause (unsatisfied, with a free literal). -/
def activePred (σ : Restriction n) (C : Clause n) : Bool :=
  !clauseSatisfied σ C && decide (0 < (freeLits σ C).length)

/-- The active clause's **index** — the per-step witness. -/
def activeIdx (cs : List (Clause n)) (σ : Restriction n) : ℕ :=
  cs.findIdx (activePred σ)

theorem activeClause_eq_find (cs : List (Clause n)) (σ : Restriction n) :
    activeClause cs σ = cs.find? (activePred σ) := rfl

/-- When a clause is active, the witness index is in range. -/
theorem activeIdx_lt {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (h : activeClause cs σ = some C) : activeIdx cs σ < cs.length := by
  rw [activeClause_eq_find] at h
  rw [activeIdx, List.findIdx_lt_length]
  exact ⟨C, List.mem_of_find?_eq_some h, List.find?_some h⟩

/-- The witness index points back to the active clause: the decoder recovers it. -/
theorem getElem_activeIdx {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (h : activeClause cs σ = some C) :
    cs[activeIdx cs σ]'(activeIdx_lt h) = C := by
  have h' := h
  rw [activeClause_eq_find, List.find?_eq_some_iff_getElem] at h'
  obtain ⟨hp, i, hi, hget, hmin⟩ := h'
  have hidx : activeIdx cs σ = i := by
    rw [activeIdx, List.findIdx_eq hi]
    refine ⟨hget ▸ hp, fun j hj => ?_⟩
    have := hmin j hj
    simpa using this
  have key : cs[activeIdx cs σ]? = some C := by
    rw [hidx, List.getElem?_eq_getElem hi, hget]
  rw [List.getElem?_eq_getElem (activeIdx_lt h), Option.some_inj] at key
  exact key

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_witLabels
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.getElem_activeIdx
