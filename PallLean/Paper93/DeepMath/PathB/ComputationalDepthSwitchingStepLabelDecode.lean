import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActive

/-!
# Håstad switching lemma — the clause-position literal codec (first brick of the label decoder)

The `(2w)^s` switching count reduces (via `replay_switching_count`) to a decoder `D` recovering the
selected set from the end-state and a **position label** `PathLabel w s = Fin s → Fin w × Bool`.
`decodeLoop_recover` proves the decoder works given the active-literal *list*; `SwitchingDecoder`'s
docstring flags the conversion from a `Fin w` position back to the literal — **via the active clause**
— as the part *not* discharged.  `SwitchingEndStateDecoder.replay_count_nothing_falsified` then
discharges `hdec` *label-free* for the **ρ-falsifies-nothing** regime, leaving the general case
(where a false literal at the end-state may be `ρ`-fixed, so the label is needed to disambiguate) as
the open core.

This file builds the **position↔literal codec for the active clause** — the conversion that was left
open — and proves it recovers the active literal exactly, *given the active clause*.  This is the
local half of the label decoder: the `Fin w` position of a step is `posOfLit C ℓ` (`< C.width`), and
`litAtPos` recovers `ℓ` from it.  What remains (honestly isolated) is identifying the active clause
`C` from the end-state under mid-completion (Håstad's active-clause identification / the confound).

## What is proved (clean axioms, no `sorry`)

* `litAtPos` / `posOfLit` — the decoder (position → literal) and encoder (literal → position).
* `litAtPos_posOfLit` — round-trip: `ℓ ∈ C.lits → litAtPos C (posOfLit C ℓ) = some ℓ`.
* `posOfLit_lt_width` — the position fits: `ℓ ∈ C.lits → posOfLit C ℓ < C.width`.
* `activeLit_mem_clause` — the active literal is a literal of its active clause.
* `litAtPos_active` — **the codec recovers the active literal from its active clause**, with the
  position `< C.width` (so it injects into `Fin w` for `w ≥ width`).

## Honest scope

This discharges the position↔literal conversion (the `Fin w` half of `PathStepLabel`) *given* the
active clause.  The active-clause identification from the end-state (the confound / Håstad core) is
**not** done here and is **not** faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP
untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Decoder (position → literal):** the literal at position `p` of clause `C` (the `Fin w` half of
a `PathStepLabel` resolves here, against the active clause). -/
def litAtPos (C : Clause n) (p : ℕ) : Option (Rung4Literal n) := C.lits[p]?

/-- **Encoder (literal → position):** the position of literal `ℓ` within clause `C`. -/
def posOfLit (C : Clause n) (ℓ : Rung4Literal n) : ℕ := C.lits.idxOf ℓ

/-- **Codec round-trip:** decoding the encoded position of a clause literal recovers it. -/
theorem litAtPos_posOfLit {C : Clause n} {ℓ : Rung4Literal n} (h : ℓ ∈ C.lits) :
    litAtPos C (posOfLit C ℓ) = some ℓ := by
  rw [litAtPos, posOfLit, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h),
    List.getElem_idxOf]

/-- **The encoded position fits in the clause width** (so it injects into `Fin w` for `w ≥ width`). -/
theorem posOfLit_lt_width {C : Clause n} {ℓ : Rung4Literal n} (h : ℓ ∈ C.lits) :
    posOfLit C ℓ < C.width := List.idxOf_lt_length_of_mem h

/-- **The active literal is a literal of its active clause.** -/
theorem activeLit_mem_clause {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    {ℓ : Rung4Literal n} (hC : activeClause cs σ = some C) (hℓ : activeLit cs σ = some ℓ) :
    ℓ ∈ C.lits := by
  unfold activeLit at hℓ
  rw [hC] at hℓ
  exact (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1

/-- **The clause-position codec recovers the active literal from its active clause.**  The step's
`Fin w` position is `posOfLit C ℓ` (`< C.width`), and `litAtPos` recovers `ℓ` — the local half of the
Håstad label decoder, given the active clause `C`. -/
theorem litAtPos_active {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    {ℓ : Rung4Literal n} (hC : activeClause cs σ = some C) (hℓ : activeLit cs σ = some ℓ) :
    litAtPos C (posOfLit C ℓ) = some ℓ ∧ posOfLit C ℓ < C.width :=
  ⟨litAtPos_posOfLit (activeLit_mem_clause hC hℓ),
   posOfLit_lt_width (activeLit_mem_clause hC hℓ)⟩

/-!
**First Håstad label-decoder brick, proved.**  The position↔literal codec (`Fin w` half of
`PathStepLabel`) is discharged: given the active clause `C`, the step's `Fin w` position recovers the
active literal exactly (`litAtPos_active`).  This is the conversion `SwitchingDecoder` left open.  The
remaining core — identifying the active clause `C` from the end-state under mid-completion (the
confound) — is **not** faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.litAtPos_active
