import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStepLabelDecode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath

/-!
# Håstad switching lemma — per-step label inverse (second label-decoder brick)

Building on the clause-position codec (`SwitchingStepLabelDecode`): this file proves the **per-step
soundness of the canonical position encoding**.  The encoder records, at a state `π`, the position of
the active literal within its active clause (`canonPos`); the decoder, *recomputing the active clause
from `π` itself* (`decodeActiveLit`), recovers the active literal exactly (`decodeActiveLit_canonPos`).

The point: at any genuine step state `π` the active clause `activeClause cs π` is a **pure function of
`π`** — so the decoder needs no circuit advice, only `π` and the `Fin w` position.  This is the part
of the Håstad decoder with *no* confound: when you have the step state, the position label recovers
the literal.  The confound is exactly what remains — recovering the per-step state (equivalently its
active clause) from the **end-state** `replayPath cs ρ s`, which `decodeActiveLit` cannot do on its
own and which this file does **not** fake.

## What is proved (clean axioms, no `sorry`)

* `canonPos` — the encoder: position of the active literal in its active clause (`0` if no step).
* `decodeActiveLit` — the decoder: recompute the active clause from `π`, then read the position.
* `decodeActiveLit_canonPos` — **per-step inverse**: at any `π` with an active literal,
  `decodeActiveLit cs π (canonPos cs π) = activeLit cs π`.
* `decodeActiveLit_canonPos_replayPath` — the inverse along the replay path, at each genuine step.

## Honest scope

This discharges the per-step encode→decode inverse *given the step state* (the no-confound half).
The end-state → step-state (active-clause) recovery — Håstad's active-clause identification under
mid-completion, the confound — is **not** done here and is **not** faked.  AC⁰/depth-3; collapse and
P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Encoder:** the position of the active literal within its active clause (the `Fin w` half of the
canonical step label); `0` when there is no active step. -/
def canonPos (cs : List (Clause n)) (π : Restriction n) : ℕ :=
  match activeClause cs π, activeLit cs π with
  | some C, some ℓ => posOfLit C ℓ
  | _, _ => 0

/-- **Decoder:** recompute the active clause from `π`, then read the literal at position `p`. -/
def decodeActiveLit (cs : List (Clause n)) (π : Restriction n) (p : ℕ) : Option (Rung4Literal n) :=
  (activeClause cs π).bind (fun C => litAtPos C p)

/-- **Per-step inverse.**  Wherever a step exists, decoding the canonical position (against the
active clause recomputed from `π`) recovers the active literal. -/
theorem decodeActiveLit_canonPos (cs : List (Clause n)) (π : Restriction n)
    (hl : (activeLit cs π).isSome) :
    decodeActiveLit cs π (canonPos cs π) = activeLit cs π := by
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨C, hC⟩ : ∃ C, activeClause cs π = some C := by
    cases hh : activeClause cs π with
    | none => unfold activeLit at hℓ; rw [hh] at hℓ; simp at hℓ
    | some C => exact ⟨C, rfl⟩
  have hpos : canonPos cs π = posOfLit C ℓ := by simp only [canonPos, hC, hℓ]
  rw [hℓ, decodeActiveLit, hC, Option.bind_some, hpos]
  exact litAtPos_posOfLit (activeLit_mem_clause hC hℓ)

/-- **The per-step inverse along the replay path.**  At each genuine step `k`, the canonical position
label recovers the step's active literal — the decoder using only the step state and the `Fin w`
position. -/
theorem decodeActiveLit_canonPos_replayPath (cs : List (Clause n)) (ρ : Restriction n) (k : ℕ)
    (hl : (activeLit cs (replayPath cs ρ k)).isSome) :
    decodeActiveLit cs (replayPath cs ρ k) (canonPos cs (replayPath cs ρ k))
      = activeLit cs (replayPath cs ρ k) :=
  decodeActiveLit_canonPos cs (replayPath cs ρ k) hl

/-!
**Per-step label inverse, proved.**  The position encoding is sound at every genuine step: with the
step state in hand, the `Fin w` position recovers the active literal (recomputing the active clause
from the state — no circuit advice, no confound).  The remaining core — recovering the per-step state
/ active clause from the **end-state** (the confound) — is **not** faked.  AC⁰/depth-3; collapse +
P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.decodeActiveLit_canonPos
