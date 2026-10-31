import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStepLabelDecode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath

/-!
# Håstad switching lemma — per-step inverse on the **term** selector (third label-decoder brick)

The clause-position codec (`litAtPos`/`posOfLit`, `SwitchingStepLabelDecode`) is selector-agnostic.
The per-step inverse (`SwitchingStepLabelInverse`) was stated for the *clause* selector
(`activeClause`/`activeLit`), but the actual counting machinery — `replaySel`, `replayPath`,
`decodeLoop_recover`, `replay_switching_count` — runs on the **term** selector `activeTermLit`
(`¬termFalsified ∧ has-free-literal`, guarded by no-term-satisfied), which is **different** from the
clause selector (`¬clauseSatisfied ∧ has-free-literal`).  This file ports the per-step inverse to the
term selector, so the codec composes with the count machinery.

* `canonTermPos` — the encoder: position of the active *term* literal within its active term.
* `decodeActiveTermLit` — the decoder: recompute the active term from `π`, read the position.
* `activeTermLit_mem_term` — the active term literal is a literal of its active term.
* `decodeActiveTermLit_canonTermPos` — **per-step inverse on the term selector**: at any `π` with an
  active term literal, decoding the canonical position recovers it.  This is the literal-recovery
  layer for `replaySel`/`replay_switching_count`, given the per-step state.

## Honest scope

This discharges the per-step encode→decode inverse on the term selector *given the step state* — the
literal-recovery layer for the actual count machinery.  The end-state → step-state (active-term)
recovery (the confound / Håstad active-clause identification under mid-completion) is **not** done
here and is **not** faked.  AC⁰/depth-3; collapse + P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Encoder (term selector):** position of the active term literal within its active term. -/
def canonTermPos (cs : List (Clause n)) (π : Restriction n) : ℕ :=
  match activeTerm cs π, activeTermLit cs π with
  | some T, some ℓ => posOfLit T ℓ
  | _, _ => 0

/-- **Decoder (term selector):** recompute the active term from `π`, then read position `p`. -/
def decodeActiveTermLit (cs : List (Clause n)) (π : Restriction n) (p : ℕ) :
    Option (Rung4Literal n) :=
  (activeTerm cs π).bind (fun T => litAtPos T p)

/-- **The active term literal is a literal of its active term.** -/
theorem activeTermLit_mem_term {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    {ℓ : Rung4Literal n} (hT : activeTerm cs σ = some T) (hℓ : activeTermLit cs σ = some ℓ) :
    ℓ ∈ T.lits := by
  unfold activeTermLit at hℓ
  rw [hT] at hℓ
  exact (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1

/-- **Per-step inverse on the term selector.**  Wherever a step exists, decoding the canonical
position (against the active term recomputed from `π`) recovers the active term literal — the
literal-recovery layer the count machinery (`replaySel`) consumes, given the step state. -/
theorem decodeActiveTermLit_canonTermPos (cs : List (Clause n)) (π : Restriction n)
    (hl : (activeTermLit cs π).isSome) :
    decodeActiveTermLit cs π (canonTermPos cs π) = activeTermLit cs π := by
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨T, hT⟩ : ∃ T, activeTerm cs π = some T := by
    cases hh : activeTerm cs π with
    | none => unfold activeTermLit at hℓ; rw [hh] at hℓ; simp at hℓ
    | some T => exact ⟨T, rfl⟩
  have hpos : canonTermPos cs π = posOfLit T ℓ := by simp only [canonTermPos, hT, hℓ]
  rw [hℓ, decodeActiveTermLit, hT, Option.bind_some, hpos]
  exact litAtPos_posOfLit (activeTermLit_mem_term hT hℓ)

/-- **The per-step inverse along the replay path**, at each genuine step. -/
theorem decodeActiveTermLit_canonTermPos_replayPath (cs : List (Clause n)) (ρ : Restriction n)
    (k : ℕ) (hl : (activeTermLit cs (replayPath cs ρ k)).isSome) :
    decodeActiveTermLit cs (replayPath cs ρ k) (canonTermPos cs (replayPath cs ρ k))
      = activeTermLit cs (replayPath cs ρ k) :=
  decodeActiveTermLit_canonTermPos cs (replayPath cs ρ k) hl

/-!
**Per-step inverse on the term selector, proved.**  The position encoding is sound at every genuine
step of the actual count process: with the step state in hand, the `Fin w` position recovers the
active term literal (recomputing the active term from the state — no circuit advice).  The remaining
core — recovering the per-step state / active term from the **end-state** (the confound) — is **not**
faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.decodeActiveTermLit_canonTermPos
