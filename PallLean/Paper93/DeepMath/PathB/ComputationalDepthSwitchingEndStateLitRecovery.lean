import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingTermLabelInverse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReadOnceId

/-!
# Håstad switching lemma — end-state literal recovery modulo term-recovery (fourth label-decoder brick)

Wiring brick 3 (`decodeActiveTermLit_canonTermPos`) against the count machinery (`replaySel`,
`mem_replaySel`).  The per-step inverse decodes the active literal *given the step state*; here we
push it to the **end-state**: assuming a term-recovery oracle `recT` that recovers each step's active
term from the end-state `replayPath cs ρ s` (the confound, the lone remaining primitive), the
canonical position label recovers each step's active literal — and hence every selected variable —
from the end-state alone.

* `decode_from_endstate` — given `recT (end-state) k = activeTerm cs (step-k state)`, the canonical
  position decodes the step-`k` active literal from the end-state.
* `decode_from_endstate_var` — the same at the variable level.
* `replaySel_recovered` — **decoder completeness modulo the oracle**: every selected variable
  `v ∈ replaySel cs ρ s` is recovered from the end-state and labels (via `recT`) at some step `k < s`.

So the `(2w)^s` switching count reduces — at the literal/variable level — to the single primitive
`recT`: recover each step's active term from the end-state.  That primitive **is** the confound and is
**not** discharged or faked here.

## Honest scope

This discharges the literal/variable-recovery layer of `hdec` modulo the active-term-recovery oracle
(the confound).  Building the full `Finset` decoder `D` and the soundness direction (decoded ⊆
selected) to invoke `replay_switching_count` is the next assembly; the confound itself remains.
AC⁰/depth-3; collapse + P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **End-state literal recovery modulo term-recovery.**  If the oracle recovers the step-`k` active
term from the end-state, the canonical position label recovers the step-`k` active literal. -/
theorem decode_from_endstate {cs : List (Clause n)} {ρ : Restriction n} {s k : ℕ}
    (hact : (activeTermLit cs (replayPath cs ρ k)).isSome)
    {recT : Restriction n → ℕ → Option (Clause n)}
    (hrec : recT (replayPath cs ρ s) k = activeTerm cs (replayPath cs ρ k)) :
    (recT (replayPath cs ρ s) k).bind
        (fun T => litAtPos T (canonTermPos cs (replayPath cs ρ k)))
      = activeTermLit cs (replayPath cs ρ k) := by
  rw [hrec]
  exact decodeActiveTermLit_canonTermPos cs (replayPath cs ρ k) hact

/-- The variable-level end-state recovery. -/
theorem decode_from_endstate_var {cs : List (Clause n)} {ρ : Restriction n} {s k : ℕ}
    (hact : (activeTermLit cs (replayPath cs ρ k)).isSome)
    {recT : Restriction n → ℕ → Option (Clause n)}
    (hrec : recT (replayPath cs ρ s) k = activeTerm cs (replayPath cs ρ k)) :
    ((recT (replayPath cs ρ s) k).bind
        (fun T => litAtPos T (canonTermPos cs (replayPath cs ρ k)))).map litVar
      = (activeTermLit cs (replayPath cs ρ k)).map litVar := by
  rw [decode_from_endstate hact hrec]

/-- **Decoder completeness modulo the term-recovery oracle.**  Every selected variable is recovered
from the end-state and the canonical labels at some step. -/
theorem replaySel_recovered {cs : List (Clause n)} {ρ : Restriction n} {s : ℕ}
    {recT : Restriction n → ℕ → Option (Clause n)}
    (hact : ∀ k, k < s → (activeTermLit cs (replayPath cs ρ k)).isSome)
    (hrec : ∀ k, k < s → recT (replayPath cs ρ s) k = activeTerm cs (replayPath cs ρ k))
    {v : Fin n} (hv : v ∈ replaySel cs ρ s) :
    ∃ k, k < s ∧
      ((recT (replayPath cs ρ s) k).bind
        (fun T => litAtPos T (canonTermPos cs (replayPath cs ρ k)))).map litVar = some v := by
  obtain ⟨k, hk, ℓ, hℓ, hℓv⟩ := mem_replaySel s hv
  refine ⟨k, hk, ?_⟩
  rw [decode_from_endstate (hact k hk) (hrec k hk), hℓ]
  simp [hℓv]

/-!
**End-state literal/variable recovery modulo the oracle, proved.**  The literal-recovery layer of the
Håstad decoder is now pushed to the end-state: modulo the single term-recovery oracle `recT` (the
confound), the canonical `(2w)^s` labels recover every selected variable from the end-state.  The
remaining core — `recT` itself (recover each step's active term from the end-state) — is **not**
faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replaySel_recovered
