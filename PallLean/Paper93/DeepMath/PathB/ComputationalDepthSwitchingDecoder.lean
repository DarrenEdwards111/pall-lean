import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReplayPath

/-!
# The per-step active-term decoder (hdec), assembled

`SwitchingCounting.replay_switching_count` reduces the `(2w)^s` switching count to a single
hypothesis `hdec`: a decoder `D` recovering the selected set `replaySel cs ρ s` from the end-state
`replayPath cs ρ s` and a `(2w)^s` label.  Its difficulty is **active-clause identification under
mid-completion**.  This file builds the part of `hdec` that *is* provable — the **decoder recovery
loop** — and isolates with full precision the part that is not.

* `freeOn_replayPath_succ_recover` — **the per-step decoder.**  Given the active literal `ℓ` of
  step `k`, re-freeing `litVar ℓ` from the step-`k+1` state recovers the step-`k` state:
  `freeOn (replayPath cs ρ (k+1)) {litVar ℓ} = replayPath cs ρ k`.  A direct lift of the proved
  single-step inverse `freeOn_replayStep_recover` to the path.

* `decodeLoop` / `decodeLoop_recover` — **the assembled decoder loop.**  Folding `freeOn` over the
  reversed sequence of active literals (the "advice") recovers *both* the original restriction `ρ`
  and the selected set `replaySel cs ρ s`, exactly, from the end-state `replayPath cs ρ s`.  Proved
  by induction, each step discharged by the per-step decoder.

So the decoder *loop* is correct: **given the `s` active literals, the recovery is exact.**

**The remaining open core (not faked).**  `decodeLoop_recover` consumes the active-literal *list*
(`s` literals over `n` variables).  For the `(2w)^s` count, that advice must instead be a
`PathLabel w s = Fin s → Fin w × Bool` — each literal encoded as a *position within its active
clause* (`≤ w`) plus a bit, **not** as a free index over `n`.  Converting a position back to the
actual literal requires identifying the active clause at each step purely from the end-state — the
Håstad active-clause identification, the genuine research core flagged in `replay_switching_count`'s
`hdec`.  This file proves everything downstream of that single conversion; the conversion itself is
**not** discharged here and is **not** faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **The per-step active-term decoder.**  Re-freeing the step's active variable from the next
state recovers the current state. -/
theorem freeOn_replayPath_succ_recover {cs : List (Clause n)} {ρ : Restriction n} {k : ℕ}
    {ℓ : Rung4Literal n} (h : activeTermLit cs (replayPath cs ρ k) = some ℓ) :
    freeOn (replayPath cs ρ (k + 1)) {litVar ℓ} = replayPath cs ρ k := by
  rw [replayPath]
  exact freeOn_replayStep_recover h

/-- The decoder loop: fold `freeOn` over an advice list of active literals (most-recent first). -/
def decodeLoop : List (Rung4Literal n) → Restriction n → Restriction n
  | [], π => π
  | ℓ :: rest, π => decodeLoop rest (freeOn π {litVar ℓ})

/-- **The assembled decoder loop is correct.**  If the canonical falsify-process runs `s` steps
(an active literal at each step), there is an advice list of `s` literals such that the decoder loop
recovers the original restriction `ρ` from the end-state `replayPath cs ρ s`, and the variables of
the advice are exactly the selected set `replaySel cs ρ s`.  Each step is discharged by the per-step
decoder `freeOn_replayPath_succ_recover`. -/
theorem decodeLoop_recover (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ s : ℕ, (∀ k, k < s → (activeTermLit cs (replayPath cs ρ k)).isSome) →
      ∃ advice : List (Rung4Literal n), advice.length = s ∧
        decodeLoop advice (replayPath cs ρ s) = ρ ∧
        (advice.map litVar).toFinset = replaySel cs ρ s := by
  intro s
  induction s with
  | zero =>
    intro _
    exact ⟨[], rfl, rfl, by simp [replaySel]⟩
  | succ s ih =>
    intro hrun
    obtain ⟨rest, hlen, hrec, hsel⟩ := ih (fun k hk => hrun k (by omega))
    have hsome := hrun s (by omega)
    cases hℓ : activeTermLit cs (replayPath cs ρ s) with
    | none => rw [hℓ] at hsome; simp at hsome
    | some ℓ =>
      refine ⟨ℓ :: rest, by simp [hlen], ?_, ?_⟩
      · rw [decodeLoop, freeOn_replayPath_succ_recover hℓ]
        exact hrec
      · rw [List.map_cons, List.toFinset_cons, replaySel, hℓ, ← hsel]
        ext v
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
        tauto

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_replayPath_succ_recover
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.decodeLoop_recover
