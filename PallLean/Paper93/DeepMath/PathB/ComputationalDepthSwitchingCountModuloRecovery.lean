import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateLitRecovery

/-!
# Håstad switching lemma — the `(2w)^s` count modulo term-recovery (fifth label-decoder brick)

The capstone of the label-decoder reduction.  Combining the codec (brick 1), the per-step inverse on
the term selector (brick 3), and the end-state recovery (brick 4) with `replay_switching_count`, this
discharges the full `(2w)^s` switching count **modulo a single primitive**: a term-recovery oracle
`recT` that recovers each step's active term from the end-state.

  `Bad.card ≤ Short.card · (2w)^s`,  given  `recT (end-state) k = activeTerm cs (step-k state)`.

This is the finest honest isolation of the confound: the canonical `Fin w` position labels, decoded
against `recT`, reconstruct exactly the selected set `replaySel`, so the entire count goes through
**iff** `recT` exists.  `recT` itself is Håstad's active-clause identification under mid-completion —
the genuine research core — and is **not** discharged or faked here.

## What is proved (clean axioms, no `sorry`)

* `mem_replaySel_of` — the reverse membership for `replaySel` (soundness direction).
* `canonTermPos_lt` — the canonical position fits `Fin w` (`< w`), given `0 < w` and width `≤ w`.
* `replaySel_eq_biUnion` — `replaySel cs ρ s` as the per-step union of selected-variable singletons.
* `replay_count_modulo_termRecovery` — **the `(2w)^s` count modulo the term-recovery oracle.**

## Honest scope

This reduces the `(2w)^s` switching count to the single oracle `recT` (recover each step's active
term from the end-state) — the confound, **not** faked.  AC⁰/depth-3; `Depth3CollapseModel.collapse`
and P≠NP untouched.  See `DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The per-step selected-variable set of a literal option. -/
def stepSet (o : Option (Rung4Literal n)) : Finset (Fin n) :=
  match o with
  | none => ∅
  | some ℓ => {litVar ℓ}

/-- **Reverse membership for `replaySel` (soundness direction).**  A variable that is some step's
active-literal variable is selected. -/
theorem mem_replaySel_of {cs : List (Clause n)} {ρ : Restriction n} {v : Fin n} :
    ∀ s, (∃ k, k < s ∧ ∃ ℓ, activeTermLit cs (replayPath cs ρ k) = some ℓ ∧ litVar ℓ = v) →
      v ∈ replaySel cs ρ s := by
  intro s
  induction s with
  | zero => rintro ⟨k, hk, _⟩; omega
  | succ s ih =>
    rintro ⟨k, hk, ℓ, hℓ, hℓv⟩
    rw [replaySel, Finset.mem_union]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · exact Or.inl (ih ⟨k, hlt, ℓ, hℓ, hℓv⟩)
    · subst heq
      refine Or.inr ?_
      rw [hℓ]
      exact Finset.mem_singleton.mpr hℓv.symm

/-- **The canonical position fits in `Fin w`.** -/
theorem canonTermPos_lt {w : ℕ} {cs : List (Clause n)} {π : Restriction n}
    (hw : 0 < w) (hcw : ∀ T ∈ cs, T.width ≤ w) : canonTermPos cs π < w := by
  unfold canonTermPos
  split
  · next T ℓ hT hℓ =>
      exact lt_of_lt_of_le (posOfLit_lt_width (activeTermLit_mem_term hT hℓ)) (hcw T (activeTerm_mem hT))
  · next => exact hw

/-- **`replaySel` as a per-step union of selected-variable singletons.** -/
theorem replaySel_eq_biUnion (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    replaySel cs ρ s =
      (Finset.univ : Finset (Fin s)).biUnion
        (fun k => stepSet (activeTermLit cs (replayPath cs ρ k.val))) := by
  ext v
  rw [Finset.mem_biUnion]
  constructor
  · intro hv
    obtain ⟨k, hk, ℓ, hℓ, hℓv⟩ := mem_replaySel s hv
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, by rw [hℓ]; exact Finset.mem_singleton.mpr hℓv.symm⟩
  · rintro ⟨k, _, hv⟩
    cases hℓ : activeTermLit cs (replayPath cs ρ k.val) with
    | none => rw [hℓ] at hv; simp [stepSet] at hv
    | some ℓ =>
      rw [hℓ] at hv
      simp only [stepSet, Finset.mem_singleton] at hv
      exact mem_replaySel_of s ⟨k.val, k.isLt, ℓ, hℓ, hv.symm⟩

/-- **The `(2w)^s` switching count modulo the term-recovery oracle.**  If `recT` recovers each step's
active term from the end-state (the confound), the canonical `Fin w` position labels reconstruct the
selected set and the count goes through. -/
theorem replay_count_modulo_termRecovery {w s : ℕ} {cs : List (Clause n)}
    (hw : 0 < w) (hcw : ∀ T ∈ cs, T.width ≤ w)
    (recT : Restriction n → ℕ → Option (Clause n))
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, replayPath cs ρ s ∈ Short)
    (hrec : ∀ ρ ∈ Bad, ∀ k, k < s →
      recT (replayPath cs ρ s) k = activeTerm cs (replayPath cs ρ k))
    (hact : ∀ ρ ∈ Bad, ∀ k, k < s → (activeTermLit cs (replayPath cs ρ k)).isSome) :
    Bad.card ≤ Short.card * (2 * w) ^ s := by
  refine replay_switching_count
    (fun ρ k => (⟨canonTermPos cs (replayPath cs ρ k.val), canonTermPos_lt hw hcw⟩, false))
    (fun π label => (Finset.univ : Finset (Fin s)).biUnion
      (fun k => stepSet ((recT π k.val).bind (fun T => litAtPos T (label k).1.val))))
    hmem ?_
  intro ρ hρ
  rw [replaySel_eq_biUnion]
  refine Finset.biUnion_congr rfl (fun k _ => ?_)
  congr 1
  exact decode_from_endstate (hact ρ hρ k.val k.isLt) (hrec ρ hρ k.val k.isLt)

/-!
**`(2w)^s` count modulo term-recovery, proved.**  The label decoder is fully assembled: the canonical
`(2w)^s` position labels, decoded against the oracle `recT`, reconstruct `replaySel` exactly, so the
switching count holds modulo `recT` alone.  `recT` — recover each step's active term from the
end-state (Håstad's active-clause identification under mid-completion, the confound) — is **not**
faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_count_modulo_termRecovery
