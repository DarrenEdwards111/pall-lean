import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReadOnceId

/-!
# End-state decoder for the "ρ falsifies nothing" regime — `hdec`, discharged

The decoder loop (`decodeLoop_recover`) needs the *selected variable set* `replaySel cs ρ s`, not
the clause sequence.  The selected variables are exactly the coordinates carrying a **false literal**
at the end-state `replayPath cs ρ s` — and that set is recoverable from the end-state **alone**,
under the single hypothesis "ρ falsifies no term", with **no read-once assumption**.  This
supersedes the read-once identification: read-once was sufficient but unnecessary; the clean
condition is that `ρ` falsifies nothing (so every false literal at the end-state was fixed by the
*path*, not by `ρ`).

* `decodedSel cs π` — the variables carrying a false literal of a falsified clause at `π` (computed
  from `π` alone, no label);
* `decodedSel_eq_replaySel` — **the decoder is correct**: under "ρ falsifies nothing",
  `decodedSel cs (replayPath cs ρ s) = replaySel cs ρ s`.
  - `⊆`: a false literal's variable is path-fixed (not `ρ`-fixed, else `ρ` would falsify that
    clause), hence selected;
  - `⊇`: each step's active literal stays false to the end-state and lies in a falsified clause.
* `replay_count_nothing_falsified` — **`hdec` discharged unconditionally** on any bad set of
  `ρ`-falsify-nothing restrictions: `Bad.card ≤ Short.card · (2w)^s`, via `replay_switching_count`
  with the label-free decoder `D = decodedSel`.

This closes the `(2w)^s` switching count for the **ρ-falsifies-nothing regime** with *no* remaining
decoder hypothesis.  (The fully general bad set — where `ρ` may itself falsify clauses, so a false
literal at the end-state could be `ρ`-fixed and the label is needed to disambiguate — is the
remaining case; not faked.)
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- A false literal stays false along the whole path (one false literal monotonicity). -/
theorem litFalse_replayPath_of {cs : List (Clause n)} {σ : Restriction n} {ℓ : Rung4Literal n}
    (j : ℕ) (h : litFalse σ ℓ = true) : litFalse (replayPath cs σ j) ℓ = true := by
  induction j with
  | zero => exact h
  | succ j ih => rw [replayPath]; exact litFalse_replayStep ih

/-- The variables a decoder reads off the end-state: those carrying a false literal of a falsified
clause.  Computed from the restriction alone — no label. -/
def decodedSel (cs : List (Clause n)) (π : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ C ∈ cs, termFalsified π C = true ∧
    ∃ ℓ ∈ C.lits, litVar ℓ = v ∧ litFalse π ℓ = true)

/-- **The end-state decoder is correct.**  If `ρ` falsifies no term, the variables carrying a false
literal at the end-state are exactly the path-selected variables `replaySel cs ρ s`. -/
theorem decodedSel_eq_replaySel {cs : List (Clause n)} {ρ : Restriction n}
    (hnf : ∀ T ∈ cs, termFalsified ρ T = false) (s : ℕ) :
    decodedSel cs (replayPath cs ρ s) = replaySel cs ρ s := by
  ext v
  simp only [decodedSel, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨C, hC, _, ℓ, hℓC, hℓv, hℓf⟩
    -- ρ does not fix `v` (else `ℓ` would be false under ρ, falsifying C)
    have hρnone : ρ v = none := by
      by_contra hne
      obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hne
      have hstab : replayPath cs ρ s v = some b' := by
        have hh := replayPath_fixed_stable (cs := cs) (ρ := ρ) (v := v) (b := b') 0 s
        rw [show replayPath cs ρ 0 = ρ from rfl, Nat.zero_add] at hh
        exact hh hb'
      have heq : ρ (litVar ℓ) = replayPath cs ρ s (litVar ℓ) := by rw [hℓv, hb', hstab]
      have hfρ : litFalse ρ ℓ = true := by rw [litFalse_eq_of_litVar_val heq]; exact hℓf
      have hcf : termFalsified ρ C = true := by
        rw [termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓC, hfρ⟩
      rw [hnf C hC] at hcf; exact absurd hcf (by simp)
    -- so `v` is path-fixed, hence selected
    by_contra hnotin
    have heqo := replayPath_eq_outside cs ρ s hnotin
    rw [hρnone] at heqo
    have hnone : replayPath cs ρ s (litVar ℓ) = none := by rw [hℓv]; exact heqo
    exact litFalse_litVar_fixed hℓf hnone
  · intro hv
    obtain ⟨k, hk, ℓ, hℓ, hℓv⟩ := mem_replaySel s hv
    obtain ⟨T, hTactive, hℓT⟩ : ∃ T, activeTerm cs (replayPath cs ρ k) = some T ∧ ℓ ∈ T.lits := by
      unfold activeTermLit at hℓ
      cases hat : activeTerm cs (replayPath cs ρ k) with
      | none => rw [hat] at hℓ; simp at hℓ
      | some T =>
        rw [hat] at hℓ
        exact ⟨T, rfl, (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1⟩
    have hℓfalse : litFalse (replayPath cs ρ s) ℓ = true := by
      have h1 : litFalse (replayPath cs ρ (k + 1)) ℓ = true := by
        rw [replayPath, replayStep, hℓ]; simp [litFalse, falFix_forces_false]
      have h2 := litFalse_replayPath_of (cs := cs) (σ := replayPath cs ρ (k + 1)) (s - (k + 1)) h1
      rwa [replayPath_add, show (k + 1) + (s - (k + 1)) = s from by omega] at h2
    have hTf : termFalsified (replayPath cs ρ s) T = true := termFalsified_of_active_lit_mem hk hℓ hℓT
    exact ⟨T, activeTerm_mem hTactive, hTf, ℓ, hℓT, hℓv, hℓfalse⟩

/-- **`hdec` discharged, unconditionally, for the ρ-falsifies-nothing regime.**  Any bad set of
restrictions that each falsify no term satisfies the `(2w)^s` switching count, with the *label-free*
end-state decoder `decodedSel`. -/
theorem replay_count_nothing_falsified {w s : ℕ} {cs : List (Clause n)}
    (lab : Restriction n → PathLabel w s) {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, replayPath cs ρ s ∈ Short)
    (hbadnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, termFalsified ρ T = false) :
    Bad.card ≤ Short.card * (2 * w) ^ s :=
  replay_switching_count lab (fun π _ => decodedSel cs π) hmem
    (fun ρ hρ => decodedSel_eq_replaySel (hbadnf ρ hρ) s)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.decodedSel_eq_replaySel
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replay_count_nothing_falsified
