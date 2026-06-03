import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder

/-!
# The general bad set: what the label must disambiguate

The general `(2w)^s` labeled switching count is **already proved** in the *clause-block* route:
`SwitchingCounting.canonMarkLabel_switching_count` (label `canonMarkLabel`, decoder `encLits_decode`,
injectivity `canonMarkLabel_det` + `termWalk_inj'`) holds for arbitrary `ρ` — no "falsifies nothing"
restriction — modulo the structural side conditions (`hcs`, `hwidth`) and the bad-set conditions
(`hne`, `hlen`, `hmem`).

This file pins down, for the *replay* route, **exactly** what the label has to do in the general
case (where the end-state decoder `decodedSel` over-counts), so the picture is precise rather than
opaque:

* `replaySel_subset_decodedSel` — **unconditionally**, every path-selected variable carries a false
  literal at the end-state, so `replaySel cs ρ s ⊆ decodedSel cs (replayPath cs ρ s)`.  The
  label-free decoder never *misses* a path variable.
* `decodedSel_extra_rho_fixed` — **the over-count is exactly the `ρ`-fixed false literals**: a
  `decodedSel` variable that is *not* path-selected has `ρ v ≠ none` (it was falsified by `ρ`
  itself, not by the path).

So in general `decodedSel = replaySel ⊎ {ρ-fixed false-literal variables}`, and the label's sole job
is to drop that `ρ`-fixed surplus.  When `ρ` falsifies nothing the surplus is empty and the label is
unnecessary (`decodedSel_eq_replaySel`); the surplus is precisely the case the clause-block route's
`canonMarkLabel` label handles via the canonical satisfying-completion structure.  No incorrect
replay-route decoder is asserted for the general case — the proved general count is the clause-block
one.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Unconditional ⊇.**  Every path-selected variable carries a false literal of a falsified clause
at the end-state — the end-state decoder never misses a path variable (no "ρ falsifies nothing"
needed). -/
theorem replaySel_subset_decodedSel (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    replaySel cs ρ s ⊆ decodedSel cs (replayPath cs ρ s) := by
  intro v hv
  simp only [decodedSel, Finset.mem_filter, Finset.mem_univ, true_and]
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

/-- **The over-count is exactly the `ρ`-fixed false literals.**  A variable that the end-state
decoder picks up but that is *not* path-selected was fixed by `ρ` itself.  This is precisely the
surplus the label must drop in the general case. -/
theorem decodedSel_extra_rho_fixed (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) {v : Fin n}
    (hv : v ∈ decodedSel cs (replayPath cs ρ s)) (hnotsel : v ∉ replaySel cs ρ s) :
    ρ v ≠ none := by
  simp only [decodedSel, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨C, _, _, ℓ, _, hℓv, hℓf⟩ := hv
  have hfix : replayPath cs ρ s (litVar ℓ) ≠ none := litFalse_litVar_fixed hℓf
  have heqo := replayPath_eq_outside cs ρ s hnotsel
  rw [hℓv, heqo] at hfix
  exact hfix

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.replaySel_subset_decodedSel
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.decodedSel_extra_rho_fixed
