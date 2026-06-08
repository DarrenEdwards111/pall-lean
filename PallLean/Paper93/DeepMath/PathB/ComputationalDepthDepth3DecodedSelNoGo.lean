import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingEndStateDecoder
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FilterFalsified

/-!
# Tight switching, step 9: the decoder-side invariance is FALSE (the empty-skip wall) (branch `razborov-recoverRho-wip`)

The honest no-go that blocks the `hnf`-free reconstruction via filter-transfer.  Bricks 112–113 showed the
*tree/leaf/path/set* side of the alive condition is filter-invariant.  The remaining piece — the *decoder*
side — would need `decodedSel cs π = decodedSel (cs.filter live) π`.  **This is false.**

`decodedSel cs π` reads off the variables carrying a *false literal of a π-falsified clause*; the live
filter `cs.filter (¬ termFalsified ρ ·)` *removes* the ρ-falsified clauses.  A ρ-falsified clause (absent in
`cs'`) still contributes its fixed-false variable to `decodedSel cs π` (since `π ⊇ ρ` also falsifies it).
So `decodedSel cs π` over-counts relative to `decodedSel cs' π` exactly the spurious variables of ρ-dead
clauses — which the decoder, given only the leaf `π`, **cannot** tell apart from genuine path variables.

* `decodedSel_not_filter_invariant` — a witness (`cs = [{x_{v₀}}]`, `ρ ≡ false`) with
  `decodedSel cs ρ ≠ decodedSel (cs.filter live) ρ`.

## Consequence (honest)

This is the empty-skip wall in its sharpest form: the deepest-branch forward-scan reconstruction
*genuinely* requires `hnf` (no ρ-falsified clause), and cannot be made `hnf`-free by transferring through
the live filter.  So the tight `(2w)^s` count via this reconstruction bounds only the *alive* deep
restrictions; covering all deep ρ would need a *different*, disambiguating tight encoding (a tightened
`descentSat`/`codesList` that records the dead clauses, not the forward scan).  The crude `(4^w+1)^F`
route's encoding does disambiguate (works for all ρ); the tight forward-scan route does not.  This pins the
irreducible content precisely; it is **not** faked.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The decoder-side invariance fails.**  `decodedSel` is *not* invariant under the ρ-live filter:
a ρ-falsified clause contributes a spurious variable that the filter removes. -/
theorem decodedSel_not_filter_invariant (v₀ : Fin n) :
    ∃ (cs : List (Clause n)) (ρ : Restriction n),
      decodedSel cs ρ
        ≠ decodedSel (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) ρ := by
  refine ⟨[(⟨[Rung4Literal.pos v₀]⟩ : Clause n)], fun _ => some false, ?_⟩
  have hfals : SwitchingCounting.termFalsified (fun _ : Fin n => (some false : Option Bool))
      (⟨[Rung4Literal.pos v₀]⟩ : Clause n) = true := by
    simp [SwitchingCounting.termFalsified, SwitchingCounting.litFalse, litFixedVal]
  have hmem : v₀ ∈ decodedSel [(⟨[Rung4Literal.pos v₀]⟩ : Clause n)]
      (fun _ : Fin n => (some false : Option Bool)) := by
    simp only [decodedSel, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨[Rung4Literal.pos v₀]⟩, List.mem_singleton.mpr rfl, hfals,
      Rung4Literal.pos v₀, List.mem_singleton.mpr rfl, rfl, by
        simp [SwitchingCounting.litFalse, litFixedVal]⟩
  intro hcontra
  rw [hcontra] at hmem
  have hfilter : ([(⟨[Rung4Literal.pos v₀]⟩ : Clause n)]).filter
      (fun T => !SwitchingCounting.termFalsified (fun _ : Fin n => (some false : Option Bool)) T)
      = [] := by simp [hfals]
  rw [hfilter] at hmem
  simp [decodedSel] at hmem

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.decodedSel_not_filter_invariant
