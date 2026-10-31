import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityGeneralDBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityGeneralDDischarge

/-!
# Block-DT model, route-2 step [168]: general-`d` block bound, `hround` discharged (option (b))

The block twin of `parity_not_altO_hround_discharged`.  The per-round survivor `hround` of
`parity_not_altO_block` [167] is discharged trivially (`survivor_round_trivial`, needs only `n ≤ F`,
since the per-round collapse `collapseRound` is `EquivOn` unconditionally and needs no switching).
What remains is the single terminal switching `hterm`, now over the block tree `canonicalDTree` — the
exact shape the m-free route-2 terminal `terminal_shallow_of_survivor_findep` [165] discharges per
bottom `DNF`.

* `parity_not_altO_block_hround_discharged` — `AltO (d+2) C₀` ⟹ `∃ x, eval C₀ x ≠ parity x`, with only
  the block terminal `hterm` remaining as an input.

This isolates the *entire* remaining m-ful-vs-m-free content of the depth-`d` lower bound into one
block-level terminal hypothesis.  Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **General-`d` block bound, `hround` discharged.**  Only the block terminal switching `hterm`
remains (dischargeable per bottom `DNF` by `terminal_shallow_of_survivor_findep` [165], m-free).  The
per-round survivor is supplied for free by `survivor_round_trivial`. -/
theorem parity_not_altO_block_hround_discharged (s w F d : ℕ) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hF : n ≤ F) (hC₀ : AltO (d + 2) C₀)
    (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hterm : ∀ (cs : List (Clause n)) (σ : Fin n → Option Bool), s ≤ SwitchingCounting.stars σ →
      ∃ σ' : Fin n → Option Bool, Extends σ σ' ∧ SwitchingCounting.stars σ' < F ∧
        (canonicalDTree cs w F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x :=
  parity_not_altO_block s w F d C₀ τ₀ hC₀ hτ₀ (survivor_round_trivial hF s) hterm

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block_hround_discharged
