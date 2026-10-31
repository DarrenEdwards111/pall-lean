import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSatPath

/-!
# Håstad switching lemma — star-encoding recomputability anchor (scoping)

Scoping the **star-encoding** (Razborov's satisfy-side decoder, the canonical switching-lemma proof).
Its decoder advantage over the falsify route is that the satisfy process makes each active clause
**satisfied**, so processed clauses are recomputable from the end-state as *newly-satisfied* clauses.
This file proves that recomputability anchor:

  after a satisfy step, the active clause (`firstUnsat`) is satisfied  (`satStep_satisfies_active`).

This is the satisfy-side analogue of `replayStep_falsifies` and the structural basis of the star
decoder.

**Scoping finding (see `STAR_ENCODING_SCOPE.md`).**  The satisfy/deepest decoder already in the
codebase (`recoverStream_correct`) is, like the falsify decoder (`decodedSel_eq_replaySel`) and my
set-route (`replay_count_nothing_falsified_setroute`), **restricted to the ρ-falsifies-nothing
regime** (`hnf`).  So the star route does **not** break the confound; the general
ρ-falsifies-terms case (dead/ρ-falsified terms contributing spurious variables) is the irreducible
core across *all* routes.  Breaking it needs the probabilistic switching lemma proper (random ρ +
dead-term handling), not a deterministic decoder tweak.

## What is proved (clean axioms, no `sorry`)

* `satStep_satisfies_active` — after a satisfy step, the step's active clause is satisfied.

## Honest scope

A foundational recomputability anchor for the star decoder, plus the scoping finding that the star
route is also `hnf`-restricted.  The general-case (confound) decoder is **not** built or faked.
AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.  See `STAR_ENCODING_SCOPE.md`,
`DEPTH3_STATUS.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Star-encoding recomputability anchor.**  After a satisfy step, the step's active clause
(`firstUnsat`) is satisfied — so the decoder can recompute processed clauses as newly-satisfied. -/
theorem satStep_satisfies_active {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    {ℓ : Rung4Literal n} (hC : firstUnsat σ cs = some C) (hℓ : satStepLit cs σ = some ℓ) :
    clauseSatisfied (satStep cs σ) C = true := by
  have hℓmem : ℓ ∈ C.lits := by
    unfold satStepLit at hℓ
    rw [hC] at hℓ
    exact (List.mem_filter.mp (List.mem_of_mem_head? hℓ)).1
  rw [satStep, hℓ]
  exact clauseSatisfied_satFix σ C hℓmem

/-!
**Star-encoding anchor proved.**  The satisfy step satisfies its active clause — the recomputability
basis of Razborov's star decoder.  But (scoping finding) the star/satisfy decoder is `hnf`-restricted
like every other route, so the general ρ-falsifies-terms case (the confound) remains the irreducible
core; it is **not** faked.  AC⁰/depth-3; collapse + P≠NP untouched.
-/

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.satStep_satisfies_active
