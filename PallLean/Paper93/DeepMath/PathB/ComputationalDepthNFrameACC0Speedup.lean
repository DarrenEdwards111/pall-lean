import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitModel

/-!
# The N-frame → ACC⁰-SAT speedup kernel (support-extraction form)

`nframe_williams_cashout` (`…WilliamsNEXP_ACC0`) reduces `NEXP ⊄ ACC⁰` to the bridge
`NFrameGivesACC0SatSpeedup → ACC0SatSpeedup`.  The boundary/action form of the speedup is in
`…NFrameSpeedupBridge` (a reachable‑set DP: `action < 2^n ⇒` beats brute force).  This file gives the
**ACC⁰‑specific structural kernel**: the support‑extraction collapse of the SAT search.

The kernel: a SAT search over the `2^n` cube collapses to a search over the **statistic the circuit factors
through**.  By support extraction (`…ACC0CircuitModel.eval_factors`) a depth‑2 `MOD`‑bottom circuit satisfies
`eval x = g (weightVec supports x)`, so

> `(∃ x, eval x = true) ↔ ∃ w ∈ image(weightVec), g w = true`

— satisfiability is decided by searching the **`weightVec` image** (the residue / cell vectors), not the cube.
The image is the cell space of the bottom support family; its size is the speedup parameter (`≤ 2^{#surviving}`
after a low‑survivor restriction, far below `2^{#live}`).  That collapse is the N‑frame's contribution to the SAT
speedup; turning it into a `2^{n - n^ε}` *time bound* (branching over killed coordinates with this fast base case)
is the named algorithmic gap.

## What is proved (clean axioms, no `sorry`)

* `sat_iff_image` — **the general reduction**: a predicate factoring through a statistic is satisfiable iff some
  achieved statistic value is accepted (search the image, not the domain).
* `sat_depth2_reduces` — **the N‑frame kernel**: a depth‑2 `MOD`‑bottom circuit's satisfiability reduces to a search
  over its `weightVec` image (via support extraction).

## Honest scope

This is the *structural* core of the N‑frame speedup — proved, powered by the corpus's support extraction and
cell/survivor analysis.  It is **not** the full `ACC0SatSpeedup`: converting the small‑image search into a
`2^{n - n^ε}` time bound needs the restriction‑tree branching over killed coordinates and a time model, neither
formalized here.  So `NFrameGivesACC0SatSpeedup` is *partially* discharged — its search‑space‑collapse half is
proved; the time accounting remains the named algorithmic ingredient (the genuine Williams content).  Nothing here
proves `NEXP ⊄ ACC⁰` outright, let alone `NP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup

open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel

variable {n k : ℕ}

/-- A Boolean function is satisfiable if some input accepts. -/
def Satisfiable (f : (Fin n → Bool) → Bool) : Prop := ∃ x, f x = true

/-- **The general SAT reduction (proved): search the statistic, not the domain.**  A predicate `g ∘ stat` is
satisfiable iff some *achieved* statistic value `s ∈ image(stat)` is accepted.  When `image(stat)` is far smaller
than the input space, this is a search‑space collapse. -/
theorem sat_iff_image {S : Type*} [DecidableEq S] (g : S → Bool) (stat : (Fin n → Bool) → S) :
    (∃ x, g (stat x) = true) ↔ ∃ s ∈ Finset.univ.image stat, g s = true := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨stat x, Finset.mem_image_of_mem stat (Finset.mem_univ x), hx⟩
  · rintro ⟨s, hs, hgs⟩
    obtain ⟨x, _, hxs⟩ := Finset.mem_image.mp hs
    exact ⟨x, by rw [hxs]; exact hgs⟩

/-- **The N‑frame speedup kernel (proved): depth‑2 `MOD`‑bottom SAT reduces to a `weightVec`‑image search.**  By
support extraction the circuit factors through `weightVec supports`, so its satisfiability is decided by searching
the (small) `weightVec` image — the residue / cell vectors — rather than the `2^n` cube.  This is the structural
speedup the N‑frame supplies; the time bound is the named remaining gap. -/
theorem sat_depth2_reduces (C : Depth2ModCircuit n k) :
    ∃ g : (Fin k → ℕ) → Bool,
      Satisfiable C.eval ↔ ∃ w ∈ Finset.univ.image (weightVec C.supports), g w = true := by
  obtain ⟨g, hg⟩ := eval_factors C
  refine ⟨g, ?_⟩
  have hsat : Satisfiable C.eval ↔ ∃ x, g (weightVec C.supports x) = true := by
    unfold Satisfiable
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hg]; exact hx⟩
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [hg]; exact hx⟩
  rw [hsat]
  exact sat_iff_image g (weightVec C.supports)

end PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup.sat_iff_image
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup.sat_depth2_reduces
