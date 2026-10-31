import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingLocality

/-!
# Left-side locality: the mirror foundation for the splice

The palindrome fooling needs a **splice** — the mixed input `u·0…·u'ᴿ` matches `x_u` on the left and
`x_{u'}` on the right — which requires *left*-side determinism alongside the right-side determinism
already built.  This file lays the left-side step foundation, exactly mirroring `CrossingLocality`
with the region `≤ b` in place of `> b`.

* `step_local_left` — two configurations sharing state and head `h ≤ b` and agreeing on all cells
  `≤ b` still share state and head and agree on `≤ b` after one step.  (While the head is `≤ b`, the
  step reads and writes only cells `≤ b`.)
* `step_left_frozen` — if the head is at `> b`, one step leaves every cell `≤ b` unchanged.

## Scope (honest)

This is only the *step-level* left foundation.  The full left-determinism needs the run-level,
chaining, cycle, and recursive layers mirrored (as on the right), and then the fooling needs the
genuinely new **three-way splice** induction (comparing the mixed computation against two references,
matching the left one on left excursions and the right one on right excursions), the concrete
palindrome family, and the summation over `Ω(n)` cuts.  Those remain; this file does **not** claim the
`Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* result (`crossingCount ≤ time` caps
the technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Locality (left excursion).**  Two configurations sharing state and head `h ≤ b` and agreeing on
all cells `≤ b` still share state and head and agree on `≤ b` after one step. -/
theorem step_local_left (M : Machine) (b : ℕ) (c₁ c₂ : Cfg M)
    (hst : c₁.st = c₂.st) (hhd : c₁.hd = c₂.hd) (hhb : c₁.hd ≤ b)
    (hagree : ∀ p, p ≤ b → c₁.tp.getD p false = c₂.tp.getD p false) :
    (step M c₁).st = (step M c₂).st ∧ (step M c₁).hd = (step M c₂).hd ∧
      (∀ p, p ≤ b → (step M c₁).tp.getD p false = (step M c₂).tp.getD p false) := by
  have hread : c₁.tp.getD c₁.hd false = c₂.tp.getD c₂.hd false := by
    rw [hhd]; exact hagree c₂.hd (by rw [← hhd]; exact hhb)
  by_cases hh : M.halt c₁.st = true
  · have hh2 : M.halt c₂.st = true := by rw [← hst]; exact hh
    rw [step_of_halted M hh, step_of_halted M hh2]
    exact ⟨hst, hhd, hagree⟩
  · have hh1 : M.halt c₁.st = false := by simpa using hh
    have htr : M.δ c₁.st (c₁.tp.getD c₁.hd false) = M.δ c₂.st (c₂.tp.getD c₂.hd false) := by
      rw [hst, hread]
    rw [step_eq_of_not_halted M hh1, step_eq_of_not_halted M (by rw [← hst]; exact hh1)]
    refine ⟨congrArg (fun r => r.1) htr, by rw [htr, hhd], ?_⟩
    intro p hp
    rw [htr]
    dsimp only
    rcases hw : (M.δ c₂.st (c₂.tp.getD c₂.hd false)).2.1 with _ | w
    · exact hagree p hp
    · rw [writeAt_getD, writeAt_getD, hhd]
      by_cases hpc : p = c₂.hd
      · rw [if_pos hpc, if_pos hpc]
      · rw [if_neg hpc, if_neg hpc]; exact hagree p hp

/-- **Frozen left region.**  If the head is at `> b`, one step leaves every cell `≤ b` unchanged. -/
theorem step_left_frozen (M : Machine) (b : ℕ) (c : Cfg M) (hb : b < c.hd) (p : ℕ) (hp : p ≤ b) :
    (step M c).tp.getD p false = c.tp.getD p false := by
  by_cases hh : M.halt c.st = true
  · rw [step_of_halted M hh]
  · have hh1 : M.halt c.st = false := by simpa using hh
    rw [step_eq_of_not_halted M hh1]
    dsimp only
    rcases hw : (M.δ c.st (c.tp.getD c.hd false)).2.1 with _ | w
    · rfl
    · rw [writeAt_getD, if_neg (by omega : ¬ p = c.hd)]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
