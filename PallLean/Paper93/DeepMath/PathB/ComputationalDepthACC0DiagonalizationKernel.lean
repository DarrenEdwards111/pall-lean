import Mathlib

/-!
# The diagonalization kernel of the Williams interface's hierarchy input (PROVED)

A genuine run at the **algorithmic half** of Williams' route (the user's point #3).  The interface
`probabilistic_route_to_NEXP_not_ACC0` is an abstract socket whose two undischarged inputs are
`williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse` and `hierarchy : ¬ Collapse`.  The
`hierarchy` input is the **nondeterministic time hierarchy** (`NTIME(2^n) ⊄ NTIME(2^n/ω(1))`), whose
engine is **diagonalization**.  This file proves the irreducible kernel of that engine, abstractly:

  `diag_ne` / `diag_not_mem_range` — the diagonal function `diag D k = ¬ D k k` differs from every `D k`
  and so is **not** in the enumerated family `D` — Cantor's diagonal, the seed of every hierarchy and
  undecidability separation.

So the *logical core* of `¬ Collapse` is a theorem here.  What it is **not**: the NTIME hierarchy itself.
That requires (i) a concrete time-bounded (nondeterministic) machine model, (ii) an efficient universal
simulator with bounded overhead, and (iii) nondeterministic *lazy* diagonalization to fit the diagonal
inside the larger time bound.  Those are the genuine remaining complexity-theory formalization — the
machine-model gap — and are **not** built here.

## What is proved (clean axioms, no `sorry`)

* `diag_ne` — `diag D ≠ D k` for every `k`.
* `diag_not_mem_range` — `diag D ∉ Set.range D`: the diagonal escapes any enumeration.
* `no_decider_decides_own_diagonal` — no `D` has `diag D = D k` for any `k` (the self-reference form).

## Honest scope

This is the diagonalization *kernel* — the proof technique behind the hierarchy input to the Williams
interface — not the NTIME hierarchy and not the interface.  Discharging `hierarchy` (and `williams`)
needs the machine model + simulation overhead + the succinct-SAT reduction: Williams-strength, not built.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel

/-- The diagonal of a decider enumeration: `diag D k = ¬ D k k`. -/
def diag (D : ℕ → ℕ → Bool) : ℕ → Bool := fun k => !D k k

/-- **The diagonal differs from every enumerated decider (proved).** -/
theorem diag_ne (D : ℕ → ℕ → Bool) (k : ℕ) : diag D ≠ D k := by
  intro h
  have hk := congrFun h k
  simp only [diag] at hk
  exact (Bool.not_ne_self (D k k)) hk

/-- **The diagonal escapes the enumeration (proved): `diag D ∉ Set.range D`.**  Cantor's diagonal — the
seed of the time hierarchy / undecidability separations. -/
theorem diag_not_mem_range (D : ℕ → ℕ → Bool) : diag D ∉ Set.range D := by
  rintro ⟨k, hk⟩
  exact diag_ne D k hk.symm

/-- **No decider decides its own diagonal (proved).** -/
theorem no_decider_decides_own_diagonal (D : ℕ → ℕ → Bool) : ¬ ∃ k, diag D = D k := by
  rintro ⟨k, hk⟩
  exact diag_ne D k hk

/-!
**Diagonalization kernel proved.**  The diagonal escapes any decider enumeration — the logical core of
the hierarchy input `¬ Collapse` to the Williams interface.  The NTIME hierarchy itself (machine model +
bounded-overhead universal simulator + nondeterministic lazy diagonalization) and the `williams`
reduction (succinct-SAT) are the genuine remaining complexity-theory content, Williams-strength, not
built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel.diag_not_mem_range
