import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DiagonalizationKernel

/-!
# The abstract time hierarchy from diagonalization — the `¬Collapse` structure (PROVED)

Next step on the algorithmic half.  `ACC0DiagonalizationKernel` proved the diagonal escapes any
enumeration.  This file lifts that kernel into the **separation structure** the Williams interface's
`hierarchy : ¬ Collapse` input needs: a *strict* class separation `Small ⊊ Big`, derived from
diagonalization, with the genuine machine-model content isolated as exactly two named hypotheses.

  `abstract_time_hierarchy` — if the `Small` class is **enumerable** by deciders `D` (`hsmall`) and the
  diagonal `diag D` lies in the `Big` class (`hbig`), then there is a `Big` language decided by **no**
  `Small` decider: `∃ L, Big L ∧ ¬ Small L`.

  `collapse_false_of_hierarchy` — hence the abstract `Collapse` (`Big ⊆ Small`) is **false** under those
  two hypotheses — the `¬ Collapse` input, modulo the machine model.

The proof is pure diagonalization (`diag_ne`): the diagonal is in `Big` (by `hbig`) but differs from
every `Small` decider, so it is not in `Small`.

## What is proved (clean axioms, no `sorry`)

* `abstract_time_hierarchy` — diagonalization ⇒ strict `Small ⊊ Big` (modulo enumerability + simulability).
* `collapse_false_of_hierarchy` — the `¬ (Big ⊆ Small)` form (the interface's `hierarchy` input).

## Honest scope — exactly where the machine model enters

The two hypotheses are the genuine, unbuilt complexity-theory content:
* `hsmall : ∀ L, Small L → ∃ k, L = D k` — the small class is **effectively enumerable** (a time-bounded
  machine model + a Gödel numbering of its deciders).
* `hbig : Big (diag D)` — the diagonal is **computable within the big class's budget** (a universal
  simulator with bounded overhead + nondeterministic lazy diagonalization).

This is the hierarchy *structure*, proved; the *instantiation* to `NTIME(2^n) ⊄ NTIME(2^n/ω(1))` — i.e.
discharging `hsmall`/`hbig` for the real nondeterministic time classes — is the machine-model gap,
Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0AbstractHierarchy

open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel

variable {Small Big : (ℕ → Bool) → Prop}

/-- **The abstract time hierarchy (proved).**  If `Small` is enumerable by `D` and the diagonal of `D`
lies in `Big`, then some `Big` language is decided by no `Small` decider — a strict separation, by
diagonalization. -/
theorem abstract_time_hierarchy (D : ℕ → ℕ → Bool)
    (hsmall : ∀ L, Small L → ∃ k, L = D k)
    (hbig : Big (diag D)) :
    ∃ L, Big L ∧ ¬ Small L :=
  ⟨diag D, hbig, fun hS => by
    obtain ⟨k, hk⟩ := hsmall _ hS
    exact diag_ne D k hk⟩

/-- **The `¬ Collapse` input, modulo the machine model (proved).**  Under enumerability + simulability,
the abstract collapse `Big ⊆ Small` is false. -/
theorem collapse_false_of_hierarchy (D : ℕ → ℕ → Bool)
    (hsmall : ∀ L, Small L → ∃ k, L = D k)
    (hbig : Big (diag D)) :
    ¬ (∀ L, Big L → Small L) := by
  intro hsub
  obtain ⟨L, hBig, hnS⟩ := abstract_time_hierarchy D hsmall hbig
  exact hnS (hsub L hBig)

/-!
**Abstract hierarchy proved.**  Diagonalization gives the strict `Small ⊊ Big` separation — the
`¬ Collapse` structure of the Williams interface — modulo exactly two named inputs: small-class
enumerability and diagonal simulability in the big class.  Those are the time-bounded machine model +
universal simulator (the machine-model gap), Williams-strength, not built.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0AbstractHierarchy

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AbstractHierarchy.abstract_time_hierarchy
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0AbstractHierarchy.collapse_false_of_hierarchy
