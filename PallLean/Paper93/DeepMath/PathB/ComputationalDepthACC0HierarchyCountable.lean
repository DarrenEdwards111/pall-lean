import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AbstractHierarchy

/-!
# The time hierarchy reduces to a single ingredient: diagonal simulability (PROVED)

Next step on the algorithmic half.  `abstract_time_hierarchy` derived the `Small ⊊ Big` separation from
two inputs: enumerability of `Small` (`hsmall`) and simulability of the diagonal in `Big` (`hbig`).
This file discharges the **first** input from sheer **countability** — every real complexity class is
countable — so enumerability is *automatic*, and the hierarchy reduces to the *single* genuine
ingredient: the diagonal being computable within the big class.

  `enumeration_of_countable` — a countable (nonempty) class of deciders is enumerable by some
  `D : ℕ → (ℕ → Bool)`.
  `time_hierarchy_of_countable` — if `Small` is countable and the diagonal of its canonical enumeration
  lies in `Big`, then `Small ⊊ Big`.  Enumerability is free; only diagonal-simulability remains.

So the entire content of the `¬ Collapse` input to the Williams interface is now isolated to **one**
statement: *the diagonal of the small class is computable within the big class's budget* — i.e. a
universal simulator with bounded overhead.  That is the machine-model gap, in its sharpest form.

## What is proved (clean axioms, no `sorry`)

* `enumeration_of_countable` — countable + nonempty ⇒ enumerable (`hsmall` for free).
* `time_hierarchy_of_countable` — countable `Small` + diagonal in `Big` ⇒ strict separation.

## Honest scope

The hierarchy is now reduced to the **single** unbuilt ingredient — the diagonal's simulability in the
big class (a bounded-overhead universal simulator + nondeterministic lazy diagonalization).  That, and
the `williams` succinct-SAT reduction, are the genuine machine-model content, Williams-strength, **not**
built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0HierarchyCountable

open PallLean.Paper93.DeepMath.PathB.ACC0DiagonalizationKernel
open PallLean.Paper93.DeepMath.PathB.ACC0AbstractHierarchy

variable {Small Big : (ℕ → Bool) → Prop}

/-- **A countable nonempty class of deciders is enumerable (proved).**  Discharges the `hsmall` input of
`abstract_time_hierarchy` from `Set.Countable`. -/
theorem enumeration_of_countable (hc : (setOf Small).Countable) (hne : ∃ L, Small L) :
    ∃ D : ℕ → (ℕ → Bool), ∀ L, Small L → ∃ k, L = D k := by
  obtain ⟨L0, hL0⟩ := hne
  obtain ⟨D, hD⟩ := hc.exists_eq_range ⟨L0, hL0⟩
  refine ⟨D, fun L hL => ?_⟩
  have hmem : L ∈ Set.range D := by rw [← hD]; exact hL
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, hk.symm⟩

/-- **The time hierarchy, modulo only diagonal simulability (proved).**  If `Small` is countable and
nonempty, and the diagonal of its canonical enumeration lies in `Big`, then there is a `Big` language
decided by no `Small` decider.  Enumerability is free (countability); the sole remaining ingredient is
the diagonal's membership in `Big`. -/
theorem time_hierarchy_of_countable (hc : (setOf Small).Countable) (hne : ∃ L, Small L)
    (hbig : ∀ D : ℕ → (ℕ → Bool), (∀ L, Small L → ∃ k, L = D k) → Big (diag D)) :
    ∃ L, Big L ∧ ¬ Small L := by
  obtain ⟨D, hD⟩ := enumeration_of_countable hc hne
  exact abstract_time_hierarchy D hD (hbig D hD)

/-!
**Hierarchy reduced to one ingredient.**  Countability makes enumerability free, so the `¬ Collapse`
input of the Williams interface is now isolated to a *single* statement — the diagonal of the small
class is computable within the big class's budget.  That (a bounded-overhead universal simulator) plus
the `williams` succinct-SAT reduction is the machine-model gap, Williams-strength, not built.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0HierarchyCountable

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0HierarchyCountable.enumeration_of_countable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0HierarchyCountable.time_hierarchy_of_countable
