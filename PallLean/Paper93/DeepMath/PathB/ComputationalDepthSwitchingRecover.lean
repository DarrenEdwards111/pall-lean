import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFreeLits

/-!
# Per-clause recovery atom of the switching injection

**STATUS: REAL.  THE GLOBAL SEQUENTIAL INJECTION REMAINS THE HARD CORE.**

The per-clause instance of the `hrec` recovery used by `card_bad_le_pathlabel`:
from the *shortened* restriction together with the clause's **free-literal label**
(which literals — `≤ w` of them — were free), the original restriction `ρ` is
recovered.  The free literals' variables are exactly the fixed coordinates
(`canonicalSel_eq_freeLits`), and freeing them inverts `fixOn` (`freeOn_fixOn`).

This is the recovery step at one clause.  The remaining hard core is the **global
sequential** version: an active-clause traversal producing the length-`s`
`PathLabel`, with each step's `Fin w` index resolved against the *current* active
clause, and the corresponding global injectivity — a recursive construction with a
replay invariant, the genuine mathematical content of Håstad's lemma, not yet
built here.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Per-clause recovery.**  The shortened restriction `fixOn ρ (canonicalSel ρ C) a`
together with the free-literal label (whose variables are the fixed coordinates)
recovers `ρ` by freeing those coordinates. -/
theorem clause_recover (ρ : Restriction n) (a : Fin n → Bool) (C : Clause n) :
    freeOn (fixOn ρ (canonicalSel ρ C) a)
      (((C.lits.filter (Depth3.litFree ρ)).map litVar).toFinset) = ρ := by
  rw [← canonicalSel_eq_freeLits]
  exact freeOn_fixOn ρ (canonicalSel ρ C) a (canonicalSel_subset_freeVars ρ C)

/-- The per-clause free-literal label is `≤ w`-bounded (the per-step budget). -/
theorem clause_label_card_le_width (ρ : Restriction n) (C : Clause n) :
    (C.lits.filter (Depth3.litFree ρ)).length ≤ C.width :=
  freeLits_length_le_width ρ C

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clause_recover
