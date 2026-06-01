import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingDecode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingAssembly

/-!
# Injectivity via the path-list witness

**STATUS: REAL.  TIGHT `(2w)^s` REINDEX REMAINS (and genuinely needs per-step replay).**

Transfers the set-label injectivity (`circuitPath_inj`) to the actual **path-list**
witness `circuitPathList`: since the selected set is the union of the path list
(`circuitSel_eq`), a restriction is recovered from its path restriction together
with its path list.

  `circuitPathList_inj : circuitPath ρ = circuitPath σ → circuitPathList ρ = circuitPathList σ → ρ = σ`.

This is the encoding injective in its *path-list* representation — one step closer
to the `PathLabel w s` form the counting lemma consumes.

**Honest note on the remaining step.**  Reindexing `circuitPathList` (a per-*clause*
list of selected-coordinate finsets) into the tight per-*variable* `PathLabel w s`
(`Fin s → Fin w × Bool`) is **not** pure bookkeeping: recovering a coordinate from
a `Fin w` index requires knowing the *active clause* at that step, i.e. the
per-variable active-clause replay.  The set-level recovery proved here does not by
itself supply that index→coordinate expansion.  So the tight reindex is a genuine
(finer-granularity) construction, not just a representation change.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Injectivity via the path-list witness.**  A restriction is recovered from its
path restriction together with its path list (the selected set is the union of the
list, `circuitSel_eq`, so this reduces to `circuitPath_inj`). -/
theorem circuitPathList_inj (ts : List (Term n)) (a : Fin n → Bool) {ρ σ : Restriction n}
    (hp : circuitPath ρ ts a = circuitPath σ ts a)
    (hl : circuitPathList ρ ts a = circuitPathList σ ts a) : ρ = σ := by
  refine circuitPath_inj ts a hp ?_
  rw [circuitSel_eq ts ρ a, circuitSel_eq ts σ a, hl]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.circuitPathList_inj
