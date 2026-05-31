import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonicalPath

/-!
# The selector is the variables of the clause's free literals (recoverability basis)

**STATUS: REAL.  THE PER-STEP SEQUENTIAL PATH + GLOBAL INJECTION REMAIN.**

The tight `(2w)^s` label works because the canonical selector for a clause is not
an arbitrary subset of `[N]` — it is exactly the variables of the *free literals*
of that clause, and a clause has `≤ w` literals.  So the selected coordinates are
recoverable from *which literals of the clause* were chosen (a `≤ w`-bounded
datum), which is precisely what a `PathStepLabel`'s `Fin w` component records.

  `canonicalSel ρ C = ((C.lits.filter (litFree ρ)).map litVar).toFinset`.

This is the recoverability basis for the index-based label.  Assembling it into a
per-step sequential active-clause traversal (giving the `(2w)^s` path, not the
loose `2^w` per clause) and the global encoding injection is the remaining
synthesis — the genuine hard core of Håstad's lemma.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Recoverability basis.**  The canonical selector of a clause is exactly the set
of variables of its *free* literals.  Since a clause has `≤ w` literals, the
selected coordinates are determined by which literals (a `≤ w`-bounded choice) — the
basis for the tight index-based label. -/
theorem canonicalSel_eq_freeLits (ρ : Restriction n) (C : Clause n) :
    canonicalSel ρ C = ((C.lits.filter (Depth3.litFree ρ)).map litVar).toFinset := by
  ext e
  simp only [canonicalSel, Finset.mem_inter, mem_freeVars, clauseVars, List.mem_toFinset,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨he, ℓ, hℓ, hve⟩
    exact ⟨ℓ, ⟨hℓ, by simp [litFree_var, hve, he]⟩, hve⟩
  · rintro ⟨ℓ, ⟨hℓ, hfℓ⟩, hve⟩
    rw [litFree_var, hve] at hfℓ
    exact ⟨Option.isNone_iff_eq_none.mp hfℓ, ℓ, hℓ, hve⟩

/-- The number of *free literals* of a clause is at most its width — the per-clause
budget that the per-step label spends. -/
theorem freeLits_length_le_width (ρ : Restriction n) (C : Clause n) :
    (C.lits.filter (Depth3.litFree ρ)).length ≤ C.width := by
  rw [Clause.width]
  exact List.length_filter_le _ _

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.canonicalSel_eq_freeLits
