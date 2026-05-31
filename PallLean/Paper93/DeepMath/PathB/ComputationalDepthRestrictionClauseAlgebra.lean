import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWidthSize

/-!
# Clause-level algebra of value restriction (toward the general DAG size–width bound)

The fat-clause method restricts a popular literal `ℓ` to **true**.  At the clause
level this means:

* a clause containing `ℓ` is satisfied and *removed*;
* every other clause `C` loses its now-false literal `compl ℓ`, i.e. maps to
  `C.erase (compl ℓ)`.

This file proves the purely combinatorial core of how that interacts with the
resolvent — the part that is independent of any `Fin` re-indexing of the
surviving clauses.  The three facts that drive the restricted-derivation
recursion are:

* **`restrictClause_resolvent`** (unconditional): restriction commutes with the
  resolvent, `rc (resolvent C E p) = resolvent (rc C) (rc E) p`.  Hence when both
  parents survive the restricted clause is again an exact resolvent.
* **`restrictClause_subset_resolvent_pivot`** / **`_pivot'`**: when the pivot is
  `ℓ` (resp. `compl ℓ`) — the only way a resolvent can survive while a parent is
  removed — the restricted resolvent is a *superclause* of the surviving parent.
  This is the **weakening** that forces the restricted system into the
  weakening-DAG model.

Width does not increase (`restrictClause_width_le`).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace RestrictionClauseAlgebra

variable {Lit : Type*} [DecidableEq Lit]

/-- Restrict the clause `C` by setting literal `ℓ` to true: drop the now-false
literal `compl ℓ`.  (Clauses containing `ℓ` are removed elsewhere; this map is the
action on surviving clauses.) -/
def restrictClause (compl : Lit → Lit) (ℓ : Lit) (C : ResolutionClause Lit) :
    ResolutionClause Lit :=
  C.erase (compl ℓ)

@[simp] theorem mem_restrictClause (compl : Lit → Lit) (ℓ : Lit) (C : ResolutionClause Lit)
    (x : Lit) : x ∈ restrictClause compl ℓ C ↔ x ≠ compl ℓ ∧ x ∈ C := by
  simp [restrictClause, Finset.mem_erase]

/-- **Restriction commutes with the resolvent**, unconditionally.  Erase distributes
over union and commutes with erasing the pivot, so dropping `compl ℓ` from the
resolvent equals resolving the two restricted parents. -/
theorem restrictClause_resolvent (compl : Lit → Lit) (ℓ : Lit)
    (C E : ResolutionClause Lit) (p : Lit) :
    restrictClause compl ℓ (ResolutionClause.resolvent compl C E p)
      = ResolutionClause.resolvent compl (restrictClause compl ℓ C)
          (restrictClause compl ℓ E) p := by
  ext x
  simp only [restrictClause, ResolutionClause.resolvent, Finset.mem_erase, Finset.mem_union]
  tauto

/-- Restriction never increases width. -/
theorem restrictClause_width_le (compl : Lit → Lit) (ℓ : Lit) (C : ResolutionClause Lit) :
    ResolutionClause.width (restrictClause compl ℓ C) ≤ ResolutionClause.width C :=
  Finset.card_erase_le

/-- **Weakening via pivot `ℓ`.**  If a resolvent with pivot `ℓ` survives the
restriction while its left parent `C` was satisfied (removed), the restricted
resolvent is a superclause of the restricted right parent `E`. -/
theorem restrictClause_subset_resolvent_pivot (compl : Lit → Lit) (ℓ : Lit)
    (C E : ResolutionClause Lit) :
    restrictClause compl ℓ E
      ⊆ restrictClause compl ℓ (ResolutionClause.resolvent compl C E ℓ) := by
  intro x hx
  rw [restrictClause_resolvent]
  rw [mem_restrictClause] at hx
  simp only [ResolutionClause.resolvent, Finset.mem_union, Finset.mem_erase, mem_restrictClause]
  exact Or.inr ⟨hx.1, hx.1, hx.2⟩

/-- **Weakening via pivot `compl ℓ`.**  Symmetric to the previous lemma: a
resolvent with pivot `compl ℓ` whose right parent was removed restricts to a
superclause of the restricted left parent `C`. -/
theorem restrictClause_subset_resolvent_pivot' (compl : Lit → Lit) (ℓ : Lit)
    (C E : ResolutionClause Lit) :
    restrictClause compl ℓ C
      ⊆ restrictClause compl ℓ (ResolutionClause.resolvent compl C E (compl ℓ)) := by
  intro x hx
  rw [restrictClause_resolvent]
  rw [mem_restrictClause] at hx
  simp only [ResolutionClause.resolvent, Finset.mem_union, Finset.mem_erase, mem_restrictClause]
  exact Or.inl ⟨hx.1, hx.1, hx.2⟩

end RestrictionClauseAlgebra

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionClauseAlgebra.restrictClause_resolvent
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionClauseAlgebra.restrictClause_subset_resolvent_pivot
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictionClauseAlgebra.restrictClause_subset_resolvent_pivot'
