import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWidthSize

/-!
# The unit-resolution graft identity

The mechanism of the **asymmetric** branching recombination in the general
size–width method.  After deriving a unit clause `{compl ℓ}` from `F`, the
restricted axioms of `F|_{compl ℓ}` — each of the form `C.erase ℓ` for an
`F`-axiom `C` — are recovered as resolvents `resolvent compl C {compl ℓ} ℓ` at
**no extra width**:
\[
  \operatorname{resolvent} C\ \{compl\ ℓ\}\ ℓ \;=\; C.\mathrm{erase}\ ℓ .
\]

This is exactly why one branch of the BSW recursion pays `+1` (the lift) while the
other pays `+0` (this graft) — the source of the `√(n ln S)` (rather than `n`)
width bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace ResolutionClause

variable {Lit : Type*} [DecidableEq Lit]

/-- **Unit-graft identity.**  Resolving any clause `C` against the unit `{compl ℓ}`
on pivot `ℓ` just erases `ℓ` from `C`. -/
theorem resolvent_unit_eq_erase (compl : Lit → Lit) (C : ResolutionClause Lit) (ℓ : Lit) :
    ResolutionClause.resolvent compl C {compl ℓ} ℓ = C.erase ℓ := by
  rw [ResolutionClause.resolvent, Finset.erase_singleton, Finset.union_empty]

/-- The graft does not increase width: `C.erase ℓ` is no wider than `C`. -/
theorem width_resolvent_unit_le (compl : Lit → Lit) (C : ResolutionClause Lit) (ℓ : Lit) :
    ResolutionClause.width (ResolutionClause.resolvent compl C {compl ℓ} ℓ)
      ≤ ResolutionClause.width C := by
  rw [resolvent_unit_eq_erase]
  exact Finset.card_erase_le

/-- Symmetric form: resolving the unit `{ℓ}` (left) against `E` on pivot `ℓ` erases
`compl ℓ` from `E`. -/
theorem resolvent_unit_left_eq_erase (compl : Lit → Lit) (E : ResolutionClause Lit) (ℓ : Lit) :
    ResolutionClause.resolvent compl {ℓ} E ℓ = E.erase (compl ℓ) := by
  rw [ResolutionClause.resolvent, Finset.erase_singleton, Finset.empty_union]

end ResolutionClause

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.ResolutionClause.resolvent_unit_eq_erase
#print axioms PallLean.Paper93.DeepMath.PathB.ResolutionClause.width_resolvent_unit_le
#print axioms PallLean.Paper93.DeepMath.PathB.ResolutionClause.resolvent_unit_left_eq_erase
