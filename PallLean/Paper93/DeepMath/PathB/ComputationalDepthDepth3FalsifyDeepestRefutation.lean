import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TseitinInstantiation

/-!
# Attacking Obligation 1 (falsify-deepest): the good restriction's shallow residual refutation

In the falsify-deepest regime the switching count is unconditional (`exists_good_falsify_deepest`):
a *good* restriction exists.  To make the depth-3 lower bound unconditional there, that good
restriction must yield the **shallow refuting tree** that `depth3_lower_bound_modulo_collapse`
consumes.  This file builds the refutation-extraction side, for the explicit Tseitin circuit.

The key fact (`validSearch_canonicalDT` is *general* in the restriction): for the explicit
tautological circuit `dualDNF (tseitinAxList G charge)`, the canonical tree at **any** restriction
`ρ` is a valid resolution search from `falseSet ρ`, of depth `≤ stars ρ`.  Hence at a *low-star* good
restriction (`stars ρ ≤ budget`):

* `tseitin_circuit_validSearch_shallow` — the canonical tree is a `ValidSearch` from `falseSet ρ` of
  depth `≤ budget`.  The tautology is discharged concretely (`tseitinAxList_unsat` ⟹
  `rFalsifies_unsat_of_tlit_unsat` ⟹ `dualDNF_taut_of_unsat`).

This is the falsify-deepest collapse **output**: a good restriction of the explicit circuit gives a
shallow residual refutation.

## The two remaining sub-gaps (honest, NOT faked)

1. **Star bound from the count.**  `exists_good_falsify_deepest` gives `ρ ∉ Bad` for the
   falsify-path bad set; pinning `stars ρ ≤ budget` needs the standard `K`-star restriction family
   (`exists_good_restriction_in` over `{stars = K}`) plus the binomial regime — wiring, not new math.
2. **`falseSet ρ` → `∅` restriction-composition.**  The residual refutation here is from `falseSet ρ`
   (the restriction's fixed literals), while the width lower bound consumes an `∅`-refutation over the
   (restricted) expander.  Bridging them — the residual Tseitin is still an expander on the unfixed
   edges — is the genuine restriction-composition step, distinct from the count.

So in the falsify-deepest regime the collapse's refutation-extraction is built; the end-to-end is
reduced to these two precise pieces (neither is the fenced satisfy-step core).  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

namespace SearchDischarge

open Depth3

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- **The explicit Tseitin circuit is a tautology** (over Boolean assignments): its dual DNF is true
everywhere, since the constraint system is unsatisfiable (odd charge). -/
theorem tseitin_circuit_taut (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) :
    ∀ x, Depth3.dnfEval (dualDNF (tseitinAxList G charge)) x = true :=
  dualDNF_taut_of_unsat (rFalsifies_unsat_of_tlit_unsat (tseitinAxList_unsat G charge hodd))

/-- **Good restriction ⟹ shallow residual refutation.**  At any restriction `ρ` of the explicit
Tseitin circuit with `stars ρ ≤ budget`, the canonical tree is a valid resolution search from
`falseSet ρ` of depth `≤ budget` — the falsify-deepest collapse's refutation output.  (The width
lower bound additionally needs this lifted from `falseSet ρ` to `∅`; see the file docstring.) -/
theorem tseitin_circuit_validSearch_shallow (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) (ρ : Fin n → Option Bool) {budget : ℕ}
    (hb : SwitchingCounting.stars ρ ≤ budget) :
    ValidSearch rpos rcompl (labSearch (dualDNF (tseitinAxList G charge)))
        (AxiomOf (dualDNF (tseitinAxList G charge))) (falseSet ρ)
        (Depth3.canonicalDT (dualDNF (tseitinAxList G charge)) (SwitchingCounting.stars ρ) ρ) ∧
      (Depth3.canonicalDT (dualDNF (tseitinAxList G charge)) (SwitchingCounting.stars ρ) ρ).depth
        ≤ budget := by
  refine ⟨validSearch_canonicalDT _ (tseitin_circuit_taut G charge hodd) _ ρ (le_refl _), ?_⟩
  exact le_trans (Depth3.canonicalDT_depth_le _ _ ρ) hb

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tseitin_circuit_taut
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tseitin_circuit_validSearch_shallow
