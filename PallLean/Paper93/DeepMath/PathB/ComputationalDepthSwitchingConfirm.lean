import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFreeConfirm

/-!
# The confirm test and the Finset recovery — fold foundations

**STATUS: REAL.  THE PER-CLAUSE STEP AND RECOVERY THE FOLD ITERATES.**

Two foundations for the forward-decoder fold:

* `confirm`: the decoder's executable per-clause test — `C` is satisfied under `σ*` but
  becomes unsatisfied after freeing its labelled variables;
* `confirm_complete_eq`: it reduces to the abstract flip `sat σ* ∧ ¬sat ρ`;
* `freeOn_complete_recover`: freeing the path-variable set (as a `Finset`) from `σ*`
  returns `ρ` — the recovery the fold's collected variable set feeds into.

These are the unit the walk applies per clause and the recovery it closes with.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The decoder's executable confirm test: `C` is satisfied under `σ*` but becomes
unsatisfied after freeing its labelled variables. -/
def confirm (σstar : Restriction n) (sel : Finset (Fin n)) (C : Clause n) : Bool :=
  clauseSatisfied σstar C && !clauseSatisfied (freeOn σstar sel) C

/-- **The executable confirm test reduces to the abstract flip.**  If the freed set
matches the path variables on `C`, the test equals `satisfied under σ* ∧ unsatisfied
under ρ` — i.e. it confirms exactly the processed clauses. -/
theorem confirm_complete_eq {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {sel : Finset (Fin n)} {C : Clause n}
    (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hS : ∀ ℓ ∈ C.lits, (litVar ℓ ∈ sel ↔ litVar ℓ ∈ litList.map litVar)) :
    confirm (complete ρ litList) sel C
      = (clauseSatisfied (complete ρ litList) C && !clauseSatisfied ρ C) := by
  unfold confirm
  rw [clauseSatisfied_freeOn_complete_eq hfree hS]

/-- **Finset recovery.**  Freeing the path-variable set from the completion returns `ρ`. -/
theorem freeOn_complete_recover {ρ : Restriction n} {litList : List (Rung4Literal n)}
    {S : Finset (Fin n)} (hfree : ∀ v ∈ litList.map litVar, ρ v = none)
    (hS : ∀ j, j ∈ S ↔ j ∈ litList.map litVar) :
    freeOn (complete ρ litList) S = ρ := by
  funext j
  simp only [freeOn]
  by_cases hj : j ∈ S
  · rw [if_pos hj]; exact (hfree j ((hS j).mp hj)).symm
  · rw [if_neg hj]
    exact complete_apply_eq_of_not_mem ρ litList j (fun h => hj ((hS j).mpr h))

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.confirm_complete_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_complete_recover
