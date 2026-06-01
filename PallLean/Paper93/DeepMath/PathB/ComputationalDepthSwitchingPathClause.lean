import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathNodup
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingProcessedUnsat

/-!
# Each path literal sits in a processed clause

**STATUS: REAL.  THE CONNECTIVE FOR THE FORWARD-DECODER COLLECTION.**

For the fold to collect every path variable, each path literal must belong to a clause
that the decoder *confirms*: a clause of `cs` that contains it and is unsatisfied under
`ρ` (so the flip test passes).  That clause is the active clause at the step the literal
was chosen.

* `pathLits_clause_facts`: every `ℓ ∈ pathLits` lies in some `C ∈ cs` with `ℓ ∈ C.lits`
  and `clauseSatisfied ρ C = false`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- Every path literal lies in a clause of `cs` that is unsatisfied under `ρ` (its active
clause at the step it was chosen). -/
theorem pathLits_clause_facts (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ s, ∀ ℓ ∈ pathLits cs ρ s,
      ∃ C, C ∈ cs ∧ ℓ ∈ C.lits ∧ clauseSatisfied ρ C = false := by
  intro s
  induction s with
  | zero => intro ℓ h; simp [pathLits] at h
  | succ k ih =>
    intro ℓ hℓ
    cases hal : activeLit cs (actPath cs ρ k) with
    | none =>
      have hpl : pathLits cs ρ (k + 1) = pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl] at hℓ; exact ih ℓ hℓ
    | some ℓ₀ =>
      have hpl : pathLits cs ρ (k + 1) = ℓ₀ :: pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl] at hℓ
      rcases List.mem_cons.mp hℓ with rfl | hℓ'
      · obtain ⟨C, hC⟩ : ∃ C, activeClause cs (actPath cs ρ k) = some C := by
          cases hac : activeClause cs (actPath cs ρ k) with
          | none => unfold activeLit at hal; rw [hac] at hal; simp at hal
          | some C => exact ⟨C, rfl⟩
        have hhead : (freeLits (actPath cs ρ k) C).head? = some ℓ := by
          have heq : activeLit cs (actPath cs ρ k) = (freeLits (actPath cs ρ k) C).head? := by
            unfold activeLit; rw [hC]
          rw [heq] at hal; exact hal
        have hℓC : ℓ ∈ C.lits := (List.mem_filter.mp (List.mem_of_mem_head? hhead)).1
        exact ⟨C, activeClause_mem hC, hℓC, clauseSatisfied_ρ_false_of_active hC⟩
      · exact ih ℓ hℓ'

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.pathLits_clause_facts
