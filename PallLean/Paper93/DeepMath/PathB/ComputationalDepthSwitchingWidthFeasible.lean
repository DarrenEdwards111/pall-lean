import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathClause

/-!
# Clause-relative indices fit in `Fin w`

**STATUS: REAL.  TYPE-LEVEL FEASIBILITY OF THE `(2w)^s` ENCODING.**

The `(2w)^s` label encodes each path variable by its index *inside its clause*.  For that
to land in `Fin w` (with `w` the bottom fan-in / max clause width), each such index must
be `< w`.  It is: a path literal lies in a clause of `cs` (`pathLits_clause_facts`), and
its `idxOf` is below the clause length, which is `≤ w`.

* `pathLits_idxOf_lt`: every path literal has a clause-relative index `< w`.

This is the feasibility fact for the clause-relative encoding; assembling the full label
(the σ\*-guided clause walk that recovers which clause each index belongs to) is the
remaining `(2w)^s` construction.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Clause-relative index feasibility.**  Under a width bound `w`, every path literal
has an index `< w` inside its clause — so the clause-relative encoding lands in `Fin w`. -/
theorem pathLits_idxOf_lt {cs : List (Clause n)} {ρ : Restriction n} {s w : ℕ}
    (hw : ∀ C ∈ cs, C.lits.length ≤ w) :
    ∀ ℓ ∈ pathLits cs ρ s, ∃ C ∈ cs, ℓ ∈ C.lits ∧ C.lits.idxOf ℓ < w := by
  intro ℓ hℓ
  obtain ⟨C, hCcs, hℓC, _⟩ := pathLits_clause_facts cs ρ s ℓ hℓ
  exact ⟨C, hCcs, hℓC, lt_of_lt_of_le (List.idxOf_lt_length_of_mem hℓC) (hw C hCcs)⟩

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.pathLits_idxOf_lt
