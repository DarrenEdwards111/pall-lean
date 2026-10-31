import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PosLabels

/-!
# Block-DT model, route-2 step [155b] kernel: the position↔variable round-trip (branch `razborov-recoverRho-wip`)

The verified core of [155b] (freed-position label injectivity): `posInTerm` is invertible given the term.  A
variable's `Fin w` position recovers the variable via the term's literal list — the key fact a position-based
decoder needs to map positions back to variables.

* `posInTerm_recover` — for a freed variable `u` of a width-`≤ w` term, `litVarOf (T.lits[posInTerm w T u])`
  is `u` (the position round-trips to the variable).

## Honest scope

This is the **fiddly core** of the recovery (the `findIdx`/`%w`/`getElem?` interplay), isolated and verified.
The full injectivity `descentSat σ₁ = descentSat σ₂ → descentPosLabels σ₁ = descentPosLabels σ₂ → σ₁ = σ₂`
additionally needs a boundary-walk decode (`posDecode…` mirroring `codeMasks_recovery`, entangled with `resetX`
semantics) — the mechanical-but-long remainder, deferred.  This kernel de-risks it: the position→variable
inversion works.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Position round-trips to variable.**  For a freed variable `u` of `T` (width `≤ w`), the literal at
`u`'s in-term position has variable `u`: `posInTerm` is invertible via `T.lits`. -/
theorem posInTerm_recover {σ : Fin n → Option Bool} {T : Clause n} {u : Fin n} (w : ℕ) [NeZero w]
    (hw : T.lits.length ≤ w) (hu : u ∈ freeVarsOf σ T) :
    (T.lits[(posInTerm w T u).val]?).map litVarOf = some u := by
  have hex : ∃ ℓ ∈ T.lits, (fun ℓ => decide (litVarOf ℓ = u)) ℓ = true := by
    rw [freeVarsOf, List.mem_filterMap] at hu
    obtain ⟨ℓ, hℓ, he⟩ := hu
    refine ⟨ℓ, hℓ, ?_⟩
    by_cases hc : σ (litVarOf ℓ) = none
    · rw [if_pos hc] at he; injection he with he'; simp [← he']
    · rw [if_neg hc] at he; simp at he
  have hfi : T.lits.findIdx (fun ℓ => decide (litVarOf ℓ = u)) < T.lits.length :=
    List.findIdx_lt_length.mpr hex
  have hmod : (posInTerm w T u).val = T.lits.findIdx (fun ℓ => decide (litVarOf ℓ = u)) := by
    simp only [posInTerm]; exact Nat.mod_eq_of_lt (lt_of_lt_of_le hfi hw)
  rw [hmod, List.getElem?_eq_getElem hfi, Option.map_some]
  congr 1
  exact of_decide_eq_true (List.findIdx_getElem (w := hfi))

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.posInTerm_recover
