import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFreeCount

/-!
# Iterated stability: the active clause is constant through within-clause steps

**STATUS: REAL.  THE DECODER CAN RECOMPUTE THE ACTIVE CLAUSE FROM THE END STATE.**

Combining single-step stability (`activeClause_stable`) with the exact free-count
decrement (`freeLits_actStep_length_eq`): as long as fewer than the full free-literal
count of steps are taken, the active clause stays `C` and the count decreases by one
each step.

* `activeClause_actPath_eq`: for `k < (freeLits σ C).length`,
  `activeClause cs (actPath cs σ k) = some C` and
  `(freeLits (actPath cs σ k) C).length = (freeLits σ C).length - k`.

So the reverse decoder, holding `actPath cs σ s` for any `s < (freeLits σ C).length`,
recomputes `C` directly — no label needed for the clause identity within a clause.
This is the iterated form of the within-clause clause-identity bridge; the only
remaining content for `decodeVars` is reading the per-step literal *index* off the
`(2w)^s` label.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Iterated within-clause stability.**  Below the free-literal count, the active
clause is constant and the free count decreases by one per step. -/
theorem activeClause_actPath_eq {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (hnodup : (C.lits.map litVar).Nodup) (hC : activeClause cs σ = some C) :
    ∀ k, k < (freeLits σ C).length →
      activeClause cs (actPath cs σ k) = some C ∧
        (freeLits (actPath cs σ k) C).length = (freeLits σ C).length - k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨hC, by simp [actPath]⟩
  | succ k ih =>
    intro hk
    have hk' : k < (freeLits σ C).length := Nat.lt_of_succ_lt hk
    obtain ⟨hCk, hlenk⟩ := ih hk'
    -- at step `k` the count is `len - k ≥ 2`, so the step stays within `C`
    have hge2 : 1 < (freeLits (actPath cs σ k) C).length := by
      rw [hlenk]; omega
    have hpath : actPath cs σ (k + 1) = actStep cs (actPath cs σ k) := rfl
    refine ⟨?_, ?_⟩
    · rw [hpath]; exact activeClause_stable hnodup hCk hge2
    · rw [hpath]
      have := freeLits_actStep_length_eq hnodup hCk hge2
      omega

/-- The decoder recomputes the active clause from the end state, for any step count
strictly below the clause's free-literal count. -/
theorem activeClause_actPath_end {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (hnodup : (C.lits.map litVar).Nodup) (hC : activeClause cs σ = some C)
    {s : ℕ} (hs : s < (freeLits σ C).length) :
    activeClause cs (actPath cs σ s) = some C :=
  (activeClause_actPath_eq hnodup hC s hs).1

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeClause_actPath_eq
