import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSatPath

/-!
# Corrected active clause: first unsatisfied clause that still has a free literal

**STATUS: REAL.  TRAVERSAL FIX FOR THE FORWARD DECODER.**

A bug surfaced while designing the decoder: `firstUnsat` (first *unsatisfied*
clause) does not advance past a fully **falsified** clause — such a clause is
unsatisfied but has no free literal, so the step stalls and the path never reaches
later clauses (degenerate, single-clause).

The canonical path must instead use the first clause that is unsatisfied **and**
still has a free literal — `activeClause` — so that once a clause is exhausted
(fully falsified) the path moves on.  This file builds that corrected selector and
its characterizing facts (the decoder needs: the active clause is unsatisfied, has
a free literal, and the chosen literal is genuinely free).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The corrected active clause: first clause that is unsatisfied **and** has a free
literal.  A pure function of `σ` (decoder-recomputable). -/
def activeClause (cs : List (Clause n)) (σ : Restriction n) : Option (Clause n) :=
  cs.find? (fun C => !clauseSatisfied σ C && decide (0 < (freeLits σ C).length))

theorem activeClause_mem {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (h : activeClause cs σ = some C) : C ∈ cs :=
  List.mem_of_find?_eq_some h

theorem activeClause_unsat {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (h : activeClause cs σ = some C) : clauseSatisfied σ C = false := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this.1

theorem activeClause_hasFree {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (h : activeClause cs σ = some C) : 0 < (freeLits σ C).length := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

/-- The literal chosen at one step under the corrected active clause: the first free
literal of the active clause. -/
def activeLit (cs : List (Clause n)) (σ : Restriction n) : Option (Rung4Literal n) :=
  match activeClause cs σ with
  | none => none
  | some C => (freeLits σ C).head?

/-- Under the corrected active clause, a step's literal exists whenever an active
clause exists (the active clause has a free literal). -/
theorem activeLit_isSome {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (h : activeClause cs σ = some C) : (activeLit cs σ).isSome := by
  unfold activeLit
  rw [h]
  cases hf : (freeLits σ C) with
  | nil => exact absurd (activeClause_hasFree h) (by rw [hf]; simp)
  | cons a l => simp [hf]

/-- The chosen literal is genuinely free. -/
theorem activeLit_free {cs : List (Clause n)} {σ : Restriction n} {ℓ : Rung4Literal n}
    (h : activeLit cs σ = some ℓ) : Depth3.litFree σ ℓ = true := by
  unfold activeLit at h
  cases hC : activeClause cs σ with
  | none => rw [hC] at h; exact absurd h (by simp)
  | some C =>
    rw [hC] at h
    exact (List.mem_filter.mp (List.mem_of_mem_head? h)).2

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeLit_free
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeClause_hasFree
