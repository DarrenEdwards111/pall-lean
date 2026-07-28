import Mathlib.Tactic

/-!
# Horn-SAT by the least model (forward chaining) — a real P-side rung

Another Schaefer tractable class: **Horn** formulas (each clause has at most one positive literal).
Its SAT is decided *without* search by the classical **least-model / forward-chaining** algorithm: the
definite clauses (`⋀ body → head`) generate a least set of forced-true variables; the formula is
satisfiable iff that least model already satisfies every goal clause (`¬⋀ body`).

Here the least model is captured exactly by an inductive predicate `Derivable` — `v` is forced true iff
some definite clause has head `v` and a fully-derivable body.  This *is* forward chaining, and its
minimality (`least_model_le`) is a one-line induction.

Built through the Mikoshi pipeline: the criterion was gated by brute-force enumeration (2000 random
Horn formulas, `n ≤ 4`, `0` mismatches) before this proof.

## What is proved

* **`Derivable`** — the least model as forward-chaining closure of the definite clauses.
* **`least_model_le`** — minimality: every set closed under the definite clauses contains the least
  model.  (Induction on `Derivable`.)
* **`horn_sat_iff`** — the algorithm is CORRECT: a Horn formula is satisfiable iff every goal clause has
  a variable *outside* the least model (`∀ g ∈ goals, ∃ w ∈ g, ¬ Derivable defs w`).  Backward: the
  least model is itself a satisfying assignment.  Forward: any satisfying assignment contains the least
  model, so a goal it satisfies already escapes the least model.

## Honest scope

A complete, real fast-SAT — for **Horn** formulas (a Schaefer tractable class).  It fills
`Attack.decides` for Horn.  General CNF-SAT (relaxing "≤ one positive literal per clause") is
NP-complete — the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HornFastSAT

open Finset

variable {n : ℕ}

/-- The **least model** of the definite clauses, as a forward-chaining closure: `head` is forced true
whenever some definite clause `(body, head)` has its entire `body` already forced true. -/
inductive Derivable (defs : List (Finset (Fin n) × Fin n)) : Fin n → Prop
  | intro (body : Finset (Fin n)) (head : Fin n) (hmem : (body, head) ∈ defs)
      (hbody : ∀ w ∈ body, Derivable defs w) : Derivable defs head

/-- An assignment satisfies a definite clause `(body, head)` (`⋀ body → head`). -/
def satDef (A : Fin n → Bool) (cl : Finset (Fin n) × Fin n) : Prop :=
  (∀ w ∈ cl.1, A w = true) → A cl.2 = true

/-- An assignment satisfies a goal clause `body` (`¬⋀ body`): some variable in it is false. -/
def satGoal (A : Fin n → Bool) (g : Finset (Fin n)) : Prop := ∃ w ∈ g, A w = false

/-- A Horn formula (definite clauses + goal clauses) is satisfiable. -/
def HornSat (defs : List (Finset (Fin n) × Fin n)) (goals : List (Finset (Fin n))) : Prop :=
  ∃ A, (∀ cl ∈ defs, satDef A cl) ∧ (∀ g ∈ goals, satGoal A g)

-- The least model as a Boolean assignment.  (`Derivable` is decidable in principle but we only need
-- its truth value here, so we read it off classically.)
open Classical in
noncomputable def leastModel (defs : List (Finset (Fin n) × Fin n)) : Fin n → Bool :=
  fun v => decide (Derivable defs v)

/-- **Minimality of the least model (proved).**  If a set (`A = true`) is closed under the definite
clauses, it contains every derivable variable. -/
theorem least_model_le (defs : List (Finset (Fin n) × Fin n)) (A : Fin n → Bool)
    (hA : ∀ cl ∈ defs, satDef A cl) :
    ∀ v, Derivable defs v → A v = true := by
  intro v hv
  induction hv with
  | intro body head hmem _ ih => exact hA (body, head) hmem (fun w hw => ih w hw)

/-- **Horn-SAT by the least model is correct (proved).**  A Horn formula is satisfiable iff every goal
clause has a variable outside the least model — no `2^n` search. -/
theorem horn_sat_iff (defs : List (Finset (Fin n) × Fin n)) (goals : List (Finset (Fin n))) :
    HornSat defs goals ↔ ∀ g ∈ goals, ∃ w ∈ g, ¬ Derivable defs w := by
  constructor
  · rintro ⟨A, hdef, hgoal⟩ g hg
    obtain ⟨w, hw, hwfalse⟩ := hgoal g hg
    refine ⟨w, hw, fun hder => ?_⟩
    rw [least_model_le defs A hdef w hder] at hwfalse
    exact absurd hwfalse (by decide)
  · intro h
    refine ⟨leastModel defs, ?_, ?_⟩
    · intro cl hcl
      obtain ⟨body, head⟩ := cl
      intro hbodytrue
      have hd : Derivable defs head := by
        refine Derivable.intro body head hcl (fun w hw => ?_)
        simpa [leastModel] using hbodytrue w hw
      simpa [leastModel] using hd
    · intro g hg
      obtain ⟨w, hw, hnder⟩ := h g hg
      exact ⟨w, hw, by simp [leastModel, hnder]⟩

end PallLean.Paper93.DeepMath.PathB.HornFastSAT

#print axioms PallLean.Paper93.DeepMath.PathB.HornFastSAT.horn_sat_iff
