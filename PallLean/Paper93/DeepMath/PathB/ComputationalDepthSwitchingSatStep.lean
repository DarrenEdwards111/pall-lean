import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCanonicalPath
import Mathlib.Logic.Function.Basic

/-!
# Satisfaction-based one-variable step (the Håstad canonical step)

**STATUS: REAL.  ONE-STEP LAYER OF THE SATISFACTION-BASED REBUILD.**

The arbitrary-value `fixOn`/`circuitPath` can recover only via an explicit
per-clause label (loose).  To reach the tight `(2w)^s` the path must fix each
variable so as to **satisfy** the active clause; then the decoder can recompute
the active clause as "first unsatisfied" from the restriction alone.

This module builds the one-step primitives and proves exactly the one-step facts
the fold will need:

* `satFix` fixes a literal's variable to make the literal **true**
  (`satFix_forces`), and changes nothing else (`satFix_eq_outside`);
* fixing any literal of a clause makes that clause **satisfied**
  (`clauseSatisfied_satFix`) — the per-step progress;
* the active clause `firstUnsat σ cs` is a function of `σ` alone (the decoder can
  recompute it), lands in `cs`, and is unsatisfied (`firstUnsat_mem`,
  `firstUnsat_unsat`);
* a `Fin`-index into the active clause's free literals resolves to a genuine free
  literal of the clause (`freeLitOf_free`, `freeLitOf_mem`).

The fold (`satPath`/`satLabel`) and the replay invariant come next.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The value that makes a literal true: `x ↦ true`, `¬x ↦ false`. -/
def satValue : Rung4Literal n → Bool
  | .pos _ => true
  | .neg _ => false

/-- Fix a literal's variable so the literal becomes true. -/
def satFix (ρ : Restriction n) (ℓ : Rung4Literal n) : Restriction n :=
  Function.update ρ (litVar ℓ) (some (satValue ℓ))

/-- `satFix` changes only the literal's own variable. -/
theorem satFix_eq_outside (ρ : Restriction n) (ℓ : Rung4Literal n) {j : Fin n}
    (hj : j ≠ litVar ℓ) : satFix ρ ℓ j = ρ j :=
  Function.update_of_ne hj _ _

/-- **The step forces its literal true.**  After `satFix`, the literal is forced
to value `true`. -/
theorem satFix_forces (ρ : Restriction n) (ℓ : Rung4Literal n) :
    Depth3.litFixedVal (satFix ρ ℓ) ℓ = some true := by
  cases ℓ with
  | pos i => simp [Depth3.litFixedVal, satFix, satValue, litVar, Function.update_self]
  | neg i => simp [Depth3.litFixedVal, satFix, satValue, litVar, Function.update_self]

/-- A clause is satisfied by `σ` if one of its literals is forced true. -/
def clauseSatisfied (σ : Restriction n) (C : Clause n) : Bool :=
  C.lits.any (Depth3.litTrue σ)

/-- **Per-step progress.**  Fixing any literal of a clause satisfies the clause. -/
theorem clauseSatisfied_satFix (ρ : Restriction n) (C : Clause n) {ℓ : Rung4Literal n}
    (hℓ : ℓ ∈ C.lits) : clauseSatisfied (satFix ρ ℓ) C = true := by
  rw [clauseSatisfied, List.any_eq_true]
  exact ⟨ℓ, hℓ, by simp [Depth3.litTrue, satFix_forces]⟩

/-- The canonical active clause: the first clause not yet satisfied by `σ`.  A pure
function of `σ` — the decoder recomputes it identically. -/
def firstUnsat (σ : Restriction n) (cs : List (Clause n)) : Option (Clause n) :=
  cs.find? (fun C => !clauseSatisfied σ C)

theorem firstUnsat_mem {σ : Restriction n} {cs : List (Clause n)} {C : Clause n}
    (h : firstUnsat σ cs = some C) : C ∈ cs :=
  List.mem_of_find?_eq_some h

theorem firstUnsat_unsat {σ : Restriction n} {cs : List (Clause n)} {C : Clause n}
    (h : firstUnsat σ cs = some C) : clauseSatisfied σ C = false := by
  have := List.find?_some h
  simpa using this

/-- The free literals of a clause under `σ`. -/
def freeLits (σ : Restriction n) (C : Clause n) : List (Rung4Literal n) :=
  C.lits.filter (Depth3.litFree σ)

/-- The `i`-th free literal of a clause (the step's `Fin w` index resolves here). -/
def freeLitOf (σ : Restriction n) (C : Clause n) (i : Fin (freeLits σ C).length) :
    Rung4Literal n :=
  (freeLits σ C).get i

/-- **The index resolves to a genuinely free literal.** -/
theorem freeLitOf_free (σ : Restriction n) (C : Clause n) (i : Fin (freeLits σ C).length) :
    Depth3.litFree σ (freeLitOf σ C i) = true :=
  (List.mem_filter.mp (List.get_mem (freeLits σ C) i)).2

/-- The chosen free literal is a literal of the clause. -/
theorem freeLitOf_mem (σ : Restriction n) (C : Clause n) (i : Fin (freeLits σ C).length) :
    freeLitOf σ C i ∈ C.lits :=
  List.mem_of_mem_filter (List.get_mem (freeLits σ C) i)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.satFix_forces
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.clauseSatisfied_satFix
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeLitOf_free
