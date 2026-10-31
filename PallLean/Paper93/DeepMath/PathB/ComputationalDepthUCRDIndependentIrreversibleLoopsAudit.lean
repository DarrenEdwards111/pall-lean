import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDLegalLoopTransportAudit

/-!
# UCRD independent irreversible-loop audit

For every coordinate of an `n`-bit observer state, construct a legal loop whose
return irreversibly sets exactly that coordinate to `true`. The loop
holonomies are non-flat, idempotent, pairwise commuting, and private to
distinct coordinates. All `n` loops therefore contribute `n` persistent
defects. Yet the family is stored by an ordinary `n`-bit vector and traversing
every loop costs exactly `4n`.

Thus independence, persistence, irreversibility, and non-cancellation still do
not force superpolynomial reconstruction. A separating theorem must make an
individual loop or its interaction computationally hard, rather than merely
count one cheaply addressable coordinate per loop.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDIndependentIrreversibleLoopsAudit

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.UCRDLegalLoopTransportAudit

attribute [local instance] Classical.propDecidable

/-- Boolean observer state of width `n`. -/
abbrev LoopState (n : Nat) := Fin n → Bool

def zeroState (n : Nat) : LoopState n := fun _ ↦ false

/-- Irreversibly activate one private contextual coordinate. -/
def activate {n : Nat} (i : Fin n) (s : LoopState n) : LoopState n :=
  fun j ↦ if j = i then true else s j

theorem activate_at {n : Nat} (i : Fin n) (s : LoopState n) :
    activate i s i = true := by
  simp [activate]

theorem activate_away {n : Nat} (i j : Fin n) (hji : j ≠ i)
    (s : LoopState n) : activate i s j = s j := by
  simp [activate, hji]

theorem activate_idempotent {n : Nat} (i : Fin n) (s : LoopState n) :
    activate i (activate i s) = activate i s := by
  funext j
  by_cases hji : j = i <;> simp [activate, hji]

theorem activate_commute {n : Nat} (i j : Fin n) (s : LoopState n) :
    activate i (activate j s) = activate j (activate i s) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [activate]
  · by_cases hkj : k = j <;> simp [activate, hki, hkj]

/-- Contexts are separated into one four-beat legal cycle per coordinate. -/
abbrev IndexedExperienceContext (n : Nat) := Fin n × ExperienceContext

def indexedLegal {n : Nat} :
    IndexedExperienceContext n → IndexedExperienceContext n → Prop
  | (i, c), (j, d) => i = j ∧ experienceLegal c d

/-- The `i`th loop has one irreversible private activation on return. -/
def independentLoop {n : Nat} (i : Fin n) :
    LegalTransportLoop (IndexedExperienceContext n) (LoopState n) where
  legal := indexedLegal
  c0 := (i, .opening)
  c1 := (i, .rising)
  c2 := (i, .turning)
  c3 := (i, .returning)
  legal01 := by exact ⟨rfl, trivial⟩
  legal12 := by exact ⟨rfl, trivial⟩
  legal23 := by exact ⟨rfl, trivial⟩
  legal30 := by exact ⟨rfl, trivial⟩
  transport01 := id
  transport12 := id
  transport23 := id
  transport30 := activate i
  cost01 := 1
  cost12 := 1
  cost23 := 1
  cost30 := 1

theorem independentLoop_holonomy {n : Nat} (i : Fin n) (s : LoopState n) :
    (independentLoop i).holonomy s = activate i s := by
  rfl

theorem independentLoop_work {n : Nat} (i : Fin n) :
    (independentLoop i).loopWork = 4 := by
  rfl

theorem independentLoop_not_flat {n : Nat} (i : Fin n) :
    ¬ (independentLoop i).Flat := by
  intro hflat
  have h := congrFun (hflat (zeroState n)) i
  rw [independentLoop_holonomy] at h
  simp [activate, zeroState] at h

/-- Repeating one irreversible loop does not cancel its defect. -/
theorem independentLoop_twoIterations_persist {n : Nat}
    (i : Fin n) (s : LoopState n) :
    (independentLoop i).iterateHolonomy 2 s =
      (independentLoop i).holonomy s := by
  simp only [LegalTransportLoop.iterateHolonomy]
  exact activate_idempotent i s

/-- Distinct loop holonomies commute and remain succinctly coordinate-wise. -/
theorem independentLoop_holonomies_commute {n : Nat}
    (i j : Fin n) (s : LoopState n) :
    (independentLoop i).holonomy ((independentLoop j).holonomy s) =
      (independentLoop j).holonomy ((independentLoop i).holonomy s) := by
  simp only [independentLoop_holonomy]
  exact activate_commute i j s

/-- Number of loops that visibly change the all-false state. -/
def familyDeficit (n : Nat) : Nat :=
  (Finset.univ.filter fun i : Fin n ↦
    (independentLoop i).holonomy (zeroState n) ≠ zeroState n).card

theorem every_independentLoop_changes_zero {n : Nat} (i : Fin n) :
    (independentLoop i).holonomy (zeroState n) ≠ zeroState n := by
  intro h
  have hi := congrFun h i
  rw [independentLoop_holonomy] at hi
  simp [activate, zeroState] at hi

theorem familyDeficit_eq_width (n : Nat) : familyDeficit n = n := by
  simp [familyDeficit, every_independentLoop_changes_zero]

/-- Total work of traversing every independent loop once. -/
def familyWork (n : Nat) : Nat :=
  ∑ i : Fin n, (independentLoop i).loopWork

theorem familyWork_eq_four_mul (n : Nat) : familyWork n = 4 * n := by
  simp [familyWork, independentLoop_work, Nat.mul_comm]

theorem familyWork_isPolynomialBudget : IsPolynomialBudget familyWork := by
  refine ⟨1, 4, ?_⟩
  intro n
  rw [familyWork_eq_four_mul]
  simp only [pow_one]
  exact Nat.mul_le_mul_left 4 (Nat.le_succ n)

/-- Persistent independent loop deficit grows only linearly, with linear work. -/
theorem independentPersistentLoops_linear_calibration (n : Nat) :
    familyDeficit n = n ∧ familyWork n = 4 * n :=
  ⟨familyDeficit_eq_width n, familyWork_eq_four_mul n⟩

end PallLean.Paper93.DeepMath.PathB.UCRDIndependentIrreversibleLoopsAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDIndependentIrreversibleLoopsAudit.activate_idempotent
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDIndependentIrreversibleLoopsAudit.independentLoop_not_flat
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDIndependentIrreversibleLoopsAudit.familyDeficit_eq_width
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDIndependentIrreversibleLoopsAudit.familyWork_isPolynomialBudget
