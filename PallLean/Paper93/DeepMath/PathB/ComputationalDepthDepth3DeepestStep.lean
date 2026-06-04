import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfy

/-!
# Step-indexed deepest-branch state infrastructure

The forward arguments the general interleaved decoder needs (continuing a branch state to the leaf,
sequencing blocks) require the deepest branch's *one-step* transition as an explicit function, plus the
unfolding `deepestEnd cs (F+1) σ = deepestEnd cs F (deepestStep cs F σ)`.

* `deepestStep cs F σ` — the single deepest-branch step from `σ` (the depth-deeper successor at
  remaining fuel `F`; `σ` itself when the branch is stuck: satisfied, no active clause, or no free
  literal).
* `deepestEnd_activeTerm_none` / `deepestEnd_head_none` — the deepest end-state is `σ` when the branch
  is stuck (companions to `deepestEnd_of_anyTermSat`).
* `deepestEnd_succ` — **the unfolding**: `deepestEnd cs (F+1) σ = deepestEnd cs F (deepestStep cs F σ)`.
  So the leaf from `σ` is the leaf from its first-step successor — enabling induction along the branch.
* `deepestStep_active` — the explicit successor at a genuine (non-stuck) step.

This is the transition layer the leaf-identification and block-sequencing arguments build on.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The deepest end-state is fixed once there is no active clause. -/
theorem deepestEnd_activeTerm_none (cs : List (Clause n)) (σ : Fin n → Option Bool)
    (h : SwitchingCounting.activeTerm cs σ = none) : ∀ F, deepestEnd cs F σ = σ
  | 0 => rfl
  | _ + 1 => by
    rw [deepestEnd]
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [hany]
    | false => simp [hany, h]

/-- The deepest end-state is fixed once the active clause has no free literal. -/
theorem deepestEnd_head_none (cs : List (Clause n)) (σ : Fin n → Option Bool) (T : Clause n)
    (hany : SwitchingCounting.anyTermSat cs σ = false) (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = none) : ∀ F, deepestEnd cs F σ = σ
  | 0 => rfl
  | _ + 1 => by rw [deepestEnd]; simp [hany, hact, hh]

/-- **One deepest-branch step.**  The depth-deeper successor at remaining fuel `F`, or `σ` when the
branch is stuck (no active clause, no free literal, or already satisfied). -/
def deepestStep (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool) : Fin n → Option Bool :=
  if SwitchingCounting.anyTermSat cs σ then σ
  else match SwitchingCounting.activeTerm cs σ with
    | none => σ
    | some T => match (SwitchingCounting.freeLits σ T).head? with
      | none => σ
      | some ℓ =>
        if (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
           (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
        then fixVar σ (litVar ℓ) false else fixVar σ (litVar ℓ) true

/-- **The deepest-end unfolding.**  The leaf from `σ` at fuel `F+1` is the leaf from its first-step
successor at fuel `F`.  Iterating this walks the branch one step at a time. -/
theorem deepestEnd_succ (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool) :
    deepestEnd cs (F + 1) σ = deepestEnd cs F (deepestStep cs F σ) := by
  rw [deepestEnd, deepestStep]
  cases hany : SwitchingCounting.anyTermSat cs σ with
  | true => simp only [hany, if_true]; exact (deepestEnd_of_anyTermSat cs hany F).symm
  | false =>
    simp only [hany, Bool.false_eq_true, if_false]
    cases hact : SwitchingCounting.activeTerm cs σ with
    | none => simp only [hact]; exact (deepestEnd_activeTerm_none cs σ hact F).symm
    | some T =>
      cases hh : (SwitchingCounting.freeLits σ T).head? with
      | none => simp only [hact, hh]; exact (deepestEnd_head_none cs σ T hany hact hh F).symm
      | some ℓ =>
        simp only [hact, hh]
        by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
            (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
        · rw [if_pos hd, if_pos hd]
        · rw [if_neg hd, if_neg hd]

/-- **The explicit successor at a genuine step.**  When `σ` is not stuck — no term satisfied, active
clause `T`, head free literal `ℓ` — the step fixes `litVar ℓ` to the depth-deeper bit. -/
theorem deepestStep_active (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool) (T : Clause n)
    {ℓ : Rung4Literal n} (hany : SwitchingCounting.anyTermSat cs σ = false)
    (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) :
    deepestStep cs F σ =
      (if (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
          (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
       then fixVar σ (litVar ℓ) false else fixVar σ (litVar ℓ) true) := by
  rw [deepestStep]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestEnd_succ
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestStep_active
