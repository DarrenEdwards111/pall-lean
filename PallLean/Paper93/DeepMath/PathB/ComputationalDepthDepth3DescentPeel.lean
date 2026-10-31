import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentSat

/-!
# Block-DT model, foundation 49: branching holography, step 4g — the peel decoder (branch only)

The label-aware peel for the branching descent, ported from the single-path `blockPeel`/`block_recovery`.
Because the branching descent's intermediate states depend on the path values `x` (unlike the
deterministic single `killTerm` path), the per-block masks carry those values (`some (x v)` on the freed
variables); the peel resets each recovered block to its stored values to step to the next state.

* `descentStream` — the descent's active-clause stream (`T₀, T₁, …`).
* `descentSatMasks` — per-block value-carrying masks (`some (x v)` on the block's freed variables).
* `descentPeel` — `find?`-first-satisfied, reset the block to its mask, recurse.
* `descentSat_step` — resetting the recovered block to its mask steps the boundary to the next state.
* `descent_recovery` — `descentPeel (descentSatMasks …) (descentSat …) = descentStream …`: the peel of the
  satisfying boundary recovers the whole active-clause stream, for any `σ`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The descent's active-clause stream. -/
def descentStream (cs : List (Clause n)) (w : ℕ) :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → List (Clause n)
  | 0, _, _ => []
  | F + 1, σ, x =>
    if anyTermSat cs σ then []
    else match activeTerm cs σ with
      | none => []
      | some T => T :: descentStream cs w F (extendσ σ T x) x

/-- The per-block value-carrying masks: `some (x v)` on the block's freed variables, `none` elsewhere. -/
def descentSatMasks (cs : List (Clause n)) (w : ℕ) :
    ℕ → (Fin n → Option Bool) → (Fin n → Bool) → List (Fin n → Option Bool)
  | 0, _, _ => []
  | F + 1, σ, x =>
    if anyTermSat cs σ then []
    else match activeTerm cs σ with
      | none => []
      | some T =>
        (fun v => if v ∈ freeVarsOf σ T then some (x v) else none)
          :: descentSatMasks cs w F (extendσ σ T x) x

/-- Reset: take the mask's value where present, else keep the restriction's. -/
def resetX (m σ' : Fin n → Option Bool) : Fin n → Option Bool :=
  fun v => match m v with
    | some b => some b
    | none => σ' v

/-- The label-aware peel: find the first satisfied term, reset its block to the mask, recurse. -/
def descentPeel (cs : List (Clause n)) :
    List (Fin n → Option Bool) → (Fin n → Option Bool) → List (Clause n)
  | [], _ => []
  | m :: ms, σ' =>
    match cs.find? (termSat σ') with
    | none => []
    | some T => T :: descentPeel cs ms (resetX m σ')

/-- A coordinate not freed by `T` does not satisfy the `descentSat` active-step condition. -/
theorem not_cond_of_not_mem_free {σ : Fin n → Option Bool} {T : Clause n} {v : Fin n}
    (hv : v ∉ freeVarsOf σ T) :
    ¬(σ v = none ∧ ((Rung4Literal.pos v) ∈ T.lits ∨ (Rung4Literal.neg v) ∈ T.lits)) := by
  rintro ⟨hnone, hor⟩
  rcases hor with hp | hn
  · exact hv (litVar_mem_freeVarsOf hp (by simp [DTree.freeLit, hnone]))
  · exact hv (litVar_mem_freeVarsOf hn (by simp [DTree.freeLit, hnone]))

/-- **The step lemma.**  Resetting the active block to its value-carrying mask steps the boundary from
`σ` to the next descent state `extendσ σ T x`. -/
theorem descentSat_step {cs : List (Clause n)} {w F : ℕ} {σ : Fin n → Option Bool} {T : Clause n}
    (x : Fin n → Bool) (hany : anyTermSat cs σ = false) (hact : activeTerm cs σ = some T) :
    resetX (fun v => if v ∈ freeVarsOf σ T then some (x v) else none) (descentSat cs w (F + 1) σ x)
      = descentSat cs w F (extendσ σ T x) x := by
  funext v
  simp only [resetX]
  by_cases hv : v ∈ freeVarsOf σ T
  · rw [if_pos hv]
    show some (x v) = descentSat cs w F (extendσ σ T x) x v
    exact (descentSat_extends cs w F (extendσ σ T x) x v (x v) (by rw [extendσ, if_pos hv])).symm
  · rw [if_neg hv]
    show descentSat cs w (F + 1) σ x v = descentSat cs w F (extendσ σ T x) x v
    rw [descentSat_succ_apply x hany hact, if_neg (not_cond_of_not_mem_free hv)]

/-- **End-to-end branching recovery.**  For a DNF of consistent terms, the label-aware peel of the
satisfying boundary `descentSat` recovers the descent's active-clause stream — for any `σ`. -/
theorem descent_recovery (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      descentPeel cs (descentSatMasks cs w F σ x) (descentSat cs w F σ x) = descentStream cs w F σ x := by
  intro F
  induction F with
  | zero => intro σ x; rw [descentSatMasks, descentPeel, descentStream]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true =>
      rw [show descentSatMasks cs w (F + 1) σ x = [] by rw [descentSatMasks]; simp [hany],
          show descentStream cs w (F + 1) σ x = [] by rw [descentStream]; simp [hany], descentPeel]
    | false =>
      cases hact : activeTerm cs σ with
      | none =>
        rw [show descentSatMasks cs w (F + 1) σ x = [] by rw [descentSatMasks]; simp [hany, hact],
            show descentStream cs w (F + 1) σ x = [] by rw [descentStream]; simp [hany, hact], descentPeel]
      | some T =>
        have hTcons : Consistent T := hcons T (activeTerm_mem hact)
        have hmask : descentSatMasks cs w (F + 1) σ x
            = (fun v => if v ∈ freeVarsOf σ T then some (x v) else none)
              :: descentSatMasks cs w F (extendσ σ T x) x := by
          rw [descentSatMasks]; simp only [hany, Bool.false_eq_true, if_false, hact]
        have hstream : descentStream cs w (F + 1) σ x = T :: descentStream cs w F (extendσ σ T x) x := by
          rw [descentStream]; simp only [hany, Bool.false_eq_true, if_false, hact]
        rw [hmask, hstream, descentPeel]
        simp only [descentSat_firstSat x hTcons hany hact, descentSat_step x hany hact,
          ih (extendσ σ T x) x]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_recovery
