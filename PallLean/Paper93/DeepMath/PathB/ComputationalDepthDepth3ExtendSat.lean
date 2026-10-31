import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CodeCard
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalComplete

/-!
# Block-DT model, route-2 step 1: `codesList` block count is F-independent (branch `razborov-recoverRho-wip`)

The first brick of **route 2** — making the *depth-graded* `descent_switching_prob` `F`-independent.  Its label
space is currently `(4^w+1)^F` because `codesList` is bounded by the fuel `F` (`codesList_length_le`).  Here we
bound the block count by `pathLen` instead — `F`-independently.

The subtlety: `codesList` *continues* past a satisfying step (it always conses), whereas `pathLen` *stops*.
They agree because once a step's `extendσ` makes the active term `T` true, the boundary is satisfied
(`anyTermSat`), so the next `codesList` call returns `[]`.  That satisfaction fact is the content here.

* `extendσ_anyTermSat_of_allTrue` — if the active term's free literals all evaluate true under `x`, then
  `extendσ σ T x` satisfies the clause family (`anyTermSat = true`).
* `codesList_length_le_pathLen` — `(codesList cs w F σ x).length ≤ pathLen cs w F σ x`, `F`-independent.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The satisfying step satisfies the active term.**  If `T` is the active term and its free literals all
evaluate `true` under `x`, then `extendσ σ T x` makes `T` true, so some term is satisfied. -/
theorem extendσ_anyTermSat_of_allTrue {cs : List (Clause n)} {σ : Fin n → Option Bool}
    {T : Clause n} {x : Fin n → Bool} (hact : activeTerm cs σ = some T)
    (hall : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true) :
    anyTermSat cs (extendσ σ T x) = true := by
  -- `T` is not falsified under `σ` (it is the `find?` result).
  have hns : anyTermSat cs σ = false := activeTerm_anyTermSat_false hact
  have hpred : (!termFalsified σ T && decide (0 < (freeLits σ T).length)) = true := by
    have := List.find?_some (activeTerm_eq_find hns ▸ hact); simpa using this
  have hnf : termFalsified σ T = false := by
    rw [Bool.and_eq_true] at hpred; simpa using hpred.1
  -- `extendσ σ T x` satisfies `T`.
  have hsat : termSat (extendσ σ T x) T = true := by
    rw [termSat, List.all_eq_true]
    intro ℓ hℓ
    have hfalseℓ : litFalse σ ℓ = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have hcon : termFalsified σ T = true := by
        rw [termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓ, hc⟩
      rw [hcon] at hnf; exact absurd hnf (by simp)
    cases ℓ with
    | pos v =>
      show Depth3.litTrue (extendσ σ T x) (Rung4Literal.pos v) = true
      simp only [Depth3.litTrue, Depth3.litFixedVal, extendσ]
      by_cases hsv : σ v = none
      · have hmem : v ∈ freeVarsOf σ T :=
          List.mem_filterMap.mpr ⟨Rung4Literal.pos v, hℓ, by simp [litVarOf, hsv]⟩
        have hin : Rung4Literal.pos v ∈ T.lits.filter (DTree.freeLit σ) :=
          List.mem_filter.mpr ⟨hℓ, by simp [DTree.freeLit, hsv]⟩
        have hev : x v = true := by
          have := (List.all_eq_true.mp hall) _ hin; simpa [Rung4Literal.eval] using this
        rw [if_pos hmem]; simp [hev]
      · have hmem : v ∉ freeVarsOf σ T := fun hc => hsv (mem_freeVarsOf_none hc)
        rw [if_neg hmem]
        rw [litFalse, Depth3.litFixedVal] at hfalseℓ
        cases hsv2 : σ v with
        | none => exact absurd hsv2 hsv
        | some b => cases b with
          | true => simp
          | false => rw [hsv2] at hfalseℓ; simp at hfalseℓ
    | neg v =>
      show Depth3.litTrue (extendσ σ T x) (Rung4Literal.neg v) = true
      simp only [Depth3.litTrue, Depth3.litFixedVal, extendσ]
      by_cases hsv : σ v = none
      · have hmem : v ∈ freeVarsOf σ T :=
          List.mem_filterMap.mpr ⟨Rung4Literal.neg v, hℓ, by simp [litVarOf, hsv]⟩
        have hin : Rung4Literal.neg v ∈ T.lits.filter (DTree.freeLit σ) :=
          List.mem_filter.mpr ⟨hℓ, by simp [DTree.freeLit, hsv]⟩
        have hev : x v = false := by
          have := (List.all_eq_true.mp hall) _ hin; simpa [Rung4Literal.eval] using this
        rw [if_pos hmem]; simp [hev]
      · have hmem : v ∉ freeVarsOf σ T := fun hc => hsv (mem_freeVarsOf_none hc)
        rw [if_neg hmem]
        rw [litFalse, Depth3.litFixedVal] at hfalseℓ
        cases hsv2 : σ v with
        | none => exact absurd hsv2 hsv
        | some b => cases b with
          | false => simp
          | true => rw [hsv2] at hfalseℓ; simp at hfalseℓ
  rw [anyTermSat, List.any_eq_true]
  exact ⟨T, activeTerm_mem hact, hsat⟩

/-- **The `codesList` block count is `F`-independent.**  It is bounded by `pathLen` (the total stars freed),
not the fuel `F`. -/
theorem codesList_length_le_pathLen (cs : List (Clause n)) (w : ℕ) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (x : Fin n → Bool),
      (codesList cs w F σ x).length ≤ pathLen cs w F σ x := by
  intro F
  induction F with
  | zero => intro σ x; simp [codesList, pathLen]
  | succ F ih =>
    intro σ x
    cases hany : anyTermSat cs σ with
    | true => rw [codesList, pathLen]; simp [hany]
    | false =>
      cases hact : activeTerm cs σ with
      | none => rw [codesList, pathLen]; simp [hany, hact]
      | some T =>
        have hcl : (codesList cs w (F + 1) σ x).length
            = 1 + (codesList cs w F (extendσ σ T x) x).length := by
          rw [codesList]; simp only [hany, Bool.false_eq_true, if_false, hact, List.length_cons]; omega
        have hpl : pathLen cs w (F + 1) σ x = (freeVarsOf σ T).length
            + (if (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) then 0
               else pathLen cs w F (extendσ σ T x) x) := by
          rw [pathLen]; simp only [hany, Bool.false_eq_true, if_false, hact]
        obtain ⟨v, hvfree, _⟩ := activeTerm_exists_free hact
        have hfvpos : 1 ≤ (freeVarsOf σ T).length := List.length_pos_of_mem hvfree
        rw [hcl, hpl]
        by_cases hsat : (T.lits.filter (DTree.freeLit σ)).all (fun ℓ => Rung4Literal.eval ℓ x) = true
        · rw [if_pos hsat]
          have hempty : codesList cs w F (extendσ σ T x) x = [] := by
            cases F with
            | zero => rfl
            | succ F' => rw [codesList]; simp [extendσ_anyTermSat_of_allTrue hact hsat]
          rw [hempty]; simp; omega
        · rw [if_neg hsat]
          have := ih (extendσ σ T x) x
          omega

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.codesList_length_le_pathLen
