import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Threading
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ActiveMonotone

/-!
# The pure-satisfy regime: the active clause is constant, and `deepestSel = deepestSatSel`

The **pure-satisfy regime** is the deepest branch with no falsify steps (`deepestFalSel cs F ρ = ∅`).
There the recovery closes cleanly: every step advances *within one clause* `T₀`, so the active clause
is **constant** along the whole branch, the backward scan needs no clause sequencing, and the satisfy
variables are read off that single clause via the position label.

This file proves the structural heart — **iterated advance-stability**: under a clause-cleanliness
condition (no literal repeats a variable in a clause, so a satisfy step cannot falsify its own clause),
a pure-satisfy run that does not satisfy its clause keeps that clause active to the leaf.

* `CleanClause T` — no two literals of `T` share a variable (so setting one literal true leaves the
  others untouched; the satisfy step never falsifies `T`).
* `deepestEnd_of_anyTermSat` / `anyTermSat_of_deepestEnd_false` — the path stops at the first satisfied
  state, so "the leaf is unsatisfied" propagates back to *every* intermediate state.
* `termFalsified_satisfy_step` — under `CleanClause T`, a satisfy step leaves `T` non-falsified.
* `activeTerm_deepestEnd_pure_satisfy` — **iterated advance-stability**: `activeTerm cs σ = some T`,
  `CleanClause T`, `deepestFalSel cs F σ = ∅`, and the leaf unsatisfied ⟹
  `activeTerm cs (deepestEnd cs F σ) = some T`.  So the active clause is the *same* `T` at the leaf.
* `deepestSel_eq_satSel_of_pure_satisfy` — in the pure-satisfy regime `deepestSel = deepestSatSel`
  (no falsify part), so the satisfy decoder recovers the *whole* selected set.

So in the pure-satisfy regime the open "active-clause identification" is trivial — the active clause
is the constant `T₀ = activeTerm cs (deepestEnd cs F ρ)` — and the satisfy-recovery engine
(`satVar_recover`, `clauseLitAt`) reads each variable off `T₀` at its labelled position.  The general
interleaved case (falsify steps moving the active clause) is unchanged and not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A clause is **clean** if no two of its literals share a variable.  Then fixing one literal's
variable touches no other literal of the clause — a satisfy step cannot falsify the clause. -/
def CleanClause (T : Clause n) : Prop :=
  ∀ m ∈ T.lits, ∀ m' ∈ T.lits, litVar m = litVar m' → m = m'

/-- **The path stops at the first satisfied state.**  If some term is satisfied at `σ`, the deepest
branch halts immediately, so the end-state is `σ`. -/
theorem deepestEnd_of_anyTermSat (cs : List (Clause n)) {σ : Restriction n}
    (h : SwitchingCounting.anyTermSat cs σ = true) : ∀ F, deepestEnd cs F σ = σ
  | 0 => rfl
  | _ + 1 => by rw [deepestEnd]; simp [h]

/-- **The leaf-unsatisfied condition propagates back.**  If the end-state is unsatisfied then `σ`
itself was unsatisfied (else the path would have stopped at `σ`, making the leaf satisfied). -/
theorem anyTermSat_of_deepestEnd_false (cs : List (Clause n)) (F : ℕ) (σ : Restriction n)
    (h : SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false) :
    SwitchingCounting.anyTermSat cs σ = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  rw [deepestEnd_of_anyTermSat cs hc F, hc] at h
  exact absurd h (by simp)

/-- **A satisfy step does not falsify a clean clause.**  Under `CleanClause T`, fixing the active
literal's variable so the active literal is not false leaves every literal of `T` non-false. -/
theorem termFalsified_satisfy_step {cs : List (Clause n)} {σ : Restriction n} {T : Clause n}
    {ℓ : Rung4Literal n} {b : Bool} (hact : SwitchingCounting.activeTerm cs σ = some T)
    (hclean : CleanClause T) (hℓ : ℓ ∈ T.lits)
    (hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = false) :
    SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) T = false := by
  have hTσ : SwitchingCounting.termFalsified σ T = false := (SwitchingCounting.activeTerm_pred hact).1
  rw [SwitchingCounting.termFalsified, List.any_eq_false] at hTσ ⊢
  intro m hm hcontra
  by_cases hv : litVar m = litVar ℓ
  · have hmℓ : m = ℓ := hclean m hm ℓ hℓ hv
    rw [hmℓ, hf] at hcontra; exact absurd hcontra (by simp)
  · have hval : fixVar σ (litVar ℓ) b (litVar m) = σ (litVar m) := by
      rw [fixVar]; exact Function.update_of_ne hv _ _
    rw [SwitchingCounting.litFalse_eq_of_litVar_val hval] at hcontra
    exact hTσ m hm hcontra

/-- **Iterated advance-stability (the pure-satisfy heart).**  If `T` is the active clause under `σ`,
`T` is clean, the run from `σ` has *no* falsify step, and the leaf is unsatisfied, then `T` is still
the active clause at the leaf `deepestEnd cs F σ`.  So a pure-satisfy run stays in one clause. -/
theorem activeTerm_deepestEnd_pure_satisfy (cs : List (Clause n)) {T : Clause n}
    (hclean : CleanClause T) :
    ∀ (F : ℕ) (σ : Restriction n),
      SwitchingCounting.activeTerm cs σ = some T →
      deepestFalSel cs F σ = ∅ →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false →
      SwitchingCounting.activeTerm cs (deepestEnd cs F σ) = some T := by
  intro F
  induction F with
  | zero => intro σ hact _ _; rw [deepestEnd]; exact hact
  | succ F ih =>
    intro σ hact hfal hsat
    have hns : SwitchingCounting.anyTermSat cs σ = false :=
      SwitchingCounting.activeTerm_anyTermSat_false hact
    obtain ⟨_, hTfree⟩ := SwitchingCounting.activeTerm_pred hact
    obtain ⟨ℓ, hℓhead⟩ : ∃ ℓ, (SwitchingCounting.freeLits σ T).head? = some ℓ := by
      cases hh : SwitchingCounting.freeLits σ T with
      | nil => rw [hh] at hTfree; simp at hTfree
      | cons a _ => exact ⟨a, rfl⟩
    have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
      unfold SwitchingCounting.activeTermLit; rw [hact]; exact hℓhead
    have hℓT : ℓ ∈ T.lits := (List.mem_filter.mp (List.mem_of_mem_head? hℓhead)).1
    -- one step in bit `b`, given that step is a satisfy step and the leaf is unsatisfied
    have body : ∀ b : Bool,
        deepestFalSel cs F (fixVar σ (litVar ℓ) b) = ∅ →
        SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = false →
        SwitchingCounting.anyTermSat cs (deepestEnd cs F (fixVar σ (litVar ℓ) b)) = false →
        SwitchingCounting.activeTerm cs (deepestEnd cs F (fixVar σ (litVar ℓ) b)) = some T := by
      intro b hfal_b hf_b hsat_b
      have hns_b : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = false :=
        anyTermSat_of_deepestEnd_false cs F _ hsat_b
      have hnf_b : SwitchingCounting.termFalsified (fixVar σ (litVar ℓ) b) T = false :=
        termFalsified_satisfy_step hact hclean hℓT hf_b
      have hfree_b : 0 < (SwitchingCounting.freeLits (fixVar σ (litVar ℓ) b) T).length := by
        by_contra hc
        rw [Nat.not_lt, Nat.le_zero, List.length_eq_zero_iff] at hc
        have hsatU : SwitchingCounting.termSat (fixVar σ (litVar ℓ) b) T = false := by
          by_contra hs
          rw [Bool.not_eq_false] at hs
          have : SwitchingCounting.anyTermSat cs (fixVar σ (litVar ℓ) b) = true := by
            rw [SwitchingCounting.anyTermSat, List.any_eq_true]
            exact ⟨T, SwitchingCounting.activeTerm_mem hact, hs⟩
          rw [hns_b] at this; exact absurd this (by simp)
        have := SwitchingCounting.term_falsified_of_not_sat_no_free hsatU hc
        rw [this] at hnf_b; exact absurd hnf_b (by simp)
      exact ih _ (activeTerm_advance_stable hact hatl hns_b hnf_b hfree_b) hfal_b hsat_b
    by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
        (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
    · -- `b = false`
      rw [deepestFalSel] at hfal
      rw [deepestEnd] at hsat ⊢
      simp only [hns, Bool.false_eq_true, if_false, hact, hℓhead] at hfal hsat ⊢
      rw [if_pos hd] at hfal hsat ⊢
      by_cases hh : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ = true
      · rw [if_pos hh] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
      · rw [Bool.not_eq_true] at hh
        rw [if_neg (by rw [hh]; simp), id_eq] at hfal
        exact body false hfal hh hsat
    · -- `b = true`
      rw [deepestFalSel] at hfal
      rw [deepestEnd] at hsat ⊢
      simp only [hns, Bool.false_eq_true, if_false, hact, hℓhead] at hfal hsat ⊢
      rw [if_neg hd] at hfal hsat ⊢
      by_cases hh : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ = true
      · rw [if_pos hh] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
      · rw [Bool.not_eq_true] at hh
        rw [if_neg (by rw [hh]; simp), id_eq] at hfal
        exact body true hfal hh hsat

/-- **In the pure-satisfy regime the satisfy set is the whole selected set.**  With no falsify steps,
`deepestSel = deepestSatSel`, so recovering `deepestSatSel` recovers all of `deepestSel`. -/
theorem deepestSel_eq_satSel_of_pure_satisfy (cs : List (Clause n)) (F : ℕ) (σ : Restriction n)
    (h : deepestFalSel cs F σ = ∅) : deepestSel cs F σ = deepestSatSel cs F σ := by
  rw [deepestSel_eq_falSel_union_satSel, h, Finset.empty_union]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.termFalsified_satisfy_step
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.activeTerm_deepestEnd_pure_satisfy
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSel_eq_satSel_of_pure_satisfy
