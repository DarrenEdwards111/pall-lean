import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfy

/-!
# Pure-satisfy regime: the satisfy variables are confined to the constant clause

`activeTerm_deepestEnd_pure_satisfy` showed a pure-satisfy run keeps one clause `T₀` active to the
leaf.  This file proves the matching set fact: **every satisfy variable lies in `T₀`**.  Each satisfy
step's variable is `litVar ℓ` for the active literal `ℓ` of the (constant) active clause `T₀`, hence a
variable of `T₀`.

* `clauseVars T` — the variable set of a clause, `(T.lits.map litVar).toFinset`.
* `deepestSatSel_subset_clauseVars` — in the pure-satisfy regime, `deepestSatSel cs F σ ⊆ clauseVars T`,
  where `T = activeTerm cs σ` is the constant active clause.

Combined with `deepestSel_eq_satSel_of_pure_satisfy` and `activeTerm_deepestEnd_pure_satisfy`, this
pins the entire selected set inside the single clause `T₀ = activeTerm cs (deepestEnd cs F σ)`: the
decoder identifies `T₀` from the leaf and the satisfy-recovery engine (`satVar_recover`,
`clauseLitAt`) reads each variable off `T₀` at its labelled position.  The remaining step is only the
`PathLabel w s` position packaging (the same bookkeeping as the `canonMarkLabel`/`flatToLabel` route);
no new active-clause identification is needed in this regime.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The variable set of a clause. -/
def clauseVars (T : Clause n) : Finset (Fin n) := (T.lits.map litVar).toFinset

theorem mem_clauseVars {T : Clause n} {ℓ : Rung4Literal n} (h : ℓ ∈ T.lits) :
    litVar ℓ ∈ clauseVars T :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨ℓ, h, rfl⟩)

/-- **The satisfy variables are confined to the constant clause.**  In the pure-satisfy regime (no
falsify steps, clean clause, leaf unsatisfied), every variable of `deepestSatSel cs F σ` is a variable
of the active clause `T = activeTerm cs σ` — which stays active throughout
(`activeTerm_deepestEnd_pure_satisfy`). -/
theorem deepestSatSel_subset_clauseVars (cs : List (Clause n)) {T : Clause n}
    (hclean : CleanClause T) :
    ∀ (F : ℕ) (σ : Restriction n),
      SwitchingCounting.activeTerm cs σ = some T →
      deepestFalSel cs F σ = ∅ →
      SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false →
      deepestSatSel cs F σ ⊆ clauseVars T := by
  intro F
  induction F with
  | zero => intro σ _ _ _; rw [deepestSatSel]; exact Finset.empty_subset _
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
    -- the recursive subset, after a satisfy step in bit `b`
    have body : ∀ b : Bool,
        deepestFalSel cs F (fixVar σ (litVar ℓ) b) = ∅ →
        SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = false →
        SwitchingCounting.anyTermSat cs (deepestEnd cs F (fixVar σ (litVar ℓ) b)) = false →
        deepestSatSel cs F (fixVar σ (litVar ℓ) b) ⊆ clauseVars T := by
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
      rw [deepestEnd] at hsat
      rw [deepestSatSel]
      simp only [hns, Bool.false_eq_true, if_false, hact, hℓhead] at hfal hsat ⊢
      rw [if_pos hd] at hfal hsat ⊢
      by_cases hh : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ = true
      · rw [if_pos hh] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
      · rw [Bool.not_eq_true] at hh
        rw [if_neg (by rw [hh]; simp), id_eq] at hfal
        rw [if_neg (by rw [hh]; simp)]
        exact Finset.insert_subset (mem_clauseVars hℓT) (body false hfal hh hsat)
    · -- `b = true`
      rw [deepestFalSel] at hfal
      rw [deepestEnd] at hsat
      rw [deepestSatSel]
      simp only [hns, Bool.false_eq_true, if_false, hact, hℓhead] at hfal hsat ⊢
      rw [if_neg hd] at hfal hsat ⊢
      by_cases hh : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ = true
      · rw [if_pos hh] at hfal; exact absurd hfal (Finset.insert_ne_empty _ _)
      · rw [Bool.not_eq_true] at hh
        rw [if_neg (by rw [hh]; simp), id_eq] at hfal
        rw [if_neg (by rw [hh]; simp)]
        exact Finset.insert_subset (mem_clauseVars hℓT) (body true hfal hh hsat)

/-- **The whole selected set is confined to the constant clause.**  Combining the partition
(`deepestSel = deepestSatSel`) with the confinement: in the pure-satisfy regime, `deepestSel cs F σ`
lies entirely inside `clauseVars T` for the constant active clause `T`. -/
theorem deepestSel_subset_clauseVars_of_pure_satisfy (cs : List (Clause n)) {T : Clause n}
    (hclean : CleanClause T) (F : ℕ) (σ : Restriction n)
    (hact : SwitchingCounting.activeTerm cs σ = some T) (hfal : deepestFalSel cs F σ = ∅)
    (hsat : SwitchingCounting.anyTermSat cs (deepestEnd cs F σ) = false) :
    deepestSel cs F σ ⊆ clauseVars T := by
  rw [deepestSel_eq_satSel_of_pure_satisfy cs F σ hfal]
  exact deepestSatSel_subset_clauseVars cs hclean F σ hact hfal hsat

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSel_subset_clauseVars
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSel_subset_clauseVars_of_pure_satisfy
