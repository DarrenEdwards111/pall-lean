import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FilterFalsified

/-!
# Tight switching, step 8: `deepestSel` ignores ρ-falsified clauses (branch `razborov-recoverRho-wip`)

The `hnf`-free reconstruction's *target*-side invariance.  `deepestSel` (the selected variables of the
canonical deepest branch — the set the decoder must recover) has the same control flow as `deepestEnd`,
so like `deepestEnd_eq_filter`/`deepestFullSeq_eq_filter` it is invariant under removing ρ-falsified
clauses: `deepestSel cs ρ = deepestSel (cs.filter live) ρ`.

This is the `RHS` of a `hnf`-free `deepestSel_recovered`: the recovered set equals that of the live sublist
`cs'` (which is alive, `hnf_filter`).  Together with the *decoder*-side invariances (`decodedSel`,
`recoverStream`, `fullReplaySatPar` — the harder forward-scan pieces, still to do) it would make the
reconstruction `hnf`-free, closing the alive condition for the tight count.

* `deepestSel_eq_filter` — `deepestSel cs σ = deepestSel (cs.filter live) σ` (for `σ` falsifying ⊇ ρ).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The selected set ignores ρ-falsified clauses.**  `deepestSel cs σ` equals that of the ρ-live
sublist, by the same control-flow argument as `deepestEnd_eq_filter`. -/
theorem deepestSel_eq_filter (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ (F : ℕ) (σ : Restriction n),
      (∀ T, SwitchingCounting.termFalsified ρ T = true →
        SwitchingCounting.termFalsified σ T = true) →
      deepestSel cs F σ
        = deepestSel (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) F σ := by
  intro F
  induction F with
  | zero => intro σ _; rfl
  | succ F ih =>
    intro σ hinv
    rw [deepestSel, deepestSel, anyTermSat_filter_eq hinv, activeTerm_filter_eq hinv]
    cases hb : SwitchingCounting.anyTermSat cs σ with
    | true => simp only [if_true]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hT : SwitchingCounting.activeTerm cs σ with
      | none => rfl
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp only [hh]
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hT]; exact hh
          have hv : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          simp only [hh,
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv)]

/-- The selected set of `cs` equals that of its ρ-live sublist (the canonical `ρ = σ` instance). -/
theorem deepestSel_eq_filter_self (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) :
    deepestSel cs F ρ
      = deepestSel (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) F ρ :=
  deepestSel_eq_filter cs ρ F ρ (fun _ h => h)

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSel_eq_filter
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSel_eq_filter_self
