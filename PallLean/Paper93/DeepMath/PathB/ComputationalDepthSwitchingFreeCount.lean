import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStable2

/-!
# Free-literal count drops by exactly one per within-clause step

**STATUS: REAL.  THE QUANTITATIVE CORE OF ITERATED STABILITY.**

For the decoder to recompute the active clause from the *end* state `σ_s`, the
active clause must stay `C` through all `s` steps — which needs the free-literal
count to stay `≥ 2` until the boundary.  That follows from the exact decrement:

* `litFree_falFix_eq`: `litFree (falFix σ ℓ) ℓ' = (litVar ℓ' ≠ litVar ℓ) ∧ litFree σ ℓ'`
  — a literal stays free iff it was free and lives on a different variable;
* `freeLits_actStep_length_eq`: a within-clause step removes exactly the head free
  literal, so `(freeLits (actStep cs σ) C).length + 1 = (freeLits σ C).length`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **How a step affects free-ness.**  A literal is free after the step iff it was
free before *and* lives on a different variable than the fixed one. -/
theorem litFree_falFix_eq {σ : Restriction n} {ℓ ℓ' : Rung4Literal n} :
    Depth3.litFree (falFix σ ℓ) ℓ'
      = (!decide (litVar ℓ' = litVar ℓ) && Depth3.litFree σ ℓ') := by
  by_cases hv : litVar ℓ' = litVar ℓ
  · have hl : Depth3.litFree (falFix σ ℓ) ℓ' = false := by
      rw [litFree_var, hv, falFix, Function.update_self]; rfl
    rw [hl]; simp [hv]
  · rw [litFree_falFix_ne hv]; simp [hv]

/-- Filtering by `litFree (falFix σ ℓ)` equals filtering by `litFree σ` then dropping
the literals on the fixed variable. -/
theorem filter_litFree_falFix (σ : Restriction n) (ℓ : Rung4Literal n)
    (L : List (Rung4Literal n)) :
    L.filter (Depth3.litFree (falFix σ ℓ))
      = (L.filter (Depth3.litFree σ)).filter (fun a => !decide (litVar a = litVar ℓ)) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filter_cons, litFree_falFix_eq, List.filter_cons]
    by_cases hf : Depth3.litFree σ a = true
    · by_cases hv : litVar a = litVar ℓ
      · simp [hf, hv, ih]
      · simp [hf, hv, List.filter_cons, ih]
    · simp only [Bool.not_eq_true] at hf
      simp [hf, ih]

/-- **Exact free-count decrement.**  A within-clause step removes exactly the head
free literal (the only literal of `C` on the fixed variable, by distinct variables),
so the free count drops by exactly one. -/
theorem freeLits_actStep_length_eq {cs : List (Clause n)} {σ : Restriction n}
    {C : Clause n} (hnodup : (C.lits.map litVar).Nodup)
    (hC : activeClause cs σ = some C) (hlen : 1 < (freeLits σ C).length) :
    (freeLits (actStep cs σ) C).length + 1 = (freeLits σ C).length := by
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp (activeLit_isSome hC)
  have hstep : actStep cs σ = falFix σ ℓ := by rw [actStep, hℓ]
  have hℓhead : (freeLits σ C).head? = some ℓ := by
    unfold activeLit at hℓ; rw [hC] at hℓ; exact hℓ
  -- `freeLits σ C = ℓ :: rest`
  obtain ⟨rest, hrest⟩ : ∃ rest, freeLits σ C = ℓ :: rest := by
    obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil
      (l := freeLits σ C) (by intro h; rw [h] at hlen; simp at hlen)
    have ha : a = ℓ := by rw [hat] at hℓhead; simpa using hℓhead
    exact ⟨t, by rw [hat, ha]⟩
  -- the step's free set is `rest`
  have hfree_eq : freeLits (actStep cs σ) C = rest := by
    rw [hstep, freeLits, filter_litFree_falFix, ← freeLits, hrest, List.filter_cons]
    have hℓdrop : (!decide (litVar ℓ = litVar ℓ)) = false := by simp
    rw [hℓdrop, if_neg (by simp)]
    -- every literal of `rest` lives on a different variable than `ℓ`
    have hndF : (freeLits σ C).Nodup := (List.Nodup.of_map litVar hnodup).filter _
    rw [hrest] at hndF
    refine List.filter_eq_self.mpr (fun a ha => ?_)
    have hane : a ≠ ℓ := fun h => (List.nodup_cons.mp hndF).1 (h ▸ ha)
    have haC : a ∈ C.lits := by
      have : a ∈ freeLits σ C := by rw [hrest]; exact List.mem_cons.mpr (Or.inr ha)
      exact (List.mem_filter.mp this).1
    have hℓC : ℓ ∈ C.lits := by
      have : ℓ ∈ freeLits σ C := by rw [hrest]; exact List.mem_cons.mpr (Or.inl rfl)
      exact (List.mem_filter.mp this).1
    have : litVar a ≠ litVar ℓ := fun hv =>
      hane (List.inj_on_of_nodup_map hnodup haC hℓC hv)
    simp [this]
  rw [hfree_eq, hrest]; simp

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.litFree_falFix_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeLits_actStep_length_eq
