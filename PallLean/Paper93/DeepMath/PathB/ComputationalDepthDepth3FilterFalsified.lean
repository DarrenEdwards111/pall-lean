import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FalsifiedMonotone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ForwardScan
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFullSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPositionLit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FullReplayCorrect

/-!
# Reducing falsifying restrictions to the live case (branch only)

The reconstruction-based switching count requires the restriction `ρ` to *falsify no clause* (`hnf`).
A general `ρ` may falsify some clauses — but a clause falsified by `ρ` stays falsified along the whole
canonical descent (`termFalsified_deepestStep_stable`), so it is **never the active term** and the
descent simply *skips* it.  Hence the canonical tree of `cs` at `ρ` equals the canonical tree of the
**sublist of `ρ`-live clauses**

  `cs' := cs.filter (fun T => !termFalsified ρ T)`,

on which `ρ` falsifies nothing by construction.  This is the honest reduction of the falsifying case
to the live (`hnf`) case:

* `canonicalDT_eq_filter` — `canonicalDT cs F σ = canonicalDT cs' F σ` (so depths agree).
* `hnf_filter` — `ρ` falsifies no clause of `cs'`.

So `depth`-counting a general `ρ` reduces, *for that `ρ`*, to the live count for `cs'`.

**Honest scope.**  `cs'` depends on `ρ` (which clauses it kills), so turning this into a single family
count means grouping the family by the killed-clause set and applying the live count per group — which
costs a factor in the number of distinct live-sublists (≤ `2^|cs|` naively).  Removing that factor is
the tight-encoding content (recording the active clause in the label), still open.  This file proves
the reduction itself, not the tight assembly.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP
untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- A falsified term is not satisfied. -/
theorem termSat_false_of_termFalsified {σ : Restriction n} {T : Clause n}
    (h : SwitchingCounting.termFalsified σ T = true) : SwitchingCounting.termSat σ T = false := by
  rw [SwitchingCounting.termFalsified, List.any_eq_true] at h
  obtain ⟨ℓ, hℓ, hf⟩ := h
  rw [SwitchingCounting.termSat, List.all_eq_false]
  exact ⟨ℓ, hℓ, by simp [SwitchingCounting.litTrue_eq_false_of_litFalse hf]⟩

/-- `List.find?` is unchanged by filtering out elements that anyway fail the predicate. -/
theorem find?_filter_eq_of {α : Type*} {p q : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = false → q x = false) →
      (l.filter p).find? q = l.find? q
  | [], _ => rfl
  | x :: t, h => by
    have ht : (∀ y ∈ t, p y = false → q y = false) :=
      fun y hy => h y (List.mem_cons_of_mem x hy)
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp]
      by_cases hq : q x = true
      · rw [List.find?_cons_of_pos hq, List.find?_cons_of_pos hq]
      · rw [List.find?_cons_of_neg hq, List.find?_cons_of_neg hq, find?_filter_eq_of t ht]
    · have hpf : p x = false := by simpa using hp
      rw [List.filter_cons_of_neg (by simp [hpf]),
          List.find?_cons_of_neg (by rw [h x List.mem_cons_self hpf]; simp),
          find?_filter_eq_of t ht]

/-- `List.any` is unchanged by filtering out elements that anyway fail the predicate. -/
theorem any_filter_eq_of {α : Type*} {p r : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = false → r x = false) →
      (l.filter p).any r = l.any r
  | [], _ => rfl
  | x :: t, h => by
    have ht : (∀ y ∈ t, p y = false → r y = false) :=
      fun y hy => h y (List.mem_cons_of_mem x hy)
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.any_cons, List.any_cons, any_filter_eq_of t ht]
    · have hpf : p x = false := by simpa using hp
      rw [List.filter_cons_of_neg (by simp [hpf]), List.any_cons,
          h x List.mem_cons_self hpf, Bool.false_or, any_filter_eq_of t ht]

/-- The `ρ`-live filter does not change which terms are satisfied: removed (`ρ`-falsified) terms are
falsified at any extension `σ` of the falsified set, hence unsatisfied. -/
theorem anyTermSat_filter_eq {cs : List (Clause n)} {ρ σ : Restriction n}
    (hinv : ∀ T, SwitchingCounting.termFalsified ρ T = true →
      SwitchingCounting.termFalsified σ T = true) :
    SwitchingCounting.anyTermSat (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) σ
      = SwitchingCounting.anyTermSat cs σ := by
  unfold SwitchingCounting.anyTermSat
  apply any_filter_eq_of
  intro T _ hp
  have hρT : SwitchingCounting.termFalsified ρ T = true := by simpa using hp
  exact termSat_false_of_termFalsified (hinv T hρT)

/-- The `ρ`-live filter does not change the active term: removed terms are falsified at `σ`, so they
fail the active predicate. -/
theorem activeTerm_filter_eq {cs : List (Clause n)} {ρ σ : Restriction n}
    (hinv : ∀ T, SwitchingCounting.termFalsified ρ T = true →
      SwitchingCounting.termFalsified σ T = true) :
    SwitchingCounting.activeTerm (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) σ
      = SwitchingCounting.activeTerm cs σ := by
  unfold SwitchingCounting.activeTerm
  rw [anyTermSat_filter_eq hinv]
  cases hb : SwitchingCounting.anyTermSat cs σ with
  | true => rfl
  | false =>
    simp only [cond_false]
    apply find?_filter_eq_of
    intro T _ hp
    have hρT : SwitchingCounting.termFalsified ρ T = true := by simpa using hp
    have hσT : SwitchingCounting.termFalsified σ T = true := hinv T hρT
    simp [hσT]

/-- The active literal's variable is free at the descent state. -/
private theorem head_free {σ : Restriction n} {T : Clause n} {ℓ : Rung4Literal n}
    (hh : (SwitchingCounting.freeLits σ T).head? = some ℓ) : σ (litVar ℓ) = none := by
  have hmem : ℓ ∈ SwitchingCounting.freeLits σ T := List.mem_of_mem_head? hh
  have hfree : Depth3.litFree σ ℓ = true := (List.mem_filter.mp hmem).2
  rw [litFree_var] at hfree
  cases hx : σ (litVar ℓ) with
  | none => rfl
  | some _ => rw [hx] at hfree; simp at hfree

/-- **The canonical tree ignores `ρ`-falsified clauses.**  For any `σ` falsifying everything `ρ`
falsifies, the canonical tree of `cs` equals that of the `ρ`-live sublist `cs'`.  (Falsified clauses
are permanently skipped, so they never affect the active term; the invariant is preserved at each step
because fixing a free variable preserves falsification.) -/
theorem canonicalDT_eq_filter (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ (F : ℕ) (σ : Restriction n),
      (∀ T, SwitchingCounting.termFalsified ρ T = true →
        SwitchingCounting.termFalsified σ T = true) →
      canonicalDT cs F σ
        = canonicalDT (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) F σ := by
  intro F
  induction F with
  | zero =>
    intro σ hinv
    simp only [canonicalDT]
    rw [anyTermSat_filter_eq hinv]
  | succ F ih =>
    intro σ hinv
    rw [canonicalDT, canonicalDT, anyTermSat_filter_eq hinv, activeTerm_filter_eq hinv]
    cases hb : SwitchingCounting.anyTermSat cs σ with
    | true => simp only [if_true]
    | false =>
      simp only [hb, Bool.false_eq_true, if_false]
      cases hT : SwitchingCounting.activeTerm cs σ with
      | none => simp only [hT]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp only [hT, hh]
        | some ℓ =>
          have hv : σ (litVar ℓ) = none := head_free hh
          simp only [hT, hh,
            ih (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv)]

/-- **Depth reduction.**  The canonical tree *depth* of `cs` at `ρ` equals that of the `ρ`-live
sublist `cs'`. -/
theorem canonicalDT_depth_eq_filter (cs : List (Clause n)) (F : ℕ) (ρ : Restriction n) :
    (canonicalDT cs F ρ).depth
      = (canonicalDT (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) F ρ).depth := by
  rw [canonicalDT_eq_filter cs ρ F ρ (fun _ h => h)]

/-- **The leaf ignores `ρ`-falsified clauses.**  The deepest end-state of `cs` equals that of the
`ρ`-live sublist `cs'` (the `if` depth-comparison agrees by `canonicalDT_eq_filter`). -/
theorem deepestEnd_eq_filter (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ (F : ℕ) (σ : Restriction n),
      (∀ T, SwitchingCounting.termFalsified ρ T = true →
        SwitchingCounting.termFalsified σ T = true) →
      deepestEnd cs F σ
        = deepestEnd (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) F σ := by
  intro F
  induction F with
  | zero => intro σ _; rfl
  | succ F ih =>
    intro σ hinv
    rw [deepestEnd, deepestEnd, anyTermSat_filter_eq hinv, activeTerm_filter_eq hinv]
    cases hb : SwitchingCounting.anyTermSat cs σ with
    | true => simp only [if_true]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hT : SwitchingCounting.activeTerm cs σ with
      | none => simp only [hT]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp only [hT, hh]
        | some ℓ =>
          have hv : σ (litVar ℓ) = none := head_free hh
          simp only [hT, hh,
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv)]

/-- The active *literal* is unchanged by the `ρ`-live filter (it depends on `cs` only through the
active term). -/
theorem activeTermLit_filter_eq {cs : List (Clause n)} {ρ σ : Restriction n}
    (hinv : ∀ T, SwitchingCounting.termFalsified ρ T = true →
      SwitchingCounting.termFalsified σ T = true) :
    SwitchingCounting.activeTermLit (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) σ
      = SwitchingCounting.activeTermLit cs σ := by
  unfold SwitchingCounting.activeTermLit
  rw [activeTerm_filter_eq hinv]

/-- The pivot position is unchanged by the `ρ`-live filter. -/
theorem pivotPosOf_filter_eq {cs : List (Clause n)} {ρ σ : Restriction n}
    (hinv : ∀ T, SwitchingCounting.termFalsified ρ T = true →
      SwitchingCounting.termFalsified σ T = true) :
    SwitchingCounting.pivotPosOf (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) σ
      = SwitchingCounting.pivotPosOf cs σ := by
  unfold SwitchingCounting.pivotPosOf
  rw [activeTerm_filter_eq hinv, activeTermLit_filter_eq hinv]

/-- **The full path ignores `ρ`-falsified clauses.**  The recorded deepest full path of `cs` equals
that of the `ρ`-live sublist `cs'` (same active terms, same pivot positions, same depth comparison). -/
theorem deepestFullSeq_eq_filter (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ (F : ℕ) (σ : Restriction n),
      (∀ T, SwitchingCounting.termFalsified ρ T = true →
        SwitchingCounting.termFalsified σ T = true) →
      deepestFullSeq cs F σ
        = deepestFullSeq (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) F σ := by
  intro F
  induction F with
  | zero => intro σ _; rfl
  | succ F ih =>
    intro σ hinv
    rw [deepestFullSeq, deepestFullSeq, anyTermSat_filter_eq hinv, activeTerm_filter_eq hinv]
    cases hb : SwitchingCounting.anyTermSat cs σ with
    | true => simp only [if_true]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hT : SwitchingCounting.activeTerm cs σ with
      | none => simp only [hT]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp only [hT, hh]
        | some ℓ =>
          have hv : σ (litVar ℓ) = none := head_free hh
          simp only [hT, hh, pivotPosOf_filter_eq hinv,
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv)]

/-- **The active-clause stream ignores `ρ`-falsified clauses.**  The active-clause stream of `cs` at
`σ` equals that of the `ρ`-live sublist `cs'`.  This is the quantity the reconstruction actually
recovers, so the *entire* reconstruction pipeline for `ρ` on `cs` coincides with that on `cs'`. -/
theorem activeStreamPar_eq_filter (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ (F : ℕ) (σ : Restriction n),
      (∀ T, SwitchingCounting.termFalsified ρ T = true →
        SwitchingCounting.termFalsified σ T = true) →
      activeStreamPar cs F σ
        = activeStreamPar (cs.filter (fun T => !SwitchingCounting.termFalsified ρ T)) F σ := by
  intro F
  induction F with
  | zero => intro σ _; rfl
  | succ F ih =>
    intro σ hinv
    rw [activeStreamPar, activeStreamPar, anyTermSat_filter_eq hinv, activeTerm_filter_eq hinv]
    cases hb : SwitchingCounting.anyTermSat cs σ with
    | true => simp only [if_true]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hT : SwitchingCounting.activeTerm cs σ with
      | none => simp only [hT]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp only [hT, hh]
        | some ℓ =>
          have hv : σ (litVar ℓ) = none := head_free hh
          simp only [hT, hh,
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            canonicalDT_eq_filter cs ρ F (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) false)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv),
            ih (fixVar σ (litVar ℓ) true)
              (fun U hU => termFalsified_fixVar_of_free (hinv U hU) hv)]

/-- **The reduction lands in the live case.**  `ρ` falsifies no clause of its live sublist `cs'`. -/
theorem hnf_filter (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ T ∈ cs.filter (fun T => !SwitchingCounting.termFalsified ρ T),
      SwitchingCounting.termFalsified ρ T = false := by
  intro T hT
  have := (List.mem_filter.mp hT).2
  simpa using this

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_eq_filter
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.canonicalDT_depth_eq_filter
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hnf_filter
