import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActivePath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingStable

/-!
# Toward active-clause stability: `find?` stability + free-set shrinking

**STATUS: REAL.  REUSABLE LEMMAS FOR THE DECODER INVARIANT.**

Two building blocks for `activeClause_stable` (the decoder invariant that the
active clause does not move while it still has a free literal):

* `find?_stable`: if `find? p l = some C`, `p' C = true`, and `p'` is false wherever
  `p` is false, then `find? p' l = some C` — the active element is unchanged when the
  predicate is preserved on the discarded prefix and still holds on the target;
* `litFree_falFix_imp`: `falFix` shrinks the free set — a literal free after the step
  was free before — and `freeLits_falFix_subset` for the clause's free literals.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **`find?` stability.**  The found element is unchanged if the predicate stays
false on the discarded prefix and still holds on the target. -/
theorem find?_stable {α : Type*} {p p' : α → Bool} {l : List α} {C : α}
    (h : l.find? p = some C) (hp' : p' C = true)
    (hagree : ∀ x ∈ l, p x = false → p' x = false) : l.find? p' = some C := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.find?_cons] at h ⊢
    cases hpa : p a with
    | true =>
      simp only [hpa] at h
      obtain rfl : a = C := by simpa using h
      simp [hp']
    | false =>
      simp only [hpa] at h
      have hpa' : p' a = false := hagree a (List.mem_cons.mpr (Or.inl rfl)) hpa
      simp only [hpa']
      exact ih h (fun x hx hpx => hagree x (List.mem_cons.mpr (Or.inr hx)) hpx)

/-- `falFix` shrinks the free set: a literal free after the step was free before. -/
theorem litFree_falFix_imp {σ : Restriction n} {ℓ ℓ' : Rung4Literal n}
    (h : Depth3.litFree (falFix σ ℓ) ℓ' = true) : Depth3.litFree σ ℓ' = true := by
  by_cases hv : litVar ℓ' = litVar ℓ
  · rw [litFree_var, hv, falFix] at h
    simp [Function.update_self] at h
  · rw [litFree_var, falFix, Function.update_of_ne hv] at h
    rw [litFree_var]; exact h

/-- **The free set of a clause shrinks under a step.**  A literal of `C` free after
the step was free before — so `freeLits (falFix σ ℓ) C ⊆ freeLits σ C`.  In
particular, if `C` had no free literal, it still has none. -/
theorem freeLits_falFix_subset {σ : Restriction n} {ℓ : Rung4Literal n} {C : Clause n} :
    freeLits (falFix σ ℓ) C ⊆ freeLits σ C := by
  intro ℓ' h
  rw [freeLits, List.mem_filter] at h ⊢
  exact ⟨h.1, litFree_falFix_imp h.2⟩

/-- If a clause had no free literal, it still has none after a step. -/
theorem freeLits_falFix_eq_nil {σ : Restriction n} {ℓ : Rung4Literal n} {C : Clause n}
    (h : freeLits σ C = []) : freeLits (falFix σ ℓ) C = [] :=
  List.eq_nil_of_subset_nil (h ▸ freeLits_falFix_subset)

/-- A literal on a different variable than the fixed one keeps its free status. -/
theorem litFree_falFix_ne {σ : Restriction n} {ℓ ℓ' : Rung4Literal n}
    (hv : litVar ℓ' ≠ litVar ℓ) : Depth3.litFree (falFix σ ℓ) ℓ' = Depth3.litFree σ ℓ' := by
  rw [litFree_var, litFree_var, falFix, Function.update_of_ne hv]

/-- **A clause with `≥ 2` free literals still has one after a step.**  The active
literal `ℓ` is the *head* free literal; with distinct clause variables the *second*
free literal lives on a different variable, so it stays free under `falFix σ ℓ`. -/
theorem freeLits_falFix_ne_nil {σ : Restriction n} {C : Clause n} {ℓ : Rung4Literal n}
    (hnodup : (C.lits.map litVar).Nodup)
    (hℓ : (freeLits σ C).head? = some ℓ)
    (hlen : 1 < (freeLits σ C).length) :
    freeLits (falFix σ ℓ) C ≠ [] := by
  -- Expose the second free literal `ℓ₂`.
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil
    (l := freeLits σ C) (by intro h; rw [h] at hlen; simp at hlen)
  have ha : a = ℓ := by rw [hat] at hℓ; simpa using hℓ
  obtain ⟨ℓ₂, rest', hts⟩ := List.exists_cons_of_ne_nil
    (l := t) (by intro h; rw [hat, h] at hlen; simp at hlen)
  have hcons : freeLits σ C = ℓ :: ℓ₂ :: rest' := by rw [hat, hts, ha]
  have hmem2 : ℓ₂ ∈ freeLits σ C := by
    rw [hcons]; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemℓ : ℓ ∈ freeLits σ C := by rw [hcons]; exact List.mem_cons.mpr (Or.inl rfl)
  have hfree2 : Depth3.litFree σ ℓ₂ = true := (List.mem_filter.mp hmem2).2
  have hC2 : ℓ₂ ∈ C.lits := (List.mem_filter.mp hmem2).1
  have hCℓ : ℓ ∈ C.lits := (List.mem_filter.mp hmemℓ).1
  -- `ℓ ≠ ℓ₂` from `Nodup`, hence `litVar ℓ₂ ≠ litVar ℓ` by injectivity on `C.lits`.
  have hndF : (freeLits σ C).Nodup := (List.Nodup.of_map litVar hnodup).filter _
  rw [hcons] at hndF
  have hne : ℓ ≠ ℓ₂ := by
    intro h; rw [h] at hndF
    exact (List.nodup_cons.mp hndF).1 (List.mem_cons.mpr (Or.inl rfl))
  have hvne : litVar ℓ₂ ≠ litVar ℓ := fun hv =>
    hne (List.inj_on_of_nodup_map hnodup hCℓ hC2 hv.symm)
  -- `ℓ₂` stays free, so the free list is nonempty.
  intro hnil
  have : ℓ₂ ∈ freeLits (falFix σ ℓ) C :=
    List.mem_filter.mpr ⟨hC2, by rw [litFree_falFix_ne hvne]; exact hfree2⟩
  rw [hnil] at this
  simp at this

/-- **Active-clause stability (the decoder invariant).**  While the active clause `C`
still has `≥ 2` free literals, one falsification step does not move the active clause:
the discarded prefix stays discarded (satisfied clauses stay satisfied; exhausted
clauses stay exhausted) and `C` stays unsatisfied with a free literal remaining. -/
theorem activeClause_stable {cs : List (Clause n)} {σ : Restriction n} {C : Clause n}
    (hnodup : (C.lits.map litVar).Nodup)
    (hC : activeClause cs σ = some C)
    (hlen : 1 < (freeLits σ C).length) :
    activeClause cs (actStep cs σ) = some C := by
  obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp (activeLit_isSome hC)
  have hstep : actStep cs σ = falFix σ ℓ := by rw [actStep, hℓ]
  have hℓhead : (freeLits σ C).head? = some ℓ := by
    unfold activeLit at hℓ; rw [hC] at hℓ; exact hℓ
  have hℓfree : Depth3.litFree σ ℓ = true := activeLit_free hℓ
  have hℓmem : ℓ ∈ C.lits :=
    (List.mem_filter.mp (List.mem_of_mem_head? hℓhead)).1
  rw [hstep, activeClause]
  refine find?_stable hC ?_ ?_
  · -- `C` still passes: unsatisfied, with a free literal remaining.
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · exact clauseSatisfied_falFix σ C hℓmem
        (fun a ha b hb h => List.inj_on_of_nodup_map hnodup ha hb h) (activeClause_unsat hC)
    · exact List.length_pos_of_ne_nil (freeLits_falFix_ne_nil hnodup hℓhead hlen)
  · -- discarded clauses stay discarded.
    intro C' _ hpf
    by_cases hsat : clauseSatisfied σ C' = true
    · have : clauseSatisfied (falFix σ ℓ) C' = true := clauseSatisfied_mono_falFix C' hℓfree hsat
      simp [this]
    · have hns : clauseSatisfied σ C' = false := by simpa using hsat
      have hempty : freeLits σ C' = [] := by
        rw [hns] at hpf
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at hpf
        rw [List.length_pos_iff_ne_nil, not_not] at hpf
        exact hpf
      have : freeLits (falFix σ ℓ) C' = [] := freeLits_falFix_eq_nil hempty
      simp [this]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.activeClause_stable
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeLits_falFix_ne_nil
