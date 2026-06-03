import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SearchDischarge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter

/-!
# The threading coupling: `canonicalDT` ⟹ `ValidSearch` ⟹ resolution refutation

This file closes the gap flagged in `ComputationalDepthDepth3SearchDischarge`: it couples the
relabelling's accumulated false-literal set `F` to the canonical decision tree's restriction `σ`,
and exhibits the De Morgan leaf certificate, assembling them into a full `ValidSearch` proof for the
canonical tree of a **tautological** DNF.

Two coupling facts:

* **`falseSet_fixVar_false` / `_true`** — descending `canonicalDT`'s branches threads `F` exactly as
  `falseSet` evolves: fixing a *free* variable `i` to `false` adds `rpos i = (i,true)` to the
  false-set, to `true` adds `(i,false) = rcompl (rpos i)`.  This is precisely the `insert` the
  `ValidSearch`/`relabel` accumulation performs, so the threaded `F` along a `canonicalDT` path
  equals `falseSet σ` for that path's restriction.

* **`negTermClause_subset_falseSet`** — the De Morgan leaf certificate: a term `T` *satisfied* by
  `σ` (`termSat`) has its negation `negTermClause T` (the De Morgan–dual axiom clause) `⊆ falseSet σ`
  — its literals are all false on the path.  Rests on `resClause_subset_falseSet` (the semantic
  kernel) and `litFalse_litNeg` (`litTrue ℓ ⟹ litFalse (litNeg ℓ)`).

The assembly `validSearch_canonicalDT`: if the DNF `cs` is a **tautology** (`∀ x, dnfEval cs x =
true` — the refuting condition, the dual CNF is unsatisfiable) and `fuel ≥ stars σ`, then
`ValidSearch` holds for `canonicalDT cs fuel σ` with the search labelling `labSearch` and axiom set
`AxiomOf cs` (the De Morgan duals of the terms).  Every `canonicalDT` leaf is a *satisfied* leaf:
the structural `false` leaves (all-terms-falsified) are impossible under tautology — they would
falsify the DNF on an extension.  Composed with `boolDT_to_ldderiv_of_valid`, this yields a genuine
resolution refutation of `AxiomOf cs` of width `≤ depth` and length `< 2^(depth+1)`.

This completes the structural chain: `canonicalDT` (computes the DNF) → relabel → `DTRef` →
width-`depth` `LDeriv` refutation — for any tautological DNF, with the *only* external input being
that the DNF is a tautology (i.e. the formula being refuted is unsatisfiable).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SearchDischarge

open Depth3 SwitchingCounting
open scoped Classical

variable {n : ℕ}

/-! ### The De Morgan leaf certificate -/

/-- `litTrue σ ℓ ⟹ litFalse σ (litNeg ℓ)`: negating a forced-true literal gives a forced-false one. -/
theorem litFalse_litNeg {σ : Fin n → Option Bool} {ℓ : Rung4Literal n}
    (h : Depth3.litTrue σ ℓ = true) : SwitchingCounting.litFalse σ (Depth3.litNeg ℓ) = true := by
  cases ℓ with
  | pos i =>
    cases hσ : σ i with
    | none => simp [Depth3.litTrue, Depth3.litFixedVal, hσ] at h
    | some b => cases b with
      | true => simp [Depth3.litNeg, SwitchingCounting.litFalse, Depth3.litFixedVal, hσ]
      | false => simp [Depth3.litTrue, Depth3.litFixedVal, hσ] at h
  | neg i =>
    cases hσ : σ i with
    | none => simp [Depth3.litTrue, Depth3.litFixedVal, hσ] at h
    | some b => cases b with
      | false => simp [Depth3.litNeg, SwitchingCounting.litFalse, Depth3.litFixedVal, hσ]
      | true => simp [Depth3.litTrue, Depth3.litFixedVal, hσ] at h

/-- The De Morgan–dual axiom clause of a DNF term: negate every literal, read as a resolution
clause. -/
def negTermClause (T : Clause n) : ResolutionClause (RLit n) :=
  resClause (T.lits.map Depth3.litNeg)

/-- **The leaf certificate.**  A term satisfied by `σ` has its dual axiom clause `⊆ falseSet σ`. -/
theorem negTermClause_subset_falseSet {σ : Fin n → Option Bool} {T : Clause n}
    (h : SwitchingCounting.termSat σ T = true) : negTermClause T ⊆ falseSet σ := by
  apply resClause_subset_falseSet
  intro ℓ hℓ
  rw [List.mem_map] at hℓ
  obtain ⟨ℓ', hℓ', rfl⟩ := hℓ
  rw [SwitchingCounting.termSat, List.all_eq_true] at h
  exact litFalse_litNeg (h ℓ' hℓ')

/-! ### The false-set threading coupling -/

/-- Fixing a free variable to `false` adds `rpos i = (i,true)` to the false-set. -/
theorem falseSet_fixVar_false {σ : Fin n → Option Bool} {i : Fin n} (hi : σ i = none) :
    falseSet (Depth3.fixVar σ i false) = insert (rpos i) (falseSet σ) := by
  ext p
  obtain ⟨a, b⟩ := p
  rw [mem_falseSet, Finset.mem_insert, mem_falseSet, Depth3.fixVar]
  by_cases hai : a = i
  · subst hai
    rw [Function.update_self]
    cases b <;> simp [rpos, hi]
  · rw [Function.update_of_ne hai]
    cases b <;> simp [rpos, hai]

/-- Fixing a free variable to `true` adds `(i,false) = rcompl (rpos i)` to the false-set. -/
theorem falseSet_fixVar_true {σ : Fin n → Option Bool} {i : Fin n} (hi : σ i = none) :
    falseSet (Depth3.fixVar σ i true) = insert (rcompl (rpos i)) (falseSet σ) := by
  ext p
  obtain ⟨a, b⟩ := p
  rw [mem_falseSet, Finset.mem_insert, mem_falseSet, Depth3.fixVar]
  by_cases hai : a = i
  · subst hai
    rw [Function.update_self]
    cases b <;> simp [rpos, rcompl, hi]
  · rw [Function.update_of_ne hai]
    cases b <;> simp [rpos, rcompl, hai]

/-! ### The search labelling and axiom set -/

/-- The axiom set of the refutation: the De Morgan duals of the DNF terms. -/
def AxiomOf (cs : List (Clause n)) : ResolutionClause (RLit n) → Prop :=
  fun A => ∃ T ∈ cs, A = negTermClause T

/-- The search labelling: at a leaf with false-set `F`, return the dual of a term whose dual is
falsified by the path (one exists at every satisfied leaf). -/
noncomputable def labSearch (cs : List (Clause n)) (F : ResolutionClause (RLit n)) :
    ResolutionClause (RLit n) :=
  if h : ∃ T ∈ cs, negTermClause T ⊆ F then negTermClause h.choose else ∅

/-- At a leaf where some dual axiom is falsified by the path, `labSearch` returns such an axiom. -/
theorem labSearch_spec {cs : List (Clause n)} {F : ResolutionClause (RLit n)}
    (h : ∃ T ∈ cs, negTermClause T ⊆ F) :
    AxiomOf cs (labSearch cs F) ∧ labSearch cs F ⊆ F := by
  rw [labSearch, dif_pos h]
  exact ⟨⟨h.choose, h.choose_spec.1, rfl⟩, h.choose_spec.2⟩

/-- At a satisfied leaf (`anyTermSat`), some dual axiom is falsified by the path. -/
theorem leafCert {cs : List (Clause n)} {σ : Fin n → Option Bool}
    (h : SwitchingCounting.anyTermSat cs σ = true) : ∃ T ∈ cs, negTermClause T ⊆ falseSet σ := by
  rw [SwitchingCounting.anyTermSat, List.any_eq_true] at h
  obtain ⟨T, hT, hsat⟩ := h
  exact ⟨T, hT, negTermClause_subset_falseSet hsat⟩

/-- Under tautology, a restriction that falsifies every term is impossible (it falsifies the DNF on
the canonical extension). -/
theorem not_all_falsified {cs : List (Clause n)} (htaut : ∀ x, Depth3.dnfEval cs x = true)
    {σ : Fin n → Option Bool} (hall : ∀ T ∈ cs, SwitchingCounting.termFalsified σ T = true) :
    False := by
  have hext : Rung4Restriction.Extends σ (fun i => (σ i).getD false) := by
    intro i b hib; simp [hib]
  have h1 := Depth3.dnfEval_false_of_all_falsified hall hext
  rw [show Depth3.dnfEval cs (fun i => (σ i).getD false) = true from htaut _] at h1
  exact absurd h1 (by decide)

/-- **The threading coupling assembly.**  For a tautological DNF `cs` and `fuel ≥ stars σ`, the
canonical decision tree solves the dual-axiom Search problem: `ValidSearch` holds for
`canonicalDT cs fuel σ` with the search labelling and axiom set `AxiomOf cs`, anchored at
`falseSet σ`.  The structural `false` leaves are ruled out by `not_all_falsified`. -/
theorem validSearch_canonicalDT (cs : List (Clause n))
    (htaut : ∀ x, Depth3.dnfEval cs x = true) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool), SwitchingCounting.stars σ ≤ fuel →
      ValidSearch rpos rcompl (labSearch cs) (AxiomOf cs) (falseSet σ)
        (Depth3.canonicalDT cs fuel σ) := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ h0
    have hst : SwitchingCounting.stars σ = 0 := Nat.le_zero.mp h0
    rw [Depth3.canonicalDT]
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      simp only [hany, if_true]
      exact labSearch_spec (leafCert hany)
    | false =>
      exfalso
      exact not_all_falsified htaut
        (Depth3.all_falsified_general hany
          (fun T _ => Or.inr (Depth3.freeLits_nil_of_stars_zero hst T)))
  | succ fuel ih =>
    intro σ hfuel
    rw [Depth3.canonicalDT]
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true =>
      simp only [hany, if_true]
      exact labSearch_spec (leafCert hany)
    | false =>
      simp only [hany, Bool.false_eq_true, if_false]
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        exfalso
        refine not_all_falsified htaut (Depth3.all_falsified_general hany (fun T hT => ?_))
        have hfind : cs.find? (fun T => !SwitchingCounting.termFalsified σ T &&
            decide (0 < (SwitchingCounting.freeLits σ T).length)) = none :=
          SwitchingCounting.activeTerm_eq_find hany ▸ hact
        have hp := (List.find?_eq_none.mp hfind) T hT
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Bool.not_eq_true'] at hp
        by_cases htf : SwitchingCounting.termFalsified σ T = true
        · exact Or.inl htf
        · exact Or.inr (List.length_eq_zero_iff.mp (by have := hp (by simpa using htf); omega))
      | some T =>
        obtain ⟨ℓ, hhead, hfree⟩ := Depth3.activeTerm_first_free hact
        simp only [hhead]
        have hs : SwitchingCounting.stars (Depth3.fixVar σ (litVar ℓ) false) ≤ fuel := by
          have := Depth3.stars_fixVar_lt (b := false) hfree; omega
        have hs' : SwitchingCounting.stars (Depth3.fixVar σ (litVar ℓ) true) ≤ fuel := by
          have := Depth3.stars_fixVar_lt (b := true) hfree; omega
        refine ⟨?_, ?_⟩
        · rw [← falseSet_fixVar_false hfree]; exact ih _ hs
        · rw [← falseSet_fixVar_true hfree]; exact ih _ hs'

/-- **The full chain: tautological DNF ⟹ resolution refutation.**  For a tautological DNF and
`fuel ≥ stars ∅`, the canonical tree's relabelling is a valid `LDeriv` over `AxiomOf cs` containing
the empty clause, with length `< 2^(depth+1)` and width `≤ depth`. -/
theorem canonicalDT_ldderiv (cs : List (Clause n)) (htaut : ∀ x, Depth3.dnfEval cs x = true)
    (fuel : ℕ) (hfuel : SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool)) ≤ fuel) :
    LDeriv rcompl (AxiomOf cs)
        (DTRef.toList rcompl (relabel rpos rcompl (labSearch cs) ∅ (Depth3.canonicalDT cs fuel (fun _ => none)))) ∧
      (∅ : ResolutionClause (RLit n)) ∈
        DTRef.toList rcompl (relabel rpos rcompl (labSearch cs) ∅ (Depth3.canonicalDT cs fuel (fun _ => none))) := by
  have hvalid : ValidSearch rpos rcompl (labSearch cs) (AxiomOf cs) ∅
      (Depth3.canonicalDT cs fuel (fun _ => none)) := by
    have h := validSearch_canonicalDT cs htaut fuel (fun _ => none) hfuel
    have hfs : falseSet (fun _ : Fin n => (none : Option Bool)) = (∅ : ResolutionClause (RLit n)) := by
      ext p; simp [mem_falseSet]
    rwa [hfs] at h
  have h := boolDT_to_ldderiv_of_valid rpos rcompl (labSearch cs)
    (Depth3.canonicalDT cs fuel (fun _ => none)) hvalid
  exact ⟨h.1, h.2.1⟩

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.validSearch_canonicalDT
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.canonicalDT_ldderiv
