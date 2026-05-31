import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionClauseAlgebra

/-!
# List-based weakening derivations and restriction-with-removal

The `Fin`-indexed `WeakeningDAG` model cannot cleanly express the *removal* of
clauses satisfied by a restriction (it would force a `Fin` re-indexing).  The
fat-clause size→width recursion needs that removal — dropping the `ℓ=1`-satisfied
clauses is exactly what shrinks the fat-clause count.

So we use a **list-based** derivation model where each clause is justified by
*earlier* clauses referenced **by value** (membership in the tail).  Removal is
then just `List.filter`, which preserves order, and validity is re-established
clause-by-clause from the restriction clause-algebra
(`restrictClause_resolvent`, the two weakening lemmas).

The payoff is `LDeriv.restrict`: restricting `ℓ:=true` — *dropping* every clause
that contains `ℓ` and erasing `compl ℓ` from the rest — maps a derivation over
`Axiom` to a derivation over the restricted, surviving axioms, with width not
increasing and the empty clause preserved.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.RestrictionClauseAlgebra

variable {Lit : Type*} [DecidableEq Lit]

/-- A list-based weakening derivation: reading the list head-first, each clause is
an axiom, the resolvent of two earlier clauses, or a superclause of an earlier
clause — where "earlier" means *membership in the tail* (reference by value). -/
inductive LDeriv (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop) :
    List (ResolutionClause Lit) → Prop
  | nil : LDeriv compl Axiom []
  | cons {C : ResolutionClause Lit} {L : List (ResolutionClause Lit)}
      (just : Axiom C ∨
        (∃ D E p, D ∈ L ∧ E ∈ L ∧ C = ResolutionClause.resolvent compl D E p) ∨
        (∃ D, D ∈ L ∧ D ⊆ C))
      (h : LDeriv compl Axiom L) : LDeriv compl Axiom (C :: L)

namespace LDeriv

variable {compl : Lit → Lit} {Axiom : ResolutionClause Lit → Prop}

/-- The clauses surviving `ℓ:=true` (those not containing `ℓ`), each restricted. -/
def restrictList (compl : Lit → Lit) (ℓ : Lit) (L : List (ResolutionClause Lit)) :
    List (ResolutionClause Lit) :=
  (L.filter (fun C => decide (ℓ ∉ C))).map (restrictClause compl ℓ)

theorem mem_restrictList (compl : Lit → Lit) (ℓ : Lit) (L : List (ResolutionClause Lit))
    (X : ResolutionClause Lit) :
    X ∈ restrictList compl ℓ L ↔ ∃ C, C ∈ L ∧ ℓ ∉ C ∧ restrictClause compl ℓ C = X := by
  simp only [restrictList, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨C, ⟨hC, hℓ⟩, hX⟩; exact ⟨C, hC, hℓ, hX⟩
  · rintro ⟨C, hC, hℓ, hX⟩; exact ⟨C, ⟨hC, hℓ⟩, hX⟩

/-- **Restriction with removal.**  Restricting `ℓ:=true` maps a derivation over
`Axiom` to a derivation over the surviving restricted axioms.  Requires only that
`ℓ` and its complement differ (`hℓ`), which holds for the Tseitin complement. -/
theorem restrict {ℓ : Lit} (hℓ : ℓ ≠ compl ℓ) (hinv : ∀ x, compl (compl x) = x)
    {L : List (ResolutionClause Lit)} (h : LDeriv compl Axiom L) :
    LDeriv compl (fun C' => ∃ C, Axiom C ∧ ℓ ∉ C ∧ restrictClause compl ℓ C = C')
      (restrictList compl ℓ L) := by
  induction h with
  | nil => exact LDeriv.nil
  | @cons C L just _ ih =>
    by_cases hℓC : ℓ ∈ C
    · -- C is satisfied by ℓ:=true; it is removed, list unchanged
      have : restrictList compl ℓ (C :: L) = restrictList compl ℓ L := by
        simp only [restrictList, List.filter_cons, decide_eq_true_eq, hℓC, not_true,
          decide_false, Bool.false_eq_true, if_false]
      rw [this]; exact ih
    · -- C survives; prepend its restriction and re-justify
      have hcons : restrictList compl ℓ (C :: L)
          = restrictClause compl ℓ C :: restrictList compl ℓ L := by
        simp only [restrictList, List.filter_cons, decide_eq_true_eq, hℓC, not_false_iff,
          decide_true, if_true, List.map_cons]
      rw [hcons]
      refine LDeriv.cons ?_ ih
      rcases just with hax | ⟨D, E, p, hD, hE, heq⟩ | ⟨D, hD, hsub⟩
      · -- axiom
        exact Or.inl ⟨C, hax, hℓC, rfl⟩
      · -- resolvent of D, E at pivot p
        by_cases hℓD : ℓ ∈ D
        · -- D removed: pivot must be ℓ, E survives, restriction weakens E
          have hpℓ : p = ℓ := by
            by_contra hp
            apply hℓC
            rw [heq, ResolutionClause.resolvent]
            exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨Ne.symm hp, hℓD⟩)
          have hℓE : ℓ ∉ E := by
            intro hmem
            apply hℓC
            rw [heq, ResolutionClause.resolvent]
            refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hmem⟩)
            rw [hpℓ]; exact hℓ
          refine Or.inr (Or.inr ⟨restrictClause compl ℓ E,
            (mem_restrictList compl ℓ L _).mpr ⟨E, hE, hℓE, rfl⟩, ?_⟩)
          rw [heq, hpℓ]
          exact restrictClause_subset_resolvent_pivot compl ℓ D E
        · by_cases hℓE : ℓ ∈ E
          · -- E removed: pivot equals `compl ℓ`, D survives, restriction weakens D
            have hpℓ : p = compl ℓ := by
              by_contra hp
              have hne : ℓ ≠ compl p := by
                intro hc; exact hp (by rw [hc]; exact (hinv p).symm)
              apply hℓC
              rw [heq, ResolutionClause.resolvent]
              exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hℓE⟩)
            refine Or.inr (Or.inr ⟨restrictClause compl ℓ D,
              (mem_restrictList compl ℓ L _).mpr ⟨D, hD, hℓD, rfl⟩, ?_⟩)
            rw [heq, hpℓ]
            exact restrictClause_subset_resolvent_pivot' compl ℓ D E
          · -- both parents survive: exact restricted resolvent
            refine Or.inr (Or.inl ⟨restrictClause compl ℓ D, restrictClause compl ℓ E, p,
              (mem_restrictList compl ℓ L _).mpr ⟨D, hD, hℓD, rfl⟩,
              (mem_restrictList compl ℓ L _).mpr ⟨E, hE, hℓE, rfl⟩, ?_⟩)
            rw [heq, restrictClause_resolvent]
      · -- weakening of D ⊆ C: D survives since D ⊆ C and ℓ ∉ C
        have hℓD : ℓ ∉ D := fun hmem => hℓC (hsub hmem)
        refine Or.inr (Or.inr ⟨restrictClause compl ℓ D,
          (mem_restrictList compl ℓ L _).mpr ⟨D, hD, hℓD, rfl⟩, ?_⟩)
        exact Finset.erase_subset_erase _ hsub

/-- Restriction never increases width: every clause of the restricted list is
within any width bound on the original. -/
theorem restrictList_width_le {ℓ : Lit} {L : List (ResolutionClause Lit)} {W : ℕ}
    (hW : ∀ C ∈ L, ResolutionClause.width C ≤ W) :
    ∀ X ∈ restrictList compl ℓ L, ResolutionClause.width X ≤ W := by
  intro X hX
  obtain ⟨C, hC, _, rfl⟩ := (mem_restrictList compl ℓ L X).mp hX
  exact le_trans (restrictClause_width_le compl ℓ C) (hW C hC)

/-- Restriction preserves a refutation: the empty clause survives. -/
theorem mem_restrictList_empty {ℓ : Lit} {L : List (ResolutionClause Lit)}
    (h : (∅ : ResolutionClause Lit) ∈ L) :
    (∅ : ResolutionClause Lit) ∈ restrictList compl ℓ L :=
  (mem_restrictList compl ℓ L ∅).mpr ⟨∅, h, by simp, by simp [restrictClause]⟩

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.restrict
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.restrictList_width_le
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.mem_restrictList_empty
