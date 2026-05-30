import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinRestriction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWeakening

/-!
# Restriction of a resolution derivation (size–width brick 2b)

Given a tree-like resolution derivation of a clause `C` and a restriction `ρ` that
does **not** satisfy `C`, we build a *weakening-resolution* derivation
(`WDerivation`, brick 2a) of the restricted clause `liveClause ρ C` over the
restricted axioms `RestrictAxiom ρ Axiom`, with `size` and `proofWidth` no larger
(`restrict_exists`).

The recursion splits on the pivot edge `p` of each resolution step:

* **pivot live** (`ρ p.1 = none`): neither parent is satisfied, so both restrict
  recursively and we resolve them on `p` — using `liveClause_resolvent`, which says
  restriction commutes with the resolvent.
* **pivot fixed** (`ρ p.1 = some _`): one parent's pivot literal is satisfied and
  that parent disappears, but the surviving parent's restricted clause is a
  *subclause* of the restricted resolvent, so we **weaken** it up.  This is exactly
  why the target system needs weakening.

This is the operation brick 3 (the logarithmic size→width recursion) iterates: a
size-`S` refutation restricts to a refutation of a one-variable-smaller formula of
size `≤ S`, and the recursion bounds the width by `w₀ + log₂ S`.  Combined with the
unconditional width lower bound (`proofWidth ≥ c·t`) this yields `size ≥ 2^{Ω(t)}`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinRestriction

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open scoped BigOperators

variable {Edge : Type*} [DecidableEq Edge]

/-! ## Restriction commutes with the clause operations -/

/-- `liveClause` distributes over union. -/
theorem liveClause_union (ρ : Restriction Edge) (C D : ResolutionClause (TLit Edge)) :
    liveClause ρ (C ∪ D) = liveClause ρ C ∪ liveClause ρ D := by
  unfold liveClause; rw [Finset.filter_union]

/-- `liveClause` commutes with `erase`. -/
theorem liveClause_erase (ρ : Restriction Edge) (x : TLit Edge) (C : ResolutionClause (TLit Edge)) :
    liveClause ρ (C.erase x) = (liveClause ρ C).erase x := by
  unfold liveClause; rw [Finset.filter_erase]

/-- **Restriction commutes with the resolvent.** -/
theorem liveClause_resolvent (ρ : Restriction Edge) (C D : ResolutionClause (TLit Edge))
    (p : TLit Edge) :
    liveClause ρ (ResolutionClause.resolvent tcompl C D p)
      = ResolutionClause.resolvent tcompl (liveClause ρ C) (liveClause ρ D) p := by
  unfold ResolutionClause.resolvent
  rw [liveClause_union, liveClause_erase, liveClause_erase]

/-! ## Parent clauses are unsatisfied -/

/-- If the resolvent is unsatisfied and the pivot literal `p` is unsatisfied, the
left parent is unsatisfied. -/
theorem not_clauseSatisfied_left (ρ : Restriction Edge)
    {C D : ResolutionClause (TLit Edge)} {p : TLit Edge}
    (hres : ¬ clauseSatisfied ρ (ResolutionClause.resolvent tcompl C D p))
    (hp : ρ p.1 ≠ some p.2) : ¬ clauseSatisfied ρ C := by
  rintro ⟨l, hlC, hl⟩
  rcases eq_or_ne l p with rfl | hne
  · exact hp hl
  · exact hres ⟨l, Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hne, hlC⟩)), hl⟩

/-- If the resolvent is unsatisfied and the complementary pivot literal `tcompl p`
is unsatisfied, the right parent is unsatisfied. -/
theorem not_clauseSatisfied_right (ρ : Restriction Edge)
    {C D : ResolutionClause (TLit Edge)} {p : TLit Edge}
    (hres : ¬ clauseSatisfied ρ (ResolutionClause.resolvent tcompl C D p))
    (hq : ρ p.1 ≠ some (p.2 + 1)) : ¬ clauseSatisfied ρ D := by
  rintro ⟨l, hlD, hl⟩
  rcases eq_or_ne l (tcompl p) with rfl | hne
  · rw [show (tcompl p).1 = p.1 from rfl, show (tcompl p).2 = p.2 + 1 from rfl] at hl
    exact hq hl
  · exact hres ⟨l, Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hne, hlD⟩)), hl⟩

/-! ## The restricted axiom set and the restriction of a derivation -/

/-- The restricted axiom set: an *unsatisfied* axiom `C`, restricted to its live
part `liveClause ρ C`. -/
def RestrictAxiom (ρ : Restriction Edge) (Axiom : ResolutionClause (TLit Edge) → Prop)
    (C' : ResolutionClause (TLit Edge)) : Prop :=
  ∃ C, Axiom C ∧ ¬ clauseSatisfied ρ C ∧ liveClause ρ C = C'

/-- **Restriction of a derivation (brick 2b).**  A derivation of an unsatisfied
clause `C` restricts to a weakening-resolution derivation of `liveClause ρ C` over
the restricted axioms, with `size` and `proofWidth` no larger. -/
theorem restrict_exists (ρ : Restriction Edge)
    {Axiom : ResolutionClause (TLit Edge) → Prop}
    {C : ResolutionClause (TLit Edge)}
    (Der : ResolutionDerivation tcompl Axiom C) :
    ¬ clauseSatisfied ρ C →
    ∃ W : WDerivation tcompl (RestrictAxiom ρ Axiom) (liveClause ρ C),
      W.size ≤ Der.size ∧ W.proofWidth ≤ Der.proofWidth ∧
        WDerivation.PivotsAvoid (fun p => ρ p.1 = none) W := by
  induction Der with
  | @ax C h =>
      intro hC
      refine ⟨WDerivation.ax ⟨C, h, hC, rfl⟩, ?_, ?_, ?_⟩
      · simp [WDerivation.size_ax, ResolutionDerivation.size_ax]
      · rw [WDerivation.proofWidth_ax, ResolutionDerivation.proofWidth_ax]
        exact liveClause_width_le ρ C
      · trivial
  | @resolve C D L R p ihL ihR =>
      intro hC
      rcases hpiv : ρ p.1 with _ | v
      · -- pivot live: both parents unsatisfied, resolve and weaken to the live resolvent
        have hp : ρ p.1 ≠ some p.2 := by rw [hpiv]; simp
        have hq : ρ p.1 ≠ some (p.2 + 1) := by rw [hpiv]; simp
        obtain ⟨WL, hWLs, hWLw, hWLa⟩ := ihL (not_clauseSatisfied_left ρ hC hp)
        obtain ⟨WR, hWRs, hWRw, hWRa⟩ := ihR (not_clauseSatisfied_right ρ hC hq)
        refine ⟨WDerivation.weaken (WDerivation.resolve WL WR p)
            (le_of_eq (liveClause_resolvent ρ C D p).symm), ?_, ?_, ?_⟩
        · simp only [WDerivation.size_weaken, WDerivation.size_resolve,
            ResolutionDerivation.size_resolve]
          omega
        · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_resolve,
            ResolutionDerivation.proofWidth_resolve]
          have hwres : (liveClause ρ (ResolutionClause.resolvent tcompl C D p)).width
              ≤ (ResolutionClause.resolvent tcompl C D p).width := liveClause_width_le _ _
          have hwlc : (ResolutionClause.resolvent tcompl (liveClause ρ C) (liveClause ρ D) p).width
              ≤ (ResolutionClause.resolvent tcompl C D p).width := by
            rw [← liveClause_resolvent]; exact liveClause_width_le _ _
          apply max_le
          · apply max_le
            · apply max_le
              · exact le_trans hWLw (le_trans (le_max_left _ _) (le_max_left _ _))
              · exact le_trans hWRw (le_trans (le_max_right _ _) (le_max_left _ _))
            · exact le_trans hwlc (le_max_right _ _)
          · exact le_trans hwres (le_max_right _ _)
        · exact ⟨hpiv, hWLa, hWRa⟩
      · have hzz : v = p.2 ∨ v = p.2 + 1 :=
          (by decide : ∀ x y : ZMod 2, x = y ∨ x = y + 1) v p.2
        rcases hzz with hv | hv
        · -- pivot literal `p` satisfied: right parent survives, weaken it up
          have hq : ρ p.1 ≠ some (p.2 + 1) := by
            rw [hpiv, hv]; intro h
            exact (by decide : ∀ x : ZMod 2, x ≠ x + 1) p.2 (Option.some.inj h)
          obtain ⟨WR, hWRs, hWRw, hWRa⟩ := ihR (not_clauseSatisfied_right ρ hC hq)
          have htnl : tcompl p ∉ liveClause ρ D := by
            intro hmem
            have h2 := (Finset.mem_filter.mp hmem).2
            rw [show (tcompl p).1 = p.1 from rfl, hpiv] at h2
            exact (Option.some_ne_none v) h2
          have hsub : liveClause ρ D
              ⊆ liveClause ρ (ResolutionClause.resolvent tcompl C D p) := by
            rw [liveClause_resolvent]; unfold ResolutionClause.resolvent
            calc liveClause ρ D = (liveClause ρ D).erase (tcompl p) :=
                  (Finset.erase_eq_of_notMem htnl).symm
              _ ⊆ (liveClause ρ C).erase p ∪ (liveClause ρ D).erase (tcompl p) :=
                  Finset.subset_union_right
          refine ⟨WDerivation.weaken WR hsub, ?_, ?_, ?_⟩
          · simp only [WDerivation.size_weaken, ResolutionDerivation.size_resolve]; omega
          · rw [WDerivation.proofWidth_weaken, ResolutionDerivation.proofWidth_resolve]
            apply max_le
            · exact le_trans hWRw (le_trans (le_max_right _ _) (le_max_left _ _))
            · exact le_trans (liveClause_width_le _ _) (le_max_right _ _)
          · exact hWRa
        · -- complementary pivot literal `tcompl p` satisfied: left parent survives
          have hp : ρ p.1 ≠ some p.2 := by
            rw [hpiv, hv]; intro h
            exact (by decide : ∀ x : ZMod 2, x ≠ x + 1) p.2 (Option.some.inj h).symm
          obtain ⟨WL, hWLs, hWLw, hWLa⟩ := ihL (not_clauseSatisfied_left ρ hC hp)
          have hpnl : p ∉ liveClause ρ C := by
            intro hmem
            have h2 := (Finset.mem_filter.mp hmem).2
            rw [hpiv] at h2
            exact (Option.some_ne_none v) h2
          have hsub : liveClause ρ C
              ⊆ liveClause ρ (ResolutionClause.resolvent tcompl C D p) := by
            rw [liveClause_resolvent]; unfold ResolutionClause.resolvent
            calc liveClause ρ C = (liveClause ρ C).erase p :=
                  (Finset.erase_eq_of_notMem hpnl).symm
              _ ⊆ (liveClause ρ C).erase p ∪ (liveClause ρ D).erase (tcompl p) :=
                  Finset.subset_union_left
          refine ⟨WDerivation.weaken WL hsub, ?_, ?_, ?_⟩
          · simp only [WDerivation.size_weaken, ResolutionDerivation.size_resolve]; omega
          · rw [WDerivation.proofWidth_weaken, ResolutionDerivation.proofWidth_resolve]
            apply max_le
            · exact le_trans hWLw (le_trans (le_max_left _ _) (le_max_left _ _))
            · exact le_trans (liveClause_width_le _ _) (le_max_right _ _)
          · exact hWLa

end PallLean.Paper93.DeepMath.PathB.TseitinRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.restrict_exists
