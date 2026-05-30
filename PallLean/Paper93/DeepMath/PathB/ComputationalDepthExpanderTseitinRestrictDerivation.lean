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

/-- **Restriction of a weakening-resolution derivation.**  Same as `restrict_exists`
but for the weakening system (needed because the tree recursion restricts already-
restricted derivations).  No pivot-avoidance is tracked (the lift no longer needs
it). -/
theorem restrict_W (ρ : Restriction Edge) {Axiom : ResolutionClause (TLit Edge) → Prop}
    {C : ResolutionClause (TLit Edge)} (W : WDerivation tcompl Axiom C) :
    ¬ clauseSatisfied ρ C →
    ∃ W' : WDerivation tcompl (RestrictAxiom ρ Axiom) (liveClause ρ C),
      W'.size ≤ W.size ∧ W'.proofWidth ≤ W.proofWidth := by
  induction W with
  | @ax C h =>
      intro hC
      refine ⟨WDerivation.ax ⟨C, h, hC, rfl⟩, ?_, ?_⟩
      · simp [WDerivation.size_ax]
      · rw [WDerivation.proofWidth_ax, WDerivation.proofWidth_ax]
        exact liveClause_width_le ρ C
  | @resolve C D L R p ihL ihR =>
      intro hC
      rcases hpiv : ρ p.1 with _ | v
      · have hp : ρ p.1 ≠ some p.2 := by rw [hpiv]; simp
        have hq : ρ p.1 ≠ some (p.2 + 1) := by rw [hpiv]; simp
        obtain ⟨WL, hWLs, hWLw⟩ := ihL (not_clauseSatisfied_left ρ hC hp)
        obtain ⟨WR, hWRs, hWRw⟩ := ihR (not_clauseSatisfied_right ρ hC hq)
        refine ⟨WDerivation.weaken (WDerivation.resolve WL WR p)
            (le_of_eq (liveClause_resolvent ρ C D p).symm), ?_, ?_⟩
        · simp only [WDerivation.size_weaken, WDerivation.size_resolve]; omega
        · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_resolve,
            WDerivation.proofWidth_resolve]
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
      · have hzz : v = p.2 ∨ v = p.2 + 1 :=
          (by decide : ∀ x y : ZMod 2, x = y ∨ x = y + 1) v p.2
        rcases hzz with hv | hv
        · have hq : ρ p.1 ≠ some (p.2 + 1) := by
            rw [hpiv, hv]; intro h
            exact (by decide : ∀ x : ZMod 2, x ≠ x + 1) p.2 (Option.some.inj h)
          obtain ⟨WR, hWRs, hWRw⟩ := ihR (not_clauseSatisfied_right ρ hC hq)
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
          refine ⟨WDerivation.weaken WR hsub, ?_, ?_⟩
          · simp only [WDerivation.size_weaken, WDerivation.size_resolve]; omega
          · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_resolve]
            apply max_le
            · exact le_trans hWRw (le_trans (le_max_right _ _) (le_max_left _ _))
            · exact le_trans (liveClause_width_le _ _) (le_max_right _ _)
        · have hp : ρ p.1 ≠ some p.2 := by
            rw [hpiv, hv]; intro h
            exact (by decide : ∀ x : ZMod 2, x ≠ x + 1) p.2 (Option.some.inj h).symm
          obtain ⟨WL, hWLs, hWLw⟩ := ihL (not_clauseSatisfied_left ρ hC hp)
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
          refine ⟨WDerivation.weaken WL hsub, ?_, ?_⟩
          · simp only [WDerivation.size_weaken, WDerivation.size_resolve]; omega
          · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_resolve]
            apply max_le
            · exact le_trans hWLw (le_trans (le_max_left _ _) (le_max_left _ _))
            · exact le_trans (liveClause_width_le _ _) (le_max_right _ _)
  | @weaken C C' D hsubW ihD =>
      intro hC'
      have hC : ¬ clauseSatisfied ρ C :=
        fun h => hC' (h.imp (fun _ hl => ⟨hsubW hl.1, hl.2⟩))
      obtain ⟨WD, hWDs, hWDw⟩ := ihD hC
      refine ⟨WDerivation.weaken WD (Finset.filter_subset_filter _ hsubW), ?_, ?_⟩
      · simp only [WDerivation.size_weaken]; omega
      · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_weaken]
        apply max_le
        · exact le_trans hWDw (le_max_left _ _)
        · exact le_trans (liveClause_width_le ρ C') (le_max_right _ _)

/-! ## The lift / un-restriction (size–width brick 2c) -/

/-- The single-edge restriction fixing edge `e` to value `w`. -/
def singleEdge (e : Edge) (w : ZMod 2) : Restriction Edge :=
  fun e' => if e' = e then some w else none

theorem singleEdge_eq_none {e : Edge} {w : ZMod 2} {e' : Edge} :
    singleEdge e w e' = none ↔ e' ≠ e := by
  unfold singleEdge; by_cases h : e' = e <;> simp [h]

/-- A literal is never its own complement (its asserted value flips). -/
theorem ne_tcompl (p : TLit Edge) : p ≠ tcompl p := by
  intro h
  have h2 : p.2 = p.2 + 1 := by
    have := congrArg Prod.snd h
    simpa [tcompl] using this
  exact (by decide : ∀ x : ZMod 2, x ≠ x + 1) p.2 h2

/-- **Inserting a literal commutes with the resolvent** — for *any* pivot.  If the
inserted `ℓ` coincides with the pivot or its complement (so it would be erased on
one side), `insert`'s distribution over `∪` recovers it from the other side.  Only
`p ≠ tcompl p` is needed (always true).  This is what frees the lift from any
pivot-avoidance hypothesis. -/
theorem insert_resolvent {ℓ : TLit Edge} (CL CR : ResolutionClause (TLit Edge))
    {p : TLit Edge} (hp : p ≠ tcompl p) :
    ResolutionClause.resolvent tcompl (insert ℓ CL) (insert ℓ CR) p
      = insert ℓ (ResolutionClause.resolvent tcompl CL CR p) := by
  unfold ResolutionClause.resolvent
  ext x
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro (⟨hxp, rfl | hxCL⟩ | ⟨hxtp, rfl | hxCR⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hxp, hxCL⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hxtp, hxCR⟩)
  · rintro (rfl | (⟨hxp, hxCL⟩ | ⟨hxtp, hxCR⟩))
    · by_cases hxp : x = p
      · exact Or.inr ⟨by rw [hxp]; exact hp, Or.inl rfl⟩
      · exact Or.inl ⟨hxp, Or.inl rfl⟩
    · exact Or.inl ⟨hxp, Or.inr hxCL⟩
    · exact Or.inr ⟨hxtp, Or.inr hxCR⟩

/-- **Lift / un-restriction (brick 2c).**  A weakening-resolution derivation over
the single-edge–restricted axioms lifts to a derivation over the original `Axiom`
of the clause with the falsified literal `(e, w+1)` re-added, with `size` no larger
and `proofWidth` at most one larger.  No pivot-avoidance hypothesis is needed
(`insert_resolvent` handles every pivot). -/
theorem lift_single (e : Edge) (w : ZMod 2)
    {Axiom : ResolutionClause (TLit Edge) → Prop}
    {C' : ResolutionClause (TLit Edge)}
    (W : WDerivation tcompl (RestrictAxiom (singleEdge e w) Axiom) C') :
    ∃ W' : WDerivation tcompl Axiom (insert (e, w + 1) C'),
      W'.size ≤ W.size ∧ W'.proofWidth ≤ W.proofWidth + 1 := by
  induction W with
  | @ax C0' h =>
      obtain ⟨C₀, hC₀ax, hC₀ns, hC₀eq⟩ := h
      subst hC₀eq
      have hsub : C₀ ⊆ insert (e, w + 1) (liveClause (singleEdge e w) C₀) := by
        intro l hl
        by_cases hle : l.1 = e
        · have hl2 : l.2 = w + 1 := by
            rcases (by decide : ∀ x y : ZMod 2, x = y ∨ x = y + 1) l.2 w with hq | hq
            · exact absurd ⟨l, hl, by rw [hle, hq]; simp [singleEdge]⟩ hC₀ns
            · exact hq
          rw [show l = (e, w + 1) from Prod.ext hle hl2]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨hl, by simp [singleEdge, hle]⟩)
      refine ⟨WDerivation.weaken (WDerivation.ax hC₀ax) hsub, ?_, ?_⟩
      · simp [WDerivation.size_weaken, WDerivation.size_ax]
      · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_ax, WDerivation.proofWidth_ax]
        apply max_le
        · calc (C₀).width = C₀.card := rfl
            _ ≤ (insert (e, w + 1) (liveClause (singleEdge e w) C₀)).card :=
                Finset.card_le_card hsub
            _ ≤ (liveClause (singleEdge e w) C₀).card + 1 := Finset.card_insert_le _ _
        · exact Finset.card_insert_le _ _
  | @resolve CL CR L R p ihL ihR =>
      obtain ⟨WL', hWL's, hWL'w⟩ := ihL
      obtain ⟨WR', hWR's, hWR'w⟩ := ihR
      have hident :
          ResolutionClause.resolvent tcompl (insert (e, w + 1) CL) (insert (e, w + 1) CR) p
            = insert (e, w + 1) (ResolutionClause.resolvent tcompl CL CR p) :=
        insert_resolvent (ℓ := (e, w + 1)) CL CR (ne_tcompl p)
      refine ⟨WDerivation.weaken (WDerivation.resolve WL' WR' p) (le_of_eq hident), ?_, ?_⟩
      · simp only [WDerivation.size_weaken, WDerivation.size_resolve]; omega
      · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_resolve,
          WDerivation.proofWidth_resolve]
        have hw1 :
            (ResolutionClause.resolvent tcompl (insert (e, w + 1) CL) (insert (e, w + 1) CR) p).width
              ≤ (ResolutionClause.resolvent tcompl CL CR p).width + 1 := by
          rw [hident]; exact Finset.card_insert_le _ _
        have hw2 :
            (insert (e, w + 1) (ResolutionClause.resolvent tcompl CL CR p)).width
              ≤ (ResolutionClause.resolvent tcompl CL CR p).width + 1 := Finset.card_insert_le _ _
        apply max_le
        · apply max_le
          · apply max_le
            · exact le_trans hWL'w
                (Nat.add_le_add_right (le_trans (le_max_left _ _) (le_max_left _ _)) 1)
            · exact le_trans hWR'w
                (Nat.add_le_add_right (le_trans (le_max_right _ _) (le_max_left _ _)) 1)
          · exact le_trans hw1 (Nat.add_le_add_right (le_max_right _ _) 1)
        · exact le_trans hw2 (Nat.add_le_add_right (le_max_right _ _) 1)
  | @weaken CC CC' D hsubW ihD =>
      obtain ⟨WD', hWD's, hWD'w⟩ := ihD
      refine ⟨WDerivation.weaken WD' (Finset.insert_subset_insert _ hsubW), ?_, ?_⟩
      · simp only [WDerivation.size_weaken]; omega
      · rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_weaken]
        apply max_le
        · exact le_trans hWD'w (Nat.add_le_add_right (le_max_left _ _) 1)
        · exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right (le_max_right _ _) 1)

/-! ## The asymmetric per-variable width bound (size–width brick 3a) -/

/-- Resolving an original axiom `C₀` (unsatisfied by `e = w+1`) against the unit
clause `{(e,w+1)}` on pivot `(e,w)` re-derives the restricted axiom
`liveClause (singleEdge e (w+1)) C₀`.  This is the engine of the **no-`+1`** side
of the asymmetric bound. -/
theorem rederive_subset (e : Edge) (w : ZMod 2) {C₀ : ResolutionClause (TLit Edge)}
    (hns : ¬ clauseSatisfied (singleEdge e (w + 1)) C₀) :
    ResolutionClause.resolvent tcompl C₀ (insert (e, w + 1) ∅) (e, w)
      ⊆ liveClause (singleEdge e (w + 1)) C₀ := by
  intro l hl
  rw [ResolutionClause.resolvent] at hl
  rcases Finset.mem_union.mp hl with h1 | h2
  · obtain ⟨hlne, hlC₀⟩ := Finset.mem_erase.mp h1
    refine Finset.mem_filter.mpr ⟨hlC₀, singleEdge_eq_none.mpr ?_⟩
    intro hle
    apply hlne
    have hl2 : l.2 = w := by
      rcases (by decide : ∀ x y : ZMod 2, x = y ∨ x = y + 1) l.2 w with hq | hq
      · exact hq
      · exact absurd ⟨l, hlC₀, by rw [hle, hq]; simp [singleEdge]⟩ hns
    exact Prod.ext hle hl2
  · exfalso
    simp [tcompl, Finset.mem_erase, Finset.mem_insert] at h2

/-- **Asymmetric per-variable width bound (brick 3a).**  Given refutations of both
single-edge restrictions of `Axiom` at edge `e`, there is a refutation of `Axiom`
whose width is `max(Wm, Wp + 1, w₀)`: the `w`-side (`Wp`) is *lifted* to the unit
clause `{(e,w+1)}` (costing `+1`), and the `(w+1)`-side (`Wm`) is *grafted* — its
restricted axioms re-derived against that unit clause at width `≤ w₀`, with **no**
`+1`.  Placing the `+1` on the smaller subtree is what makes the tree recursion
close at `log`. -/
theorem asymmetric (e : Edge) (w : ZMod 2)
    {Axiom : ResolutionClause (TLit Edge) → Prop} {w₀ : ℕ}
    (hw₀ : ∀ C, Axiom C → C.width ≤ w₀)
    (Wp : WDerivation tcompl (RestrictAxiom (singleEdge e w) Axiom) ∅)
    (Wm : WDerivation tcompl (RestrictAxiom (singleEdge e (w + 1)) Axiom) ∅) :
    ∃ W : WDerivation tcompl Axiom ∅,
      W.proofWidth ≤ max (max Wm.proofWidth (Wp.proofWidth + 1)) w₀ := by
  obtain ⟨Du, _hDus, hDuw⟩ := lift_single e w Wp
  -- The re-derivation: stated as a Prop existence (so the `Exists` witness `C₀` can
  -- be destructured), then the graft's function is extracted pointwise by choice.
  have hex : ∀ C' (h : RestrictAxiom (singleEdge e (w + 1)) Axiom C'),
      ∃ D : WDerivation tcompl Axiom C', D.proofWidth ≤ max w₀ Du.proofWidth := by
    intro C' h
    obtain ⟨C₀, hax, hns, heq⟩ := h
    subst heq
    have hWC₀ : C₀.width ≤ w₀ := hw₀ C₀ hax
    have hsubC₀ : ResolutionClause.resolvent tcompl C₀ (insert (e, w + 1) ∅) (e, w) ⊆ C₀ :=
      Finset.Subset.trans (rederive_subset e w hns) (liveClause_subset _ _)
    refine ⟨WDerivation.weaken (WDerivation.resolve (WDerivation.ax hax) Du (e, w))
        (rederive_subset e w hns), ?_⟩
    rw [WDerivation.proofWidth_weaken, WDerivation.proofWidth_resolve, WDerivation.proofWidth_ax]
    apply max_le
    · apply max_le
      · apply max_le
        · exact le_trans hWC₀ (le_max_left _ _)
        · exact le_max_right _ _
      · exact le_trans (le_trans (Finset.card_le_card hsubC₀) hWC₀) (le_max_left _ _)
    · exact le_trans (le_trans (liveClause_width_le _ _) hWC₀) (le_max_left _ _)
  refine ⟨WDerivation.graft (fun C' h => Classical.choose (hex C' h)) Wm, ?_⟩
  refine le_trans (WDerivation.graft_proofWidth_le (fun C' h => Classical.choose (hex C' h))
      (fun C' h => Classical.choose_spec (hex C' h)) Wm) ?_
  apply max_le
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · apply max_le
    · exact le_max_right _ _
    · exact le_trans hDuw (le_trans (le_max_right _ _) (le_max_left _ _))

end PallLean.Paper93.DeepMath.PathB.TseitinRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.restrict_exists
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.lift_single
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.asymmetric
