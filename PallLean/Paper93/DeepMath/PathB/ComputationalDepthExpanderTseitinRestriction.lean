import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinResolutionWidth

/-!
# Expander-Tseitin size–width (brick 1): the restriction substrate

The classical *exponential* resolution size lower bound for expander-Tseitin goes
through the Ben-Sasson–Wigderson **size–width** amplification: a small refutation
can be turned into a *narrow* one by random restrictions, so the width lower bound
(`TseitinRootBound.resolution_width_lower_bound`, `proofWidth ≥ c·t`) forces
exponential size.  The first brick is the **restriction operation on clauses** and
the satisfaction/width bookkeeping the derivation-level restriction recursion
(brick 2) will need.

A restriction `ρ : Edge → Option (ZMod 2)` fixes the values of some edges.  Each
literal `(e,b)` is then exactly one of:

* **satisfied** (`ρ e = b`): the literal is forced true, so any clause containing
  it becomes `⊤` and leaves the formula;
* **falsified** (`ρ e = b+1`): the literal is forced false and is dropped;
* **live** (`ρ e = none`): the literal survives.

`liveClause ρ C` keeps the live literals.  The two facts brick 2 needs are proved
here: restriction never increases width (`liveClause_width_le`), and for any
assignment consistent with `ρ`, satisfying `C` is the same as `C` being satisfied
outright by `ρ` or its live part being satisfied (`clauseSat_iff`).  These hold
because in `ZMod 2` a fixed edge value either matches a literal's asserted value or
is its complement — the trichotomy `lit_trichotomy`.

**UPDATE — bricks 2 and 3 are now built** (this note was previously "not here"):
* brick 2, the derivation-level restriction `Der ↦ Der|ρ` (`size`/`proofWidth` non-increasing,
  mapping refutations of the axioms to refutations of the restricted axioms), is
  `TseitinRestriction.restrict_W` in `ComputationalDepthExpanderTseitinRestrictDerivation` (proved);
* brick 3, the logarithmic size→width recursion (size-`S` tree-like refutation → width
  `≤ w₀ + ⌈log₂ S⌉`), is `TseitinRestriction.tree_width_le` in
  `ComputationalDepthExpanderTseitinSizeWidth` (proved, driven by `restrict_W`);
* combined with `proofWidth ≥ c·t` this yields `size > 2^{c·t−w₀−1}`
  (`TseitinResolution.tseitinCNF_exp_size`).
See `ComputationalDepthExpanderTseitinBSWManifest` for the full machine-checked chain.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinRestriction

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open scoped BigOperators

variable {Edge : Type*} [DecidableEq Edge]

/-- A partial assignment of edge values (a *restriction*). -/
abbrev Restriction (Edge : Type*) := Edge → Option (ZMod 2)

/-- An assignment `a` is consistent with `ρ`: it agrees wherever `ρ` is defined. -/
def Consistent (ρ : Restriction Edge) (a : Edge → ZMod 2) : Prop :=
  ∀ e v, ρ e = some v → a e = v

/-- A literal `(e,b)` is **satisfied** by `ρ` when `ρ` forces `a e = b`. -/
def litSatisfied (ρ : Restriction Edge) (l : TLit Edge) : Prop := ρ l.1 = some l.2

/-- A literal `(e,b)` is **falsified** by `ρ` when `ρ` forces `a e = b+1 ≠ b`. -/
def litFalsified (ρ : Restriction Edge) (l : TLit Edge) : Prop := ρ l.1 = some (l.2 + 1)

/-- A literal is **live** when `ρ` leaves its edge unassigned. -/
def litLive (ρ : Restriction Edge) (l : TLit Edge) : Prop := ρ l.1 = none

/-- The clause restricted by `ρ`: keep exactly the live literals (falsified ones
are dropped; a clause with a satisfied literal is handled by `clauseSatisfied`). -/
def liveClause (ρ : Restriction Edge) (C : ResolutionClause (TLit Edge)) :
    ResolutionClause (TLit Edge) :=
  C.filter (fun l => ρ l.1 = none)

/-- `C` is satisfied by `ρ` when it contains a satisfied literal (so `C|ρ = ⊤`). -/
def clauseSatisfied (ρ : Restriction Edge) (C : ResolutionClause (TLit Edge)) : Prop :=
  ∃ l ∈ C, ρ l.1 = some l.2

/-- **Trichotomy.**  Over `ZMod 2`, every literal is exactly live, satisfied, or
falsified under `ρ` (because a fixed edge value is either the literal's asserted
value or its complement). -/
theorem lit_trichotomy (ρ : Restriction Edge) (l : TLit Edge) :
    litLive ρ l ∨ litSatisfied ρ l ∨ litFalsified ρ l := by
  unfold litLive litSatisfied litFalsified
  rcases h : ρ l.1 with _ | v
  · exact Or.inl rfl
  · have hzz : ∀ x y : ZMod 2, x = y ∨ x = y + 1 := by decide
    rcases hzz v l.2 with hv | hv
    · exact Or.inr (Or.inl (by rw [hv]))
    · exact Or.inr (Or.inr (by rw [hv]))

/-- **Restriction never increases width.** -/
theorem liveClause_width_le (ρ : Restriction Edge) (C : ResolutionClause (TLit Edge)) :
    (liveClause ρ C).width ≤ C.width := by
  unfold ResolutionClause.width liveClause
  exact Finset.card_filter_le _ _

/-- A live literal of `C` belongs to `liveClause ρ C`. -/
theorem mem_liveClause {ρ : Restriction Edge} {C : ResolutionClause (TLit Edge)}
    {l : TLit Edge} (hlC : l ∈ C) (hlive : litLive ρ l) : l ∈ liveClause ρ C :=
  Finset.mem_filter.mpr ⟨hlC, hlive⟩

/-- `liveClause ρ C ⊆ C`. -/
theorem liveClause_subset (ρ : Restriction Edge) (C : ResolutionClause (TLit Edge)) :
    liveClause ρ C ⊆ C := Finset.filter_subset _ _

/-- A satisfied literal is true under any consistent assignment. -/
theorem tsat_of_litSatisfied {ρ : Restriction Edge} {a : Edge → ZMod 2}
    (hcons : Consistent ρ a) {l : TLit Edge} (h : litSatisfied ρ l) : TSat a l :=
  hcons l.1 l.2 h

/-- A falsified literal is false under any consistent assignment. -/
theorem not_tsat_of_litFalsified {ρ : Restriction Edge} {a : Edge → ZMod 2}
    (hcons : Consistent ρ a) {l : TLit Edge} (h : litFalsified ρ l) : ¬ TSat a l := by
  intro ht
  have hav : a l.1 = l.2 + 1 := hcons l.1 (l.2 + 1) h
  rw [show a l.1 = l.2 from ht] at hav
  exact (by decide : ∀ x : ZMod 2, x ≠ x + 1) l.2 hav

/-- **Satisfaction transfer (the key lemma for brick 2).**  For an assignment `a`
consistent with `ρ`, the clause `C` is satisfied iff it is satisfied outright by
`ρ` or its live part is satisfied by `a`. -/
theorem clauseSat_iff {ρ : Restriction Edge} {a : Edge → ZMod 2} (hcons : Consistent ρ a)
    (C : ResolutionClause (TLit Edge)) :
    SemanticMeasure.clauseSat TSat a C ↔
      clauseSatisfied ρ C ∨ SemanticMeasure.clauseSat TSat a (liveClause ρ C) := by
  constructor
  · rintro ⟨l, hlC, hl⟩
    rcases lit_trichotomy ρ l with hlive | hsat | hfals
    · exact Or.inr ⟨l, mem_liveClause hlC hlive, hl⟩
    · exact Or.inl ⟨l, hlC, hsat⟩
    · exact absurd hl (not_tsat_of_litFalsified hcons hfals)
  · rintro (⟨l, hlC, hsat⟩ | ⟨l, hlF, hl⟩)
    · exact ⟨l, hlC, tsat_of_litSatisfied hcons hsat⟩
    · exact ⟨l, liveClause_subset ρ C hlF, hl⟩

end PallLean.Paper93.DeepMath.PathB.TseitinRestriction

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.lit_trichotomy
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.liveClause_width_le
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinRestriction.clauseSat_iff
