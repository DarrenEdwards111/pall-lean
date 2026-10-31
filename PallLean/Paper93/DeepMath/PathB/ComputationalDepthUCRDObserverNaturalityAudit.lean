import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDPolynomialObserverCurvatureNoGo

/-!
# UCRD observer-naturality audit

The polynomial-observer audit shows that context-dependent readout creates
quotient curvature even with injective global storage and constant work.  This
file isolates the naturality law that repairs the gluing theorem:

> whenever one underlying point is visible in two contexts, its decoded label
> is the same in both contexts.

Under this law, local labels glue to one global label, and their equality
quotients glue to one global equivalence relation.  Thus naturality is a valid
P-side *sufficient condition* for flatness.

But polynomial runtime does not imply naturality.  The constant-work triangle
observer violates it at point `c`: context `bc` reads `false`, while context
`ac` reads `true`.  A context-blind decoder does imply naturality, but imposing
context blindness would discard the adaptive future-context behavior the route
was intended to model.

The result is therefore another exact boundary: naturality supplies the missing
mathematical bridge, but it is an additional semantic restriction, not a
consequence of polynomial resources.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDObserverNaturalityAudit

open PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit
open PallLean.Paper93.DeepMath.PathB.UCRDPolynomialObserverCurvatureNoGo

universe u v w z

variable {Context : Type u} {Point : Type v} {Code : Type w}

attribute [local instance] Classical.propDecidable

/-- Fixed-code overlap naturality: a point has the same operational label in
every context in which that point is visible. -/
def OverlapNaturalLabel (visible : Context → Point → Prop)
    (label : Context → Point → Code) : Prop :=
  ∀ i j x, visible i x → visible j x → label i x = label j x

/-- Glue natural local labels by selecting one visible context; use a default
code outside the cover. -/
noncomputable def gluedLabel [Inhabited Code]
    (visible : Context → Point → Prop) (label : Context → Point → Code) :
    Point → Code :=
  fun x ↦ if h : ∃ i, visible i x then label (Classical.choose h) x
    else default

/-- Naturality makes the chosen global label agree with every visible local
label. -/
theorem gluedLabel_eq [Inhabited Code]
    {visible : Context → Point → Prop} {label : Context → Point → Code}
    (hnat : OverlapNaturalLabel visible label)
    (i : Context) (x : Point) (hx : visible i x) :
    gluedLabel visible label x = label i x := by
  have hex : ∃ j, visible j x := ⟨i, hx⟩
  unfold gluedLabel
  rw [dif_pos hex]
  exact hnat (Classical.choose hex) i x (Classical.choose_spec hex) hx

/-- **Naturality-to-flatness bridge.**  Contextual equality quotients induced
by overlap-natural labels always glue to one global equivalence relation. -/
theorem naturalLabel_globallyRealizable [Inhabited Code]
    {visible : Context → Point → Prop} {label : Context → Point → Code}
    (hnat : OverlapNaturalLabel visible label) :
    GloballyRealizable (quotientOfLabels (visible := visible) label) := by
  let global : Point → Code := gluedLabel visible label
  refine ⟨fun x y ↦ global x = global y, ?_, ?_⟩
  · exact ⟨fun _ ↦ rfl, fun {_ _} h ↦ h.symm,
      fun {_ _ _} hxy hyz ↦ hxy.trans hyz⟩
  · intro i x y hx hy
    change (global x = global y) ↔ (label i x = label i y)
    rw [show global x = label i x from gluedLabel_eq hnat i x hx]
    rw [show global y = label i y from gluedLabel_eq hnat i y hy]

/-- Naturality for the labels produced by a polynomial context observer. -/
def ReadoutNatural
    {Context : Type u} {Point : Type v} {State : Type w} {Code : Type z}
    {visible : Context → Point → Prop}
    (O : PolynomialContextObserver Context Point State Code) : Prop :=
  OverlapNaturalLabel visible O.label

/-- Every natural polynomial observer induces a flat quotient.  Notice that
the proof uses naturality, not the observer's polynomial budget. -/
theorem naturalPolynomialObserver_flat
    {Context : Type u} {Point : Type v} {State : Type w} {Code : Type z}
    [Inhabited Code] {visible : Context → Point → Prop}
    (O : PolynomialContextObserver Context Point State Code)
    (hnat : ReadoutNatural (visible := visible) O) :
    GloballyRealizable (O.inducedQuotient (visible := visible)) :=
  naturalLabel_globallyRealizable hnat

/-- A context-blind decoder is a simple sufficient source of naturality. -/
def ContextBlind
    {Context : Type u} {Point : Type v} {State : Type w} {Code : Type z}
    (O : PolynomialContextObserver Context Point State Code) : Prop :=
  ∃ read : State → Code, ∀ i s, O.decode i s = read s

theorem contextBlind_readoutNatural
    {Context : Type u} {Point : Type v} {State : Type w} {Code : Type z}
    {visible : Context → Point → Prop}
    (O : PolynomialContextObserver Context Point State Code)
    (hblind : ContextBlind O) : ReadoutNatural (visible := visible) O := by
  obtain ⟨read, hread⟩ := hblind
  intro i j x hi hj
  change O.decode i (O.encode x) = O.decode j (O.encode x)
  rw [hread i, hread j]

/-- The constant-work curved observer violates naturality on the overlap point
`c`: this is the precise operational source of its quotient curvature. -/
theorem triangleObserver_not_readoutNatural :
    ¬ ReadoutNatural (visible := triangleVisible)
        trianglePolynomialObserver := by
  intro hnat
  have h := hnat TriangleContext.bc TriangleContext.ac TrianglePoint.c
    (by trivial) (by trivial)
  change false = true at h
  contradiction

/-- Polynomial resources do not force the naturality premise needed by the
flatness bridge. -/
theorem not_all_polynomialObservers_natural :
    ¬ (∀ O : PolynomialContextObserver
          TriangleContext TrianglePoint TrianglePoint Bool,
        ReadoutNatural (visible := triangleVisible) O) := by
  intro hall
  exact triangleObserver_not_readoutNatural (hall trianglePolynomialObserver)

/-- Consequently the curved observer cannot possess a context-blind decoder. -/
theorem triangleObserver_not_contextBlind :
    ¬ ContextBlind trianglePolynomialObserver := by
  intro hblind
  exact triangleObserver_not_readoutNatural
    (contextBlind_readoutNatural trianglePolynomialObserver hblind)

end PallLean.Paper93.DeepMath.PathB.UCRDObserverNaturalityAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDObserverNaturalityAudit.naturalLabel_globallyRealizable
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDObserverNaturalityAudit.naturalPolynomialObserver_flat
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDObserverNaturalityAudit.triangleObserver_not_readoutNatural
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDObserverNaturalityAudit.not_all_polynomialObservers_natural
