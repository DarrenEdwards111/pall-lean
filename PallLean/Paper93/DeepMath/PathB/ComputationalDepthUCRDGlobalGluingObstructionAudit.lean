import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDNodeLocalPotentialWall

/-!
# UCRD global gluing-obstruction audit

After node-local potentials are exhausted, the natural N-Frame candidate is a
global obstruction to consistently gluing context-dependent meanings.  This
file tests the most direct version: local Boolean sections obtained by
restricting globally defined DAG wire functions to observer contexts.

The result is exact and cautionary:

* define arbitrary context domains and Boolean local sections;
* define pairwise compatibility on every overlap;
* construct a global Boolean function from every compatible family;
* prove compatibility iff global realizability;
* therefore prove that a compatible Boolean gluing obstruction is impossible;
* instantiate the result on every wire of every semantic DAG/tower.

The key point is mathematical, not representational: ordinary Boolean-valued
functions form a sheaf on this discrete context cover.  A DAG wire already has
one global meaning, and all honest restrictions inherit it, so their Cech-style
obstruction is identically zero.

## Honest scope

This does not eliminate genuinely observer-relative curvature.  It proves that
such curvature cannot come from merely restricting the existing global wire
functions.  A non-flat object must quotient or coarse-grain meanings
differently in different contexts, and then separately prove that the quotient
is forced by bounded computation rather than chosen by definition.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDGlobalGluingObstructionAudit

open PallLean.Paper93.DeepMath.PathB.EntanglementRuler

attribute [local instance] Classical.propDecidable

universe u v

variable {Context : Type u} {Point : Type v}

/-- A Boolean section whose domain may vary with observer context. -/
structure LocalSection (visible : Context → Point → Prop) where
  value : ∀ i x, visible i x → Bool

/-- Local meanings agree wherever two observer contexts overlap. -/
def Compatible {visible : Context → Point → Prop}
    (s : LocalSection visible) : Prop :=
  ∀ i j x (hi : visible i x) (hj : visible j x),
    s.value i x hi = s.value j x hj

/-- A global Boolean meaning realizes every local contextual section. -/
def Realizes {visible : Context → Point → Prop}
    (F : Point → Bool) (s : LocalSection visible) : Prop :=
  ∀ i x (hx : visible i x), F x = s.value i x hx

/-- The local family admits one global observer-independent realization. -/
def GloballyRealizable {visible : Context → Point → Prop}
    (s : LocalSection visible) : Prop :=
  ∃ F : Point → Bool, Realizes F s

/-- Glue a compatible family by choosing any visible context at each point;
outside the cover use `false`.  Compatibility makes the choice irrelevant. -/
noncomputable def gluedValue {visible : Context → Point → Prop}
    (s : LocalSection visible) : Point → Bool :=
  fun x ↦ if h : ∃ i, visible i x then
    s.value (Classical.choose h) x (Classical.choose_spec h)
  else false

/-- Pairwise overlap compatibility is sufficient for global realization. -/
theorem compatible_gluedValue_realizes
    {visible : Context → Point → Prop} (s : LocalSection visible)
    (hcomp : Compatible s) :
    Realizes (gluedValue s) s := by
  intro i x hx
  have hex : ∃ j, visible j x := ⟨i, hx⟩
  unfold gluedValue
  rw [dif_pos hex]
  exact hcomp (Classical.choose hex) i x
    (Classical.choose_spec hex) hx

/-- Every compatible Boolean local family glues globally. -/
theorem globallyRealizable_of_compatible
    {visible : Context → Point → Prop} (s : LocalSection visible)
    (hcomp : Compatible s) : GloballyRealizable s :=
  ⟨gluedValue s, compatible_gluedValue_realizes s hcomp⟩

/-- Any globally realized family is automatically compatible on overlaps. -/
theorem compatible_of_globallyRealizable
    {visible : Context → Point → Prop} (s : LocalSection visible)
    (hglobal : GloballyRealizable s) : Compatible s := by
  obtain ⟨F, hF⟩ := hglobal
  intro i j x hi hj
  exact (hF i x hi).symm.trans (hF j x hj)

/-- **Discrete Boolean gluing theorem.**  Compatibility is exactly global
realizability. -/
theorem compatible_iff_globallyRealizable
    {visible : Context → Point → Prop} (s : LocalSection visible) :
    Compatible s ↔ GloballyRealizable s :=
  ⟨globallyRealizable_of_compatible s,
    compatible_of_globallyRealizable s⟩

/-- The proposed elementary gluing obstruction: compatible local meanings
that nevertheless possess no global meaning. -/
def HasGluingObstruction {visible : Context → Point → Prop}
    (s : LocalSection visible) : Prop :=
  Compatible s ∧ ¬ GloballyRealizable s

/-- Such an obstruction is impossible for ordinary Boolean-valued local
functions. -/
theorem no_Boolean_gluingObstruction
    {visible : Context → Point → Prop} (s : LocalSection visible) :
    ¬ HasGluingObstruction s := by
  rintro ⟨hcomp, hnot⟩
  exact hnot (globallyRealizable_of_compatible s hcomp)

/-! ## Instantiation on global DAG wire meanings -/

/-- Restrict one global Boolean meaning to arbitrary observer contexts. -/
def restrictGlobal (visible : Context → Point → Prop) (F : Point → Bool) :
    LocalSection visible where
  value := fun _ x _ ↦ F x

/-- Honest restrictions retain their original global realization. -/
theorem restrictGlobal_globallyRealizable
    (visible : Context → Point → Prop) (F : Point → Bool) :
    GloballyRealizable (restrictGlobal visible F) := by
  exact ⟨F, by intro i x hx; rfl⟩

/-- Honest restrictions are flat/compatible on every overlap. -/
theorem restrictGlobal_compatible
    (visible : Context → Point → Prop) (F : Point → Bool) :
    Compatible (restrictGlobal visible F) :=
  compatible_of_globallyRealizable _
    (restrictGlobal_globallyRealizable visible F)

/-- A semantic DAG wire viewed through arbitrary assignment contexts. -/
def dagWireSection {k b n : ℕ} (C : EntangledTower k b n)
    (visible : Context → (Fin n → Bool) → Prop) (g : ℕ) :
    LocalSection visible :=
  restrictGlobal visible (C.wireFn g)

/-- Every DAG wire's contextual views glue to its existing global wire
function. -/
theorem dagWire_globallyRealizable {k b n : ℕ}
    (C : EntangledTower k b n)
    (visible : Context → (Fin n → Bool) → Prop) (g : ℕ) :
    GloballyRealizable (dagWireSection C visible g) :=
  restrictGlobal_globallyRealizable visible (C.wireFn g)

/-- Therefore no honest restriction family of a DAG wire carries a gluing
obstruction, regardless of its fan-out or context cover. -/
theorem dagWire_no_gluingObstruction {k b n : ℕ}
    (C : EntangledTower k b n)
    (visible : Context → (Fin n → Bool) → Prop) (g : ℕ) :
    ¬ HasGluingObstruction (dagWireSection C visible g) :=
  no_Boolean_gluingObstruction _

end PallLean.Paper93.DeepMath.PathB.UCRDGlobalGluingObstructionAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDGlobalGluingObstructionAudit.compatible_iff_globallyRealizable
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDGlobalGluingObstructionAudit.no_Boolean_gluingObstruction
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDGlobalGluingObstructionAudit.dagWire_globallyRealizable
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDGlobalGluingObstructionAudit.dagWire_no_gluingObstruction
