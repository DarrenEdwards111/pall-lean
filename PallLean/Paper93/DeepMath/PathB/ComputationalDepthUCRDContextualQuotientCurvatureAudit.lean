import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUCRDGlobalGluingObstructionAudit

/-!
# UCRD contextual-quotient curvature audit

The Boolean-section audit proves that honest restrictions of one global DAG
meaning always glue.  The next N-Frame candidate is therefore a family of
context-dependent observer quotients: different bubbles may identify different
underlying points.

This file separates two facts that must not be conflated:

* context-dependent equivalence relations can carry a genuine global gluing
  obstruction;
* that obstruction can already be manufactured by one-bit, context-local
  labels, with no SAT computation and no expensive dynamics.

Conversely, every quotient induced by one context-independent label glues to
the global equality relation on labels.  Thus quotient curvature is a real
mathematical phenomenon, but curvature alone is not a complexity lower bound.
A separating use would additionally have to prove that bounded computation
forces a particular curved quotient while forbidding the cheap context-local
relabeling exhibited here.
-/

namespace PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit

universe u v w

variable {Context : Type u} {Point : Type v}

/-- A context-indexed candidate observational equivalence relation. -/
structure ContextualQuotient (visible : Context → Point → Prop) where
  rel : Context → Point → Point → Prop
  reflOn : ∀ i x, visible i x → rel i x x
  symmOn : ∀ i x y, visible i x → visible i y → rel i x y → rel i y x
  transOn : ∀ i x y z, visible i x → visible i y → visible i z →
    rel i x y → rel i y z → rel i x z

/-- One global equivalence relation realizes every local quotient exactly on
the pairs simultaneously visible in that context. -/
def GloballyRealizable {visible : Context → Point → Prop}
    (Q : ContextualQuotient visible) : Prop :=
  ∃ R : Point → Point → Prop, Equivalence R ∧
    ∀ i x y, visible i x → visible i y → (R x y ↔ Q.rel i x y)

/-- Genuine quotient curvature: all local relations are equivalences on their
bubbles, but no single global equivalence relation restricts to all of them. -/
def HasQuotientCurvature {visible : Context → Point → Prop}
    (Q : ContextualQuotient visible) : Prop :=
  ¬ GloballyRealizable Q

/-- Context-local labels always induce a valid contextual quotient by equality
of the visible labels. -/
def quotientOfLabels {visible : Context → Point → Prop} {Code : Type w}
    (label : Context → Point → Code) : ContextualQuotient visible where
  rel := fun i x y ↦ label i x = label i y
  reflOn := by intro i x hx; rfl
  symmOn := by intro i x y hx hy h; exact h.symm
  transOn := by intro i x y z hx hy hz hxy hyz; exact hxy.trans hyz

/-- A quotient induced by a context-independent summary always glues. -/
theorem uniformLabel_globallyRealizable
    {visible : Context → Point → Prop} {Code : Type w}
    (label : Point → Code) :
    GloballyRealizable
      (quotientOfLabels (visible := visible) (fun _ x ↦ label x)) := by
  refine ⟨fun x y ↦ label x = label y, ?_, ?_⟩
  · exact ⟨fun _ ↦ rfl, fun {_ _} h ↦ h.symm,
      fun {_ _ _} hxy hyz ↦ hxy.trans hyz⟩
  · intro i x y hx hy
    rfl

/-! ## The minimal three-bubble obstruction -/

inductive TriangleContext
  | ab | bc | ac
  deriving DecidableEq

inductive TrianglePoint
  | a | b | c
  deriving DecidableEq

/-- Three pairwise-overlapping observer bubbles arranged around a triangle. -/
def triangleVisible : TriangleContext → TrianglePoint → Prop
  | .ab, .a | .ab, .b => True
  | .bc, .b | .bc, .c => True
  | .ac, .a | .ac, .c => True
  | _, _ => False

/-- One bit per bubble: `a` and `b` agree in `ab`, `b` and `c` agree in
`bc`, while `a` and `c` are distinguished in `ac`. -/
def triangleLabel : TriangleContext → TrianglePoint → Bool
  | .ab, _ => false
  | .bc, _ => false
  | .ac, .a => false
  | .ac, _ => true

def triangleQuotient : ContextualQuotient triangleVisible :=
  quotientOfLabels triangleLabel

theorem triangle_ab_identifies :
    triangleQuotient.rel .ab .a .b := by
  rfl

theorem triangle_bc_identifies :
    triangleQuotient.rel .bc .b .c := by
  rfl

theorem triangle_ac_separates :
    ¬ triangleQuotient.rel .ac .a .c := by
  simp [triangleQuotient, quotientOfLabels, triangleLabel]

/-- The three cheap local quotients cannot be restrictions of one global
equivalence relation: global transitivity would identify `a` with `c`. -/
theorem triangle_hasQuotientCurvature :
    HasQuotientCurvature triangleQuotient := by
  rintro ⟨R, hR, hrestrict⟩
  have hab : R .a .b :=
    (hrestrict .ab .a .b (by trivial) (by trivial)).2
      triangle_ab_identifies
  have hbc : R .b .c :=
    (hrestrict .bc .b .c (by trivial) (by trivial)).2
      triangle_bc_identifies
  have hac : R .a .c := hR.trans hab hbc
  have hlocal : triangleQuotient.rel .ac .a .c :=
    (hrestrict .ac .a .c (by trivial) (by trivial)).1 hac
  exact triangle_ac_separates hlocal

/-- The obstruction is already realized by Boolean context-local summaries;
no large code space, SAT oracle, or expensive update process is involved. -/
theorem oneBit_contextLocal_curvature_exists :
    ∃ label : TriangleContext → TrianglePoint → Bool,
      HasQuotientCurvature
        (quotientOfLabels (visible := triangleVisible) label) := by
  exact ⟨triangleLabel, triangle_hasQuotientCurvature⟩

/-- Uniform observer labels cannot reproduce the curved triangle quotient. -/
theorem no_uniformLabel_realizes_triangle
    {Code : Type w} (label : TrianglePoint → Code) :
    quotientOfLabels (visible := triangleVisible) (fun _ x ↦ label x) ≠
      triangleQuotient := by
  intro heq
  have hglobal : GloballyRealizable triangleQuotient := by
    rw [← heq]
    exact uniformLabel_globallyRealizable label
  exact triangle_hasQuotientCurvature hglobal

end PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit

#print axioms PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit.uniformLabel_globallyRealizable
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit.triangle_hasQuotientCurvature
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit.oneBit_contextLocal_curvature_exists
#print axioms PallLean.Paper93.DeepMath.PathB.UCRDContextualQuotientCurvatureAudit.no_uniformLabel_realizes_triangle
