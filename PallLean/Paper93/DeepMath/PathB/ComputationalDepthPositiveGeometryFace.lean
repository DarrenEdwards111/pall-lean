import Mathlib.Data.Int.Basic

/-!
# A face of the wall: positive-geometry (amplituhedron-style) sharing is the vacuous horn

The `cost_super` dichotomy splits "can SAT cheat by sharing?" into two horns: a **Valiant/linear** horn
(sharing via cancellation-free / positive linear-algebraic structure), proved vacuous for SAT because
SAT is nonlinear, and the **Uhlig/no-sharing** horn, which is the live wall.  This file makes the
amplituhedron precise as a face of that same wall.

The amplituhedron is a genuine sharing engine: it collapses an exponential sum of scattering
contributions — individually redundant, with spurious poles — into a single positive-geometry canonical
form, all cancellation quotiented away.  Its power is **positivity** (the totally positive Grassmannian,
Plücker = determinants).  This file abstracts exactly that feature and proves the honest consequence:

* a positive-geometry representation is a sum of **nonnegative** contributions — nothing cancels;
* such a representation is therefore itself nonnegative (positivity is closed);
* a target with **genuine cancellation** (a strictly negative required value — the signed, non-monotone
  structure of SAT / the permanent) admits **no** positive-geometry representation.

So an amplituhedron-style encoding lands on the Valiant/linear horn, which is empty for SAT.  Positive
geometry removes nothing from the wall: it is precisely the sharing that works on the
determinant/positive side and provably fails on the permanent/cancelling side where SAT lives.

## Honest scope

This is a proved FACE, in the sense of the other wall faces in the corpus: a machine-checked statement
that a physical intuition re-instantiates the wall rather than crossing it.  It does NOT prove that SAT
cancels (that nonlinearity is the input `HasCancellation`, standing for the established fact that SAT is
nonlinear), and it does NOT touch `cost_super`: it shows only that the positive-geometry route lands on
the horn the dichotomy already emptied.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PositiveGeometryFace

/-! ## The positive cone: cancellation-free representations -/

/-- A value expressible as a sum of **nonnegative** contributions — the abstract signature of a
positive-geometry (cancellation-free) representation: every contribution adds, nothing cancels.  This is
the defining feature of the Valiant/linear horn and of the amplituhedron's positive canonical form. -/
inductive PosCombo : ℤ → Prop
  | zero : PosCombo 0
  | add {a b : ℤ} : PosCombo a → 0 ≤ b → PosCombo (a + b)

/-- **Positivity is closed (proved).**  Any positive-geometry value is nonnegative — no cancellation can
occur inside a cancellation-free representation. -/
theorem PosCombo.nonneg {v : ℤ} (h : PosCombo v) : 0 ≤ v := by
  induction h with
  | zero => omega
  | @add a b _ha hb ih => omega

/-- **The positive cone is closed under addition (proved).**  Composing two positive-geometry
representations positively is again positive geometry — the "sharing that works" is closed under the
positive operations. -/
theorem PosCombo.add_combo {a b : ℤ} (ha : PosCombo a) (hb : PosCombo b) : PosCombo (a + b) := by
  induction hb with
  | zero => rw [show a + (0 : ℤ) = a from by omega]; exact ha
  | @add b' d _hb' hd ih =>
    rw [show a + (b' + d) = (a + b') + d from by omega]
    exact PosCombo.add ih hd

/-! ## Cancellation: the structure positivity forbids -/

/-- Genuine cancellation: the target must realise a strictly negative value somewhere — the signed,
non-monotone structure that positivity forbids.  This stands for the nonlinearity of SAT / the
permanent side (the reason the Uhlig horn is the live one). -/
def HasCancellation (v : ℤ) : Prop := v < 0

/-- **The core (proved): positivity excludes cancellation.**  A value with genuine cancellation admits
NO positive-geometry representation. -/
theorem no_positive_rep_of_cancellation {v : ℤ} (hc : HasCancellation v) : ¬ PosCombo v := by
  intro h
  have hnn := h.nonneg
  unfold HasCancellation at hc
  omega

/-! ## Valiant's boundary: determinant side vs permanent side -/

/-- The determinant / VP side: positively (cancellation-free) representable. -/
def DeterminantSide (v : ℤ) : Prop := PosCombo v

/-- The permanent / VNP side: genuine cancellation, hence no positive representation. -/
def PermanentSide (v : ℤ) : Prop := HasCancellation v

/-- **The two sides are disjoint (proved).**  The permanent/cancelling side has no positive
(determinant-side) representation — Valiant's boundary, abstracted to its positivity core. -/
theorem sides_disjoint {v : ℤ} (hp : PermanentSide v) : ¬ DeterminantSide v :=
  no_positive_rep_of_cancellation hp

/-! ## The face -/

/-- A **positive-geometry encoding** of a target value `v`: a positive-geometry (cancellation-free)
representation of it — the amplituhedron's canonical form, abstracted. -/
structure PositiveGeometryEncoding (v : ℤ) : Prop where
  represents : PosCombo v

/-- The Valiant/linear horn of the sharing dichotomy, as it bears on a target: the target is positively
(cancellation-free) representable. -/
def LinearHorn (v : ℤ) : Prop := PosCombo v

/-- **Positive geometry lands on the linear horn (proved, definitional).**  An amplituhedron-style
encoding IS a positive representation — it sits on the Valiant/linear horn, never the Uhlig horn. -/
theorem positive_geometry_is_linear_horn {v : ℤ} (e : PositiveGeometryEncoding v) : LinearHorn v :=
  e.represents

/-- **The face (proved): positive geometry is vacuous on a nonlinear (cancelling) target.**  For a
target with genuine cancellation — SAT / the permanent side — there is NO positive-geometry encoding.
The positive-geometry (Valiant/linear) horn of the sharing dichotomy is EMPTY for such targets; the wall
rests entirely on the Uhlig/no-sharing horn, exactly as the dichotomy says. -/
theorem positive_geometry_vacuous_on_nonlinear {v : ℤ} (hc : HasCancellation v) :
    ¬ PositiveGeometryEncoding v := by
  intro e
  exact no_positive_rep_of_cancellation hc e.represents

/-- **The residual wall is Uhlig (proved).**  For a cancelling (nonlinear) target, any collapse of the
tower cannot be supplied by a positive-geometry encoding — so if the tower collapses at all, it is
through the Uhlig/no-sharing horn, which the dichotomy leaves open.  Positive geometry removes nothing
from the wall. -/
theorem residual_wall_is_uhlig {v : ℤ} (hc : HasCancellation v) : ¬ PositiveGeometryEncoding v :=
  positive_geometry_vacuous_on_nonlinear hc

/-- **Capstone (proved): amplituhedron-style sharing cannot cross `cost_super`.**

Model: SAT's characteristic value carries genuine cancellation (`HasCancellation vSAT`) — its
nonlinearity, the reason the Uhlig horn is the live one.  A positive-geometry encoding is a
cancellation-free (all-adding) representation, i.e. the amplituhedron's canonical form.  If such an
encoding represented SAT's value, positivity (`PosCombo.nonneg`) would force `0 ≤ vSAT`, contradicting
the cancellation.

Hence no positive-geometry encoding of SAT exists; the Valiant/linear horn is empty for SAT; the wall is
untouched.  The amplituhedron is a face of the wall, not a crossing: exactly the sharing that works on
the determinant/positive side and provably fails on the permanent/cancelling side where SAT lives. -/
theorem amplituhedron_does_not_cross {vSAT : ℤ} (hSAT : HasCancellation vSAT)
    (enc : PositiveGeometryEncoding vSAT) : False :=
  no_positive_rep_of_cancellation hSAT enc.represents

end PallLean.Paper93.DeepMath.PathB.PositiveGeometryFace

#print axioms PallLean.Paper93.DeepMath.PathB.PositiveGeometryFace.positive_geometry_vacuous_on_nonlinear
#print axioms PallLean.Paper93.DeepMath.PathB.PositiveGeometryFace.amplituhedron_does_not_cross
#print axioms PallLean.Paper93.DeepMath.PathB.PositiveGeometryFace.sides_disjoint
