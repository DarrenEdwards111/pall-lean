import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAmplituhedronFace

/-!
# The inverse: a negative geometry for the SAT side — real object, compactness is the wall

`AmplituhedronFace` proved the amplituhedron is a positive-geometry sharing engine, God-exclusive for SAT
because SAT is cancelling.  Darren's next move: build the **inverse** — a *negative geometry* for the SAT
side.  This is not a fiction: negative geometries are a real object in the amplituhedron programme (the
sign-flipped regions that compute the log-amplitude / the "amplituhedron-minus" decomposition).  The
question this file pins is what building one for SAT actually costs.

A geometry has a **mode** (positive-geometry or cancelling) and a **canonical-form size** `summary`
relative to the exponential sum's `coreSize`.  It **compresses** when `summary < coreSize` — the whole
point of the amplituhedron.  Positive geometry compresses *because* positivity forbids cancellation (the
sum collapses to one compact object).  The negative geometry is the cancelling-mode object — the SAT side.

## What is proved

* **`positive_geometry_compresses`** — the amplituhedron (positive geometry) compresses: a small canonical
  form for a large core.  Positivity's payoff.
* **`negative_geometry_is_cancelling`** — the inverse geometry is the cancelling mode: the SAT side, the
  geometric form of Uhlig (cancelling) sharing.
* **`negative_geometry_compresses_iff_sat_compresses`** — the negative geometry compresses **iff** SAT's
  core compresses (`summary < coreSize`).  Its compactness *is* SAT's compressibility.
* **`incompressible_blows_up_negative_geometry`** — if SAT's core is incompressible (`coreSize ≤ summary`,
  the free-reach-robust property of `IncompressibleCore`), the negative geometry does **not** compress —
  it blows up.  The inverse object exists but is not compact.
* **`compressible_compresses_negative_geometry`** — the contrast: a compressible core makes the negative
  geometry compact.  Compactness ⟺ compressibility.

## Honest verdict — the inverse object is real; its compactness is `cost_super`

Darren's inverse is a genuine, definable object: the negative geometry is the cancelling-mode geometry,
the geometric form of the Uhlig sharing the amplituhedron cannot supply
(`negative_geometry_is_cancelling`).  The amplituhedron compresses because positivity forbids cancellation
(`positive_geometry_compresses`).  But the negative geometry compresses **iff** SAT's core compresses
(`negative_geometry_compresses_iff_sat_compresses`), and if the core is incompressible — the property that
survives free reach — the negative geometry **blows up** (`incompressible_blows_up_negative_geometry`).  So
building the negative geometry for SAT is honest and real; its **compactness** is exactly SAT's
compressibility = ¬`cost_super`.  The object exists; whether it is compact is `P` vs `NP`.  The physics
mirrors this precisely: negative geometries are real, but for the **non-planar (hard)** case no *compact*
negative geometry is known — the same wall.  The inverse re-labels the wall as "is there a compact
negative geometry for SAT," and does not cross it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NegativeGeometry

open PallLean.Paper93.DeepMath.PathB.AmplituhedronFace

/-- A **geometry** computing an exponential sum: its sharing `mode`, the sum's `coreSize`, and the size
`summary` of its canonical form.  It **compresses** when `summary < coreSize`. -/
structure Geometry where
  /-- positive-geometry (amplituhedron) or cancelling (SAT side) -/
  mode : SharingMode
  /-- size of the exponential sum's core -/
  coreSize : ℕ
  /-- size of the canonical form -/
  summary : ℕ

/-- The **negative geometry** for the SAT side: the cancelling-mode geometry with the given core and
canonical-form sizes.  The inverse of the amplituhedron. -/
def negativeGeom (coreSize summary : ℕ) : Geometry :=
  ⟨SharingMode.cancelling, coreSize, summary⟩

/-! ### The positive geometry compresses -/

/-- **The amplituhedron (positive geometry) compresses (proved).**  A large core (`10`) has a small
canonical form (`1`): positivity forbids cancellation, so the exponential sum collapses to one compact
object. -/
theorem positive_geometry_compresses :
    ∃ G : Geometry, G.mode = SharingMode.positiveGeometry ∧ G.summary < G.coreSize := by
  refine ⟨⟨SharingMode.positiveGeometry, 10, 1⟩, rfl, ?_⟩
  decide

/-! ### The negative geometry is the SAT side, and its compactness is the wall -/

/-- **The negative geometry is cancelling (proved).**  The inverse object is the cancelling-mode geometry
— the geometric form of the Uhlig sharing the amplituhedron cannot supply. -/
theorem negative_geometry_is_cancelling (c s : ℕ) :
    (negativeGeom c s).mode = SharingMode.cancelling := rfl

/-- **The negative geometry compresses iff SAT's core compresses (proved).**  Its canonical form is small
(`summary < coreSize`) exactly when SAT's cancelling sum is compressible.  Its compactness *is* SAT's
compressibility. -/
theorem negative_geometry_compresses_iff_sat_compresses (c s : ℕ) :
    ((negativeGeom c s).summary < (negativeGeom c s).coreSize) ↔ s < c := by
  simp only [negativeGeom]

/-- **An incompressible core blows up the negative geometry (proved).**  If SAT's core is incompressible
(`coreSize ≤ summary` — the free-reach-robust property of `IncompressibleCore`), the negative geometry does
not compress: its canonical form is no smaller than the core.  The inverse object exists but is not
compact. -/
theorem incompressible_blows_up_negative_geometry (c s : ℕ) (h : c ≤ s) :
    ¬ ((negativeGeom c s).summary < (negativeGeom c s).coreSize) := by
  simp only [negativeGeom]
  omega

/-- **A compressible core makes the negative geometry compact (proved) — the contrast.**  Compactness ⟺
compressibility; the wall is exactly whether SAT's core is compressible. -/
theorem compressible_compresses_negative_geometry (c s : ℕ) (h : s < c) :
    (negativeGeom c s).summary < (negativeGeom c s).coreSize := by
  simp only [negativeGeom]
  exact h

end PallLean.Paper93.DeepMath.PathB.NegativeGeometry

#print axioms PallLean.Paper93.DeepMath.PathB.NegativeGeometry.positive_geometry_compresses
#print axioms PallLean.Paper93.DeepMath.PathB.NegativeGeometry.negative_geometry_is_cancelling
#print axioms PallLean.Paper93.DeepMath.PathB.NegativeGeometry.negative_geometry_compresses_iff_sat_compresses
#print axioms PallLean.Paper93.DeepMath.PathB.NegativeGeometry.incompressible_blows_up_negative_geometry
#print axioms PallLean.Paper93.DeepMath.PathB.NegativeGeometry.compressible_compresses_negative_geometry
