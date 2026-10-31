import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalWeakBound

/-!
# A concrete Π★ instance from the diagonal: a separating measure for a self-referential target

Attacking the gap directly: build a concrete **non-natural separating measure** (a `Π★` instance) that
is LOW on every in-class object and HIGH on a self-referential target — the object `DischargePiStar`
says is equivalent to the separation, and which only restricted constructions (`MirrorRestricted`,
depth-4 SPDP) have realised.

The diagonal of `DiagonalWeakBound` gives one, concretely.  Let `f : Fin m → Fin m → Bool` enumerate
the in-class circuits.  Define

  `diagRank f g = 0` if `g` is enumerated, `1` otherwise.

This is a separating measure for the enumerated class: **`0` on every enumerated circuit, `1` on the
diagonal `diag f`** (which differs from all of them).  It is *non-natural* — defined by reference to
the enumeration, not a simple property of `g` — exactly the shape `separatingMeasure_nonnatural` forces.

## What is proved

* **`diagRank_enumerated`** — `diagRank f (f i) = 0`: LOW on every in-class circuit.
* **`diagRank_diag`** — `diagRank f (diag f) = 1`: HIGH on the self-referential target.
* **`diagRank_separates`** — `diagRank f (f i) < diagRank f (diag f)`: the measure strictly separates
  the target from the whole in-class enumeration.  A concrete `Π★` instance.

## Honest scope

This is a *real* concrete non-natural separating measure — but restricted, like `MirrorRestricted`: it
separates `diag f` from a *finite enumeration* `f`, and the diagonal is defined by that enumeration
(coverage = enumeration size, the linear cap of `DiagonalWeakBound`).  It does not reach the general
`P/poly` class or a fixed natural target: the enumeration is not all of `P/poly`, and scaling it to the
full class is the open problem (`cost_super`).  So this pushes the concrete `Π★` construction one more
step — a self-referential target with an explicit separating measure — without crossing the wall.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PiStarDiagonal

open PallLean.Paper93.DeepMath.PathB.DiagonalWeakBound
open Classical

/-- **The diagonal separating measure (Π★ instance).**  `0` on enumerated circuits, `1` otherwise —
non-natural by construction (it references the enumeration). -/
noncomputable def diagRank {m : ℕ} (f : Fin m → Fin m → Bool) (g : Fin m → Bool) : ℕ :=
  if (∃ i, g = f i) then 0 else 1

/-- **LOW on every in-class circuit (proved).** -/
theorem diagRank_enumerated {m : ℕ} (f : Fin m → Fin m → Bool) (i : Fin m) :
    diagRank f (f i) = 0 := by
  unfold diagRank
  exact if_pos ⟨i, rfl⟩

/-- **HIGH on the self-referential target (proved).**  The diagonal differs from every enumerated
circuit (`diag_differs`), so it is not enumerated. -/
theorem diagRank_diag {m : ℕ} (f : Fin m → Fin m → Bool) : diagRank f (diag f) = 1 := by
  unfold diagRank
  apply if_neg
  intro h
  cases h with
  | intro i hi => exact diag_differs f i hi

/-- **The measure strictly separates the target from the whole enumeration (proved) — a concrete Π★
instance.** -/
theorem diagRank_separates {m : ℕ} (f : Fin m → Fin m → Bool) (i : Fin m) :
    diagRank f (f i) < diagRank f (diag f) := by
  rw [diagRank_enumerated, diagRank_diag]
  omega

end PallLean.Paper93.DeepMath.PathB.PiStarDiagonal

#print axioms PallLean.Paper93.DeepMath.PathB.PiStarDiagonal.diagRank_enumerated
#print axioms PallLean.Paper93.DeepMath.PathB.PiStarDiagonal.diagRank_diag
#print axioms PallLean.Paper93.DeepMath.PathB.PiStarDiagonal.diagRank_separates
