import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodMoveFace

/-!
# Discharging `Π★` = a separating rank measure = the lower bound

You were right that `Π★` need not be hypercomputational.  This file pins what it *is*: discharging the
God-Move reduces to exhibiting a **separating rank measure** — a rank function low on every
P-compilation and high on SAT — and such a measure exists **iff** SAT ∉ P.  So `Π★` is a standard-model
object whose existence equals the separation, not a fuel poured in from outside.

* **`SeparatingMeasure`** — the two observer readings as one object: `rank` with `rank ≤ low` on every
  P-compilation (inside) and `high ≤ rank sat` (outside), with `low < high`.
* **`separating_iff_not_PComp` (proved)** — **the equivalence**: a separating measure exists iff SAT is
  not a P-compilation (`¬ PComp sat`, i.e. SAT ∉ P).
  - *Forward* — the two readings clash on `sat` if SAT ∈ P: `high ≤ rank sat ≤ low < high`.
  - *Backward* — if SAT ∉ P, the indicator rank `[o is a P-compilation ? 0 : 1]` separates.  It is a
    perfectly standard-model function — but its construction **decides P-membership** (`Classical.dec`),
    so it is **non-natural** (not efficiently computable) — and *not* hypercomputational.
* **`shared_floor_not_separating` (proved no-go)** — the repo's audit finding, abstractly: if the
  measure gives SAT the *same* rank as a P-compilation (the identity-minor floor SPDP rank hits), no
  gap exists, so it cannot separate.  This is exactly why the obvious (SPDP / flat-projection) `Π★`
  fails.

**Honest scope.**  This *characterizes* the discharge, it does not perform it: constructing a
separating measure is equivalent to the circuit lower bound itself.  `Π★` is standard-model and
non-natural — you were right to drop "hypercomputational" — and it is the far shore precisely because a
separating measure *is* `SAT ∉ P`, the obvious candidate provably shares the floor, and any *efficient*
separating measure would be a natural proof.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DischargePiStar

/-- A **separating rank measure**: a rank function that is `≤ low` on every P-compilation (the inside
observer) and `≥ high` on SAT (the outside observer), with a genuine gap `low < high`.  This bundle is
the *content* of a working `Π★`. -/
structure SeparatingMeasure (Obj : Type) (PComp : Obj → Prop) (sat : Obj) where
  /-- the rank measure. -/
  rank : Obj → ℕ
  /-- the low reading (inside the P bubble). -/
  low : ℕ
  /-- the high reading (outside, on SAT). -/
  high : ℕ
  /-- a genuine gap. -/
  gap : low < high
  /-- inside observer: every P-compilation is low-rank. -/
  low_on_P : ∀ o, PComp o → rank o ≤ low
  /-- outside observer: SAT is high-rank. -/
  high_on_sat : high ≤ rank sat

/-- **Discharging `Π★` = a separating measure = the lower bound (proved).**  A separating rank measure
exists iff SAT is not a P-compilation (SAT ∉ P).  So `Π★` is a standard-model object whose existence is
exactly the separation. -/
theorem separating_iff_not_PComp {Obj : Type} (PComp : Obj → Prop) (sat : Obj) :
    Nonempty (SeparatingMeasure Obj PComp sat) ↔ ¬ PComp sat := by
  constructor
  · rintro ⟨S⟩ hsat
    have h1 : S.rank sat ≤ S.low := S.low_on_P sat hsat
    have h2 : S.high ≤ S.rank sat := S.high_on_sat
    have h3 := S.gap
    omega
  · intro hsat
    classical
    exact ⟨{
      rank := fun o => if PComp o then 0 else 1
      low := 0
      high := 1
      gap := by omega
      low_on_P := fun o ho => by simp [ho]
      high_on_sat := by simp [hsat] }⟩

/-- **Why the obvious `Π★` fails — the shared-floor no-go (proved).**  If the measure assigns SAT the
*same* rank as some P-compilation `c` (the identity-minor floor that raw SPDP rank hits — the repo's
audited obstruction), then there is no gap and no separation: no `low < high` can sandwich a shared
value. -/
theorem shared_floor_not_separating {Obj : Type} (rank : Obj → ℕ) (c sat : Obj)
    (hfloor : rank c = rank sat) :
    ¬ ∃ low high : ℕ, low < high ∧ rank c ≤ low ∧ high ≤ rank sat := by
  rintro ⟨low, high, hgap, hlo, hhi⟩
  rw [hfloor] at hlo
  omega

end PallLean.Paper93.DeepMath.PathB.DischargePiStar

#print axioms PallLean.Paper93.DeepMath.PathB.DischargePiStar.separating_iff_not_PComp
#print axioms PallLean.Paper93.DeepMath.PathB.DischargePiStar.shared_floor_not_separating
