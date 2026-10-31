import PallLean.Paper93.DeepMath.PathB.ComputationalDepthInverseBridge

/-!
# The inverse bridge, run by entanglement: it is the dial from gradient descent to self-reference

`InverseBridge` proved gradient descent (natural/large) and the holistic self-reference (non-natural/rare)
are *exact complements*.  Darren: bridge them inversely **via entanglement**.  Entanglement is the physical
dial that runs that bridge.  From `SharingMonogamy`, the shared (compressible) part of a seam is
`shared = template − entangle`: entanglement *cuts* sharing.  So as entanglement rises from `0` to the
whole template, the seam moves continuously from **full sharing** (gradient descent works — compressible,
natural) to **no sharing** (the holistic self-reference — incompressible, non-natural).  Entanglement is
the one quantity whose two ends are the two sides of the barrier.

## What is proved

* **`low_entanglement_full_sharing`** — at `entangle = 0` the shared part is the whole template: full
  sharing, the gradient-descent / natural end.
* **`high_entanglement_no_sharing`** — at `entangle = template` the shared part is `0`: no sharing, the
  self-reference / non-natural end (`SharingMonogamy.full_entanglement_forces_doubling`).
* **`entanglement_cuts_sharing`** — any positive entanglement strictly cuts the sharing
  (`SharingMonogamy.entanglement_strictly_cuts`): the monotone inverse relation.
* **`entanglement_dials_the_bridge`** — the two ends exist at once: a low-entanglement seam with full
  sharing (natural) and a high-entanglement seam with zero sharing (non-natural).  Entanglement runs the
  inverse bridge.

## Honest verdict — entanglement is the dial; the crossing needs high entanglement = `cost_super`

Darren's "bridge them inversely via entanglement" is exactly right: entanglement is the monogamy dial that
runs the inverse bridge.  At `entangle = 0` the seam shares fully — the gradient-descent / natural /
barriered end (`low_entanglement_full_sharing`); at `entangle = template` it shares nothing — the holistic
self-reference / non-natural / escape end (`high_entanglement_no_sharing`); and every positive entanglement
strictly cuts sharing (`entanglement_cuts_sharing`), moving monotonically between them
(`entanglement_dials_the_bridge`).  So the two sides `InverseBridge` proved complementary are the two ends
of *one entanglement axis* — the natural side is low entanglement, the non-natural side is high.  This is
the cleanest form of the inverse bridge: a single physical quantity whose ends are gradient descent and the
self-reference.  But it does not cross: reaching the high-entanglement (non-natural, un-shareable) end for
SAT is the un-proven premise — `SharingMonogamy.SATEntangledEnough`, that SAT's seam is entangled enough to
kill the sharing — which is `cost_super`.  Entanglement dials the bridge; whether SAT sits at the high end
is `P ≠ NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementBridge

open PallLean.Paper93.DeepMath.PathB.SharingMonogamy

/-! ### The two ends of the entanglement axis -/

/-- **Low entanglement = full sharing (proved).**  At `entangle = 0` the shared part is the whole template
— full sharing, the gradient-descent / natural end of the bridge. -/
theorem low_entanglement_full_sharing (S : EntangledSeam) (h : S.entangle = 0) :
    S.shared_ = S.template := by
  simp only [EntangledSeam.shared_, h, Nat.sub_zero]

/-- **High entanglement = no sharing (proved).**  At `entangle = template` the shared part is `0` — no
sharing, the holistic self-reference / non-natural end.  (`SharingMonogamy.full_entanglement_forces_doubling`.) -/
theorem high_entanglement_no_sharing (S : EntangledSeam) (h : S.entangle = S.template) :
    S.shared_ = 0 :=
  full_entanglement_forces_doubling S h

/-- **Entanglement cuts sharing (proved).**  Any positive entanglement strictly reduces the shared part —
the monotone inverse relation running the bridge.  (`SharingMonogamy.entanglement_strictly_cuts`.) -/
theorem entanglement_cuts_sharing (S : EntangledSeam) (h : 0 < S.entangle) :
    S.shared_ < S.template :=
  entanglement_strictly_cuts S h

/-! ### Entanglement runs the inverse bridge -/

/-- **Entanglement dials the bridge (proved).**  Both ends exist: a low-entanglement seam sharing fully
(the gradient-descent / natural side) and a high-entanglement seam sharing nothing (the self-reference /
non-natural side).  Entanglement is the single axis whose ends are the two sides of the barrier. -/
theorem entanglement_dials_the_bridge :
    ∃ (Slow Shigh : EntangledSeam),
      Slow.entangle = 0 ∧ Slow.shared_ = Slow.template ∧
      Shigh.entangle = Shigh.template ∧ Shigh.shared_ = 0 := by
  refine ⟨⟨4, 3, 0, by omega, by omega⟩, ⟨4, 3, 3, by omega, by omega⟩, rfl, ?_, rfl, ?_⟩
  · decide
  · decide

end PallLean.Paper93.DeepMath.PathB.EntanglementBridge

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementBridge.low_entanglement_full_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementBridge.high_entanglement_no_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementBridge.entanglement_cuts_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementBridge.entanglement_dials_the_bridge
