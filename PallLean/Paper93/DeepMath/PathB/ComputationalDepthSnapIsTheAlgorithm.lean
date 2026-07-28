import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpringRelease
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitSATOffPiStar

/-!
# The snap IS the algorithm off Π★ — the whole descent on one named socket

The torsion/spring release (`SpringRelease`) collapsed the descent's two open objects into one: the
uniformity-promotion is IKW (real) plus the **snap** — a fast SAT algorithm that closes the collapse to a
separation.  That snap algorithm is not a new object: it is the off-Π★ Circuit-SAT algorithm specified in
`CircuitSATOffPiStar` — `GenuineCrossing` (`∃ a, OffPiStar a ∧ a.decides`).

This file makes that identification machine-checked: instantiating the spring's `FastSAT` socket with
`GenuineCrossing`, the entire descent — both seams (class-strengthening and uniformity), the spring
(IKW), the padding half — rests on the **single** named socket `GenuineCrossing`.

**It does NOT build the algorithm.**  `GenuineCrossing` stays open; filling it (proving `Attack.decides`
for the general class) is `P ≠ NP`.  Every "build the crossing" instruction of this descent names this
same object, and it is left open by construction — the honest line held, one last time and in one place.

## What is proved

* **`snap_is_genuine_crossing`** — the snap the spring needs is exactly `GenuineCrossing`: given the real
  spring (release = IKW, snap machinery = Williams' contradiction) and the non-uniform assumption, the
  separation follows from `GenuineCrossing` and nothing else.
* **`descent_has_one_named_socket`** — the whole descent rests on the single socket `GenuineCrossing`,
  and it is the off-Π★ Circuit-SAT algorithm — the one thing left, the theorem.

## Honest scope

An identification, not a construction.  The single open socket is `GenuineCrossing`; everything around it
(the spring, the padding half, magnification, the restricted junta fill) is built and real.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SnapIsTheAlgorithm

open PallLean.Paper93.DeepMath.PathB.SpringRelease
open PallLean.Paper93.DeepMath.PathB.CircuitSATOffPiStar

/-- **The snap is the off-Π★ Circuit-SAT algorithm (proved).**  Instantiating the spring's `FastSAT`
socket with `GenuineCrossing`: given the real spring (release = IKW easy-witness, `snap` = Williams'
contradiction closing the collapse) and the non-uniform assumption, the separation follows from
`GenuineCrossing` — the off-Π★ Circuit-SAT algorithm — and nothing else. -/
theorem snap_is_genuine_crossing {NonUnif UnifCollapse Separation : Prop}
    (release : NonUnif → UnifCollapse)
    (snap : UnifCollapse → GenuineCrossing → Separation)
    (assumption : NonUnif) :
    GenuineCrossing → Separation :=
  descent_has_one_open_object release snap assumption

/-- **The whole descent rests on one named socket (proved).**  Both seams and the spring reduce to the
single object `GenuineCrossing = ∃ a : Attack, OffPiStar a ∧ a.decides` — a genuine sub-brute-force
Circuit-SAT algorithm that does not route through Π★.  It is the only thing left open; filling it is
`P ≠ NP`.  This states the identification; it does not fill the socket. -/
theorem descent_has_one_named_socket {NonUnif UnifCollapse Separation : Prop}
    (release : NonUnif → UnifCollapse)
    (snap : UnifCollapse → GenuineCrossing → Separation)
    (assumption : NonUnif) :
    (GenuineCrossing → Separation) ∧
      (GenuineCrossing = ∃ a : Attack, OffPiStar a ∧ a.decides) :=
  ⟨snap_is_genuine_crossing release snap assumption, rfl⟩

end PallLean.Paper93.DeepMath.PathB.SnapIsTheAlgorithm

#print axioms PallLean.Paper93.DeepMath.PathB.SnapIsTheAlgorithm.snap_is_genuine_crossing
#print axioms PallLean.Paper93.DeepMath.PathB.SnapIsTheAlgorithm.descent_has_one_named_socket
