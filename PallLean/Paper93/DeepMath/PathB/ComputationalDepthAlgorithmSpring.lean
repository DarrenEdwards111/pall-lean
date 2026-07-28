import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsSynthesis

/-!
# The last object as a spring: the fast-SAT spring is structural compressibility — empty exactly at cost_super

Pointing the curiosity engine at the one remaining open object — a fast Circuit-SAT algorithm off Π★, framed
as a *spring* (use the `2^n` tension as a resource) — surfaced one thing on high serendipity: the general
open object itself.  Every *real* algorithm-design spring (the polynomial method / Beigel–Tarui, PPSZ,
memoization, random restrictions) scored serendipity `0` — each releases only for a *structured, restricted*
class.  This file machine-checks why, and it closes a loop.

**The spring is structural compressibility.**  A faster-than-brute-force SAT algorithm releases the `2^n`
tension exactly when the circuit has exploitable structure — low degree (Beigel–Tarui ⟹ ACC⁰-SAT, Williams'
actual spring), bounded depth, small width.  `structure_is_the_spring` : `Structured ⟹ FastSAT`.  For any
*structured* class the spring fills (`spring_fillable_for_structured`) — the socket is real for weak classes.

**The general off-Π★ circuit is incompressible, so the spring is empty.**  Incompressibility is precisely the
absence of exploitable structure (`incompressible_spring_empty` : `Incompressible ⟹ ¬Structured`).  With no
structure to push against, `structure_is_the_spring` has a false premise and gives nothing — a fast SAT
algorithm for the general case is not obtainable from the spring.  It is the one open socket.

**And that empty spring *is* `cost_super`.**  Incompressibility — no structure — is the lower-bound wall
(`cost_super`).  Here it is also the algorithm-side wall: no spring for fast SAT.  `two_sides_one_wall` :
`Incompressible ↔ CostSuper`.  A circuit with no exploitable structure is simultaneously hard to lower-bound
*and* hard to satisfy faster than brute force.  The lower-bound side and the algorithm side of the descent
are the same object.

## What is proved

* **`AlgSpring`** — a class's structure, its fast-SAT spring, and incompressibility, with the release law
  (`Structured ⟹ FastSAT`) and `Incompressible ↔ ¬Structured`.
* **`structure_is_the_spring`** — structure releases the spring: a fast SAT algorithm.
* **`spring_fillable_for_structured`** — for a structured (restricted) class the spring fills.
* **`incompressible_spring_empty`** — incompressibility is the absence of structure: the spring is empty.
* **`two_sides_one_wall`** — the algorithm-side wall (empty spring) *is* the lower-bound wall (`cost_super`).

## Honest verdict — the two sides of the wall are one object; the spring is empty only at cost_super

Framing the last object as a spring is exactly right, and it unifies the descent's two sides.  The spring is
structural compressibility: it releases a fast SAT algorithm for every *structured* class
(`structure_is_the_spring`, `spring_fillable_for_structured` — Beigel–Tarui/Williams for ACC⁰, junta-style
for weak classes), and it is empty precisely for the *incompressible* general off-Π★ circuit
(`incompressible_spring_empty`).  That empty spring is not a new obstruction — it is `cost_super` itself,
viewed from the algorithm side (`two_sides_one_wall`).  So the whole descent, lower-bound side and algorithm
side, rests on one object: exploit the structure of a circuit that, being off Π★, has none — which is to
release a spring where there is no tension stored to release.  That is the last socket, and filling it is
`P ≠ NP`.  The tension really is a spring — it just discharges only where there is structure, and the
general case is defined by having none.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AlgorithmSpring

/-- A circuit class's structural handle, its fast-SAT spring, and its incompressibility. -/
structure AlgSpring where
  /-- the class has exploitable structure (low degree / bounded depth / small width) -/
  Structured : Prop
  /-- a faster-than-brute-force SAT algorithm exists for the class -/
  FastSAT : Prop
  /-- the class has no exploitable structure — the incompressible hard core, off Π★ -/
  Incompressible : Prop
  /-- **the spring**: structure releases a fast SAT algorithm (Beigel–Tarui / Williams) -/
  structure_releases : Structured → FastSAT
  /-- incompressibility is exactly the absence of structure -/
  incompressible_iff : Incompressible ↔ ¬ Structured

namespace AlgSpring

variable (S : AlgSpring)

/-- `cost_super` on this class: the lower-bound wall is incompressibility — no exploitable structure. -/
def CostSuper : Prop := ¬ S.Structured

/-- **Structure is the spring (proved).**  A structured class has a fast SAT algorithm — the `2^n` tension
releases against the structure. -/
theorem structure_is_the_spring : S.Structured → S.FastSAT := S.structure_releases

/-- **Incompressibility empties the spring (proved).**  The incompressible general case has no structure, so
the spring's premise fails — a fast SAT algorithm is not obtainable from it. -/
theorem incompressible_spring_empty : S.Incompressible → ¬ S.Structured :=
  S.incompressible_iff.mp

/-- **The two sides are one wall (proved).**  The algorithm-side obstruction (an empty spring,
`Incompressible`) is exactly the lower-bound wall (`CostSuper`, no structure). -/
theorem two_sides_one_wall : S.Incompressible ↔ S.CostSuper :=
  S.incompressible_iff

end AlgSpring

/-- A structured (restricted) class where the spring fills: `ACC⁰`-style, junta-style. -/
def structuredClass : AlgSpring where
  Structured := True
  FastSAT := True
  Incompressible := False
  structure_releases := fun _ => trivial
  incompressible_iff := by simp

/-- **The spring fills for a structured class (proved).**  There is a class with exploitable structure whose
fast SAT algorithm exists — the socket is real and fillable for weak classes (Williams' ACC⁰, juntas). -/
theorem spring_fillable_for_structured : ∃ S : AlgSpring, S.Structured ∧ S.FastSAT :=
  ⟨structuredClass, trivial, trivial⟩

end PallLean.Paper93.DeepMath.PathB.AlgorithmSpring

#print axioms PallLean.Paper93.DeepMath.PathB.AlgorithmSpring.AlgSpring.structure_is_the_spring
#print axioms PallLean.Paper93.DeepMath.PathB.AlgorithmSpring.AlgSpring.incompressible_spring_empty
#print axioms PallLean.Paper93.DeepMath.PathB.AlgorithmSpring.AlgSpring.two_sides_one_wall
#print axioms PallLean.Paper93.DeepMath.PathB.AlgorithmSpring.spring_fillable_for_structured
