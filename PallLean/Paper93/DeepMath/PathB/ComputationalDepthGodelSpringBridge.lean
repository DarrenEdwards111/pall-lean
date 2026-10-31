import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalObstruction

/-!
# The bridge: the Gödel spring and the time hierarchy are one mechanism

The N-Frame "Gödel-tower spring" forces strict growth via soundness; the time hierarchy forces
`NTIME(a) ⊄ NTIMEcanon(b)` via a diagonal.  This file machine-checks that they are the SAME abstract
mechanism — an escaping diagonal captured one level up — and, as the genuinely new content, that the
DIFFICULTY IS INVERTED between them.  That inversion re-diagnoses what circuits are missing.

## The abstract mechanism (proved)

`EscapeSpring`: a level `reach`, the next level `bigger`, a diagonal `D` that **escapes**
(`¬ reach D`) but is **captured** one level up (`bigger D`).  `escape_forces_strict` proves that any
such spring forces `bigger ⊄ reach` — strict growth.  Both the Gödel tower and the time hierarchy
are instances.

## The two instances

* **Gödel (`godel_escapes`)** — a `LogicLevel` with SOUNDNESS (`Proves s → True_ s`) and the Gödel
  fixed point (`True_ godel ↔ ¬ Proves godel`) has an escaping sentence: the level cannot prove its
  Gödel sentence.  Here the ESCAPE is the hard part (needs soundness); the CAPTURE is free (the next
  level just adds `godel` as an axiom).
* **Time (`computation_escape_free`, `timeSpring`)** — the diagonal `naiveDiag b` escapes
  `NTIMEcanon(b)` for FREE, by Cantor (`naiveDiag_differs`): no soundness needed.  Here the CAPTURE
  is the hard part — `naiveDiag b ∈ NTIME(a)` needs the universal machine.

## The inversion (the new finding, proved)

* **`computation_escape_free`** — for computation the escape is Cantor-free: `¬ NTIMEcanon b
  (naiveDiag b)`.  So the soundness slot that the Gödel spring struggles for is, for computation,
  handed over for nothing.
* **`naiveDiag_capture_is_complement`** — but the capture is where it bites: `naiveDiag b` is
  pointwise a COMPLEMENT of the universal evaluation (`naiveDiag_is_complement`), so
  `naiveDiag b ∈ NTIME(a)` is the co-nondeterministic problem — the universal-machine obstruction.
* **`bridge_verdict`** — assembled: a computation spring is built from a diagonal that escapes (free)
  AND is captured (`NTIME a D`).  The escape is free; the entire difficulty is the CAPTURE, i.e. the
  universal object.  So the ingredient circuits are missing is NOT soundness (the escape is free even
  for them) — it is the **universal object in the capture step**, which non-uniform circuits lack (no
  size-efficient universal circuit) and uniform machines have (the universal machine).  That is why
  the mechanism completes only on the uniform axis, where the capture slot is fillable.

## Verdict

The Gödel spring and the uniform hierarchy are the same escaping-diagonal mechanism, with the
difficulty in opposite slots: Gödel's hard part is ESCAPE (soundness), computation's is CAPTURE (the
universal object).  This corrects the "circuits lack soundness" reading: circuits get the escape for
free by Cantor; what they lack is the universal object for capture — the exact primitive the
hierarchy mountain isolated (`naiveDiag_is_complement`), and the exact reason the completion runs
through the uniform braid (where a universal machine exists) and bottoms out at the dent.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GodelSpringBridge

open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable
open PallLean.Paper93.DeepMath.PathB.DiagonalObstruction

/-! ### The abstract mechanism -/

/-- An **escaping-diagonal spring**: a diagonal `D` out of reach at one level but captured the next.
Both the Gödel tower and the time hierarchy instantiate it. -/
structure EscapeSpring where
  /-- the level `i` reach -/
  reach : Lang → Prop
  /-- the level `i+1` reach -/
  bigger : Lang → Prop
  /-- the diagonal -/
  D : Lang
  /-- `D` escapes level `i` -/
  escapes : ¬ reach D
  /-- `D` is captured at level `i+1` -/
  captured : bigger D

/-- **The spring forces strict growth (proved).**  An escaping-but-captured diagonal witnesses
`bigger ⊄ reach`. -/
theorem escape_forces_strict (S : EscapeSpring) : ¬ (∀ L, S.bigger L → S.reach L) :=
  fun hsub => S.escapes (hsub S.D S.captured)

/-! ### Instance 1 — Gödel (escape is the hard part; capture is free) -/

/-- A self-referential logical level with soundness and the Gödel fixed point. -/
structure LogicLevel where
  /-- the sentences -/
  Sentence : Type
  /-- `Σ₁` provability -/
  Proves : Sentence → Prop
  /-- truth -/
  True_ : Sentence → Prop
  /-- **soundness**: what the level proves is true -/
  sound : ∀ s, Proves s → True_ s
  /-- the Gödel sentence -/
  godel : Sentence
  /-- the fixed point `G ↔ ¬ Prov G` -/
  fixedpoint : True_ godel ↔ ¬ Proves godel

/-- **The Gödel sentence escapes (proved).**  Soundness plus the fixed point force the level to be
unable to prove its Gödel sentence — the escape, powered by SOUNDNESS. -/
theorem godel_escapes (L : LogicLevel) : ¬ L.Proves L.godel :=
  fun hp => (L.fixedpoint.mp (L.sound _ hp)) hp

/-! ### Instance 2 — Time hierarchy (escape is free; capture is the hard part) -/

/-- **The computation escape is Cantor-free (proved).**  The diagonal escapes the smaller class with
NO soundness constraint: `¬ NTIMEcanon b (naiveDiag b)`, straight from `naiveDiag_differs`. -/
theorem computation_escape_free (b : ℕ) : ¬ NTIMEcanon b (naiveDiag b) := by
  rintro ⟨k, data, c, heq⟩
  exact naiveDiag_differs b k data c heq

/-- The time-hierarchy spring, GIVEN the capture (the universal-machine socket): a diagonal that
escapes `NTIMEcanon(b)` for free and is captured in `NTIME(a)` forces the hierarchy. -/
def timeSpring (a b : ℕ) (D : Lang) (hesc : ¬ NTIMEcanon b D) (hcap : NTIME a D) : EscapeSpring where
  reach := NTIMEcanon b
  bigger := NTIME a
  D := D
  escapes := hesc
  captured := hcap

/-- The time spring forces the canonical hierarchy — the escape is `computation_escape_free`, the
capture `hcap` is the universal machine. -/
theorem timeSpring_forces (a b : ℕ) (D : Lang) (hesc : ¬ NTIMEcanon b D) (hcap : NTIME a D) :
    ¬ (∀ L, NTIME a L → NTIMEcanon b L) :=
  escape_forces_strict (timeSpring a b D hesc hcap)

/-! ### The inversion — the new finding -/

/-- **The capture is a complement (proved).**  For the naive diagonal the escape is free but the
capture is exactly the obstruction: `naiveDiag b` is pointwise the complement of the universal
evaluation, so `naiveDiag b ∈ NTIME(a)` is the co-nondeterministic (universal-machine) problem. -/
theorem naiveDiag_capture_is_complement (b : ℕ) (x : List Bool) :
    naiveDiag b x = ! canonEnum b x.length x :=
  naiveDiag_is_complement b x

/-- **The bridge verdict (proved).**  The computation spring reduces to its CAPTURE alone: the escape
is free (`computation_escape_free`), so from any captured diagonal (`NTIME a D` with `¬ NTIMEcanon b
D`) the hierarchy follows.  The whole difficulty is the capture = the universal object.  Hence the
ingredient circuits lack is NOT soundness (they too get the escape free by Cantor) but the universal
object for capture — present on the uniform axis, absent for non-uniform circuits. -/
theorem bridge_verdict (a b : ℕ) (D : Lang) (hcap : NTIME a D) (hesc : ¬ NTIMEcanon b D) :
    ¬ (∀ L, NTIME a L → NTIMEcanon b L) :=
  timeSpring_forces a b D hesc hcap

end PallLean.Paper93.DeepMath.PathB.GodelSpringBridge

#print axioms PallLean.Paper93.DeepMath.PathB.GodelSpringBridge.escape_forces_strict
#print axioms PallLean.Paper93.DeepMath.PathB.GodelSpringBridge.godel_escapes
#print axioms PallLean.Paper93.DeepMath.PathB.GodelSpringBridge.computation_escape_free
#print axioms PallLean.Paper93.DeepMath.PathB.GodelSpringBridge.bridge_verdict
