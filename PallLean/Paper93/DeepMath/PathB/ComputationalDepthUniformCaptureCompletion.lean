import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHierarchyCanonical
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDiagonalObstruction

/-!
# Completing the capture step through the uniform braid

The `GodelSpringBridge` audit showed the uniform route's difficulty is the **capture**: the Cantor
diagonal `naiveDiag b` escapes `NTIMEcanon(b)` for free (`naiveDiag_differs`), and the one open input
is landing it in `NTIME(a)` — the universal machine.  This file completes the capture as far as it
honestly goes: it discharges the escape and reduces the entire hierarchy ingredient of the uniform
braid to the **universal-machine primitives**, leaving the engine ready to fire.

## What is proved

* **`capture_gives_diagonal`** — the escape is discharged: given the capture `NTIME a (naiveDiag b)`,
  the diagonal socket `DiagonalAgainstCanon a b` follows immediately, using the proved
  `naiveDiag_differs`.  So `DiagonalAgainstCanon` rests on the capture *alone*.
* **`capture_gives_canonical_hierarchy`** — capture ⟹ `NTIME(a) ⊄ NTIMEcanon(b)` (one rung), via
  `hierarchyCanon_from_diagonal`.
* **`full_canonical_hierarchy_of_capture`** — the universal-capture primitive
  (`UniversalCapture`: the diagonal is captured at every level) ⟹ the whole canonical hierarchy.
* **`engine_hierarchy_of_capture_and_coverage`** — to reach the braid engine's ingredient
  (`NTIME(a) ⊄ NTIME(b)`, over the *class* not just the canonical enumeration) one additionally needs
  **coverage** (`NTIME(b) ⊆ NTIMEcanon(b)` — canonical normalization).  Given capture *and* coverage,
  the engine's hierarchy ingredient holds.

## Honest scope — the two universal-machine sockets, and the dent

The escape is fully discharged (Cantor).  The hierarchy ingredient of the uniform braid now rests on
exactly two universal-machine primitives — **capture** (simulate a canonical machine within the larger
clock, lazy diagonalisation) and **coverage** (every `NTIME(b)` machine has a canonical-clock form).
Both are the irreducible universal machine that `DiagonalObstruction` flagged (thousands of lines of
`ComposableMachine` construction); they are formalisation labor, not a conceptual gap, and they are
exactly what the *uniform* axis has and non-uniform circuits lack.  With them, `lipton_viglas_engine`
gives the SAT time–space bound up to `√2`, and the braid magnifies toward — but does not cross — the
**dent** (the `n^{1+ε}` sparse bound behind the locality barrier).  So this completes the capture up to
the universal machine and hands the completed hierarchy to the engine; it does not cross the wall.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniformCaptureCompletion

open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable
open PallLean.Paper93.DeepMath.PathB.DiagonalObstruction
open PallLean.Paper93.DeepMath.PathB.HierarchyCanonical

/-- **The escape is discharged; the diagonal socket rests on the capture alone (proved).**  Given the
capture `NTIME a (naiveDiag b)`, the diagonal socket follows from the proved Cantor escape
`naiveDiag_differs`. -/
theorem capture_gives_diagonal (a b : ℕ) (hcap : NTIME a (naiveDiag b)) :
    DiagonalAgainstCanon a b :=
  ⟨naiveDiag b, hcap, naiveDiag_differs b⟩

/-- **Capture ⟹ the canonical hierarchy, one rung (proved).** -/
theorem capture_gives_canonical_hierarchy (a b : ℕ) (hcap : NTIME a (naiveDiag b)) :
    ¬ (∀ L, NTIME a L → NTIMEcanon b L) :=
  hierarchyCanon_from_diagonal a b (capture_gives_diagonal a b hcap)

/-- **The universal-capture primitive**: the universal machine captures the diagonal at every level. -/
def UniversalCapture : Prop :=
  ∀ a b : ℕ, 1 ≤ b → b < a → NTIME a (naiveDiag b)

/-- **The whole canonical hierarchy from the universal-capture primitive (proved).**  Escape free,
capture supplied at every level ⟹ `NTIME(a) ⊄ NTIMEcanon(b)` for all `b < a`. -/
theorem full_canonical_hierarchy_of_capture (h : UniversalCapture) :
    ∀ a b : ℕ, 1 ≤ b → b < a → ¬ (∀ L, NTIME a L → NTIMEcanon b L) :=
  concreteHierarchyCanon (fun a b hb hba => capture_gives_diagonal a b (h a b hb hba))

/-- **Coverage**: every `NTIME(b)` language has a canonical-clock form.  The second universal-machine
socket (normalisation), needed to pass from the canonical hierarchy to the class hierarchy. -/
def Coverage (b : ℕ) : Prop := ∀ L, NTIME b L → NTIMEcanon b L

/-- **The engine's hierarchy ingredient, from capture + coverage (proved).**  With the diagonal
captured and the class normalised to canonical form, `NTIME(a) ⊄ NTIME(b)` — exactly the hierarchy
ingredient `lipton_viglas_engine` consumes. -/
theorem engine_hierarchy_of_capture_and_coverage (a b : ℕ)
    (hcap : NTIME a (naiveDiag b)) (hcov : Coverage b) :
    ¬ (∀ L, NTIME a L → NTIME b L) := by
  intro hsub
  exact capture_gives_canonical_hierarchy a b hcap (fun L hL => hcov L (hsub L hL))

end PallLean.Paper93.DeepMath.PathB.UniformCaptureCompletion

#print axioms PallLean.Paper93.DeepMath.PathB.UniformCaptureCompletion.capture_gives_diagonal
#print axioms PallLean.Paper93.DeepMath.PathB.UniformCaptureCompletion.capture_gives_canonical_hierarchy
#print axioms PallLean.Paper93.DeepMath.PathB.UniformCaptureCompletion.full_canonical_hierarchy_of_capture
#print axioms PallLean.Paper93.DeepMath.PathB.UniformCaptureCompletion.engine_hierarchy_of_capture_and_coverage
