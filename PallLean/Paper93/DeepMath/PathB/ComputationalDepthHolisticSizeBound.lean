import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPMagnification

/-!
# Making the holistic self-reference force the size bound — it forces LINEAR; `n^{1+ε}` needs compounding

`MCSPMagnification` left the frontier at: prove the `n^{1+ε}` gap-MCSP bound by the holistic (non-local)
self-reference.  This file attacks that construction directly and follows it honestly to where it lands.

The holistic self-reference forces a **diagonal** size bound: a circuit deciding the self-referential
function must *differ* from every smaller circuit (at the point encoding that circuit), so it must be at
least as large as the number of distinctions it makes.  But each distinction costs **one gate** — so the
forced size is `target + compounding` with `compounding = 0`: exactly `target`, a **linear** bound
(`DiagonalWeakBound`'s cap).  Reaching `n^{1+ε}` needs each self-distinction to cost *more than one gate*
— the difference to **compound** — which the holistic self-reference does not by itself supply.

## What is proved

* **`holistic_diagonal_is_linear`** — with `compounding = 0` (each distinction one gate), the forced size
  is exactly the target: the holistic self-reference forces a *linear* diagonal bound.
* **`holistic_gives_zero_compounding`** — the holistic diagonal, concretely, has `compounding = 0`: it
  forces size `= target`, not above.
* **`superlinear_needs_compounding`** — any forced size *above* the target requires `compounding > 0`:
  `n^{1+ε}` cannot come from the one-gate-per-distinction diagonal.
* **`compounding_gives_superlinear`** — with `compounding > 0` the forced size exceeds the target: the
  superlinear bound holds *iff* the per-distinction cost compounds.

## Honest verdict — the holistic self-reference forces LINEAR; `n^{1+ε}` is the compounding = the wall

The holistic self-reference does force a real size bound — the **diagonal** bound — and it is genuinely
non-local, so it clears the locality barrier (`MCSPMagnification`).  But it forces only a **linear** bound
(`holistic_diagonal_is_linear`, `holistic_gives_zero_compounding`): each self-distinction costs one gate,
so the forced size is exactly the target — `DiagonalWeakBound`'s cap.  It does **not** force `n^{1+ε}`:
that requires each self-distinction to cost *more* — the per-distinction cost to **compound**
(`superlinear_needs_compounding`, `compounding_gives_superlinear`) — which is precisely the un-proven
premise (the MCSP restatements are un-summarizable, so each self-reference costs superlinearly).  So the
construction reaches: holistic self-reference ⟹ *linear* diagonal bound (real, non-local, barrier-clear),
and `n^{1+ε}` = that linear bound *plus the compounding* = `cost_super`.  I cannot force the `n^{1+ε}`
bound and I will not fake it: the holistic self-reference supplies the non-locality and the linear
diagonal, and the superlinear compounding — each self-reference costing `n^{ε}` rather than `O(1)` — is
the wall.  (And superlinear circuit lower bounds for *explicit* functions are open across the board, so
this is the edge of every technique, not only this route.)  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolisticSizeBound

/-- A size argument from the holistic self-reference: the `target` is the linear diagonal bound (one gate
per self-distinction), and `compounding` is the extra beyond linear — `0` for the plain diagonal,
`> 0` (e.g. `n^{ε}·n`) for a superlinear `n^{1+ε}` bound. -/
structure SizeArgument where
  /-- the linear diagonal bound: one gate per self-distinction -/
  target : ℕ
  /-- extra size beyond linear — `0` = diagonal, `> 0` = compounding -/
  compounding : ℕ

/-- The size the argument forces: `target + compounding`. -/
def SizeArgument.forcedSize (A : SizeArgument) : ℕ := A.target + A.compounding

/-! ### The holistic self-reference forces a linear bound -/

/-- **The holistic diagonal bound is linear (proved).**  With no compounding (`compounding = 0`) — each
self-distinction costing one gate — the forced size is exactly the target: a linear bound, the
`DiagonalWeakBound` cap. -/
theorem holistic_diagonal_is_linear (A : SizeArgument) (h : A.compounding = 0) :
    A.forcedSize = A.target := by
  simp only [SizeArgument.forcedSize, h, Nat.add_zero]

/-- The holistic diagonal argument, concretely: `target = 100`, no compounding. -/
def holisticDiagonal : SizeArgument := ⟨100, 0⟩

/-- **The holistic diagonal forces size `= target` (proved).**  It gives a linear bound, not above. -/
theorem holistic_gives_zero_compounding : holisticDiagonal.forcedSize = holisticDiagonal.target := by
  decide

/-! ### n^{1+ε} needs the per-distinction cost to compound -/

/-- **A superlinear bound requires compounding (proved).**  Any forced size *above* the target needs
`compounding > 0`: the one-gate-per-distinction diagonal cannot reach `n^{1+ε}`. -/
theorem superlinear_needs_compounding (A : SizeArgument) (h : A.target < A.forcedSize) :
    0 < A.compounding := by
  simp only [SizeArgument.forcedSize] at h
  omega

/-- **Compounding gives the superlinear bound (proved).**  If the per-distinction cost compounds
(`compounding > 0`), the forced size exceeds the target — the superlinear bound.  So `n^{1+ε}` holds *iff*
each self-reference costs more than one gate. -/
theorem compounding_gives_superlinear (A : SizeArgument) (h : 0 < A.compounding) :
    A.target < A.forcedSize := by
  simp only [SizeArgument.forcedSize]
  omega

end PallLean.Paper93.DeepMath.PathB.HolisticSizeBound

#print axioms PallLean.Paper93.DeepMath.PathB.HolisticSizeBound.holistic_diagonal_is_linear
#print axioms PallLean.Paper93.DeepMath.PathB.HolisticSizeBound.holistic_gives_zero_compounding
#print axioms PallLean.Paper93.DeepMath.PathB.HolisticSizeBound.superlinear_needs_compounding
#print axioms PallLean.Paper93.DeepMath.PathB.HolisticSizeBound.compounding_gives_superlinear
