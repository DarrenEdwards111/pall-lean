import PallLean.Paper93.DeepMath.PathB.ComputationalDepthR5Localization

/-!
# The collapse: R5 (beat n²) reduces to R1 (non-natural) — magnification is the unique general lever

Darren's second curiosity pass, restricted to beat-n² candidates.  Honest caveat first: "complete" combos
with `UNCOVERED: NONE` are OR-aggregation artifacts (the score maxes over techniques, so a union of an
*available* technique that reaches no superpoly with an *unavailable* one that does ticks every box without
composing) — those are ignored.  The trustworthy signal is per-technique.

**Signal 1 — the unique general lever.**  Of all beat-n² candidates, exactly one passes the generality gate
(general circuits ∧ Boolean-SAT ∧ superpoly): **hardness magnification**.  Williams reaches superpoly but on
NEXP, not superpoly-on-NP; KRW is general only up to the NC¹ ceiling; matrix rigidity reaches superpoly but
is linear-horn / wrong-side for SAT; approximate degree, lifting, shrinkage, fusion, GCT are each confined
to a restricted model (query / communication / monotone / formula / algebraic) — the corpus's wall of
restricted lower bounds.  Magnification is the one general lever (`magnification_unique_lever`).

**Signal 2 — the residual blocker collapses.**  Magnification's only gaps are that its `n^{1+ε}` input is
*not available* and *not non-natural*.  But for magnification these are the *same* gap: the magnifying
`n^{1+ε}` gap-MCSP bounds all use natural arguments (the campaign's `HardnessMagnification`, `bc9d27e2`, and
the CHOPRS locality barrier), so the input becomes available exactly when it is made non-natural.  Hence a
general crossing exists **iff** magnification's input is non-natural (`general_crossing_iff_r1`):
```
   beat-n²-toward-superpoly-on-general-SAT  ⟺  magnification's n^{1+ε} input is non-natural  =  past R1.
```
The first pass localized the wall to R5 (beat n²); the second collapses R5's only general resolution into R1
(natural proofs).  One lever, one gate.

## What is proved

* **`magnification_passes`** — hardness magnification passes the generality gate.
* **`magnification_unique_lever`** — it is the *only* beat-n² candidate that passes: every other is
  NEXP-only, NC¹-ceilinged, wrong-side, or restricted.
* **`general_crossing_iff_r1`** — given the campaign fact that magnification's input is available iff
  non-natural, a general crossing exists iff that input is non-natural: R5 collapses to R1.

## Honest verdict — the same stone, wearing its exact mechanism

The engine invented no technique — it searched the encoded map.  What it did faithfully is converge on the
frontier's real structure: one general lever (magnification), one gate (natural proofs), every other route
provably confined to a restricted model.  That is `cost_super` once more, but now with the sharpest
mechanism of the session: the crossing is not "prove SAT hard", not even "beat n²", but specifically *attain
magnification's overhead-free `n^{1+ε}` weak bound in a non-natural way* — one inch past the natural-proofs
barrier.  This is exactly the `DischargePiStar` target (a separating measure high on SAT, non-natural) the
campaign already named — the loop closes, one notch tighter.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MagnificationLever

/-- The beat-n² candidate techniques the second pass ranked. -/
inductive Tech
  | magnification | williams | krw | rigidity | approxDegree | lifting | shrinkage | fusion | gct
  deriving DecidableEq

/-- Reaches *general* circuits (`P/poly`), not a restricted model. -/
def general : Tech → Prop
  | .magnification => True
  | .williams      => True
  | .rigidity      => True
  | _              => False

/-- Applies to the Boolean-SAT side (not linear-horn / wrong-side). -/
def satSide : Tech → Prop
  | .rigidity => False
  | _         => True

/-- Reaches superpoly (not NEXP-only, not an `n²`/`log n` cap). -/
def superpolyReach : Tech → Prop
  | .magnification => True
  | .krw           => True
  | .rigidity      => True
  | _              => False

/-- The generality gate: general ∧ Boolean-SAT ∧ superpoly. -/
def PassesGate (t : Tech) : Prop := general t ∧ satSide t ∧ superpolyReach t

/-! ### Magnification is the unique general lever -/

/-- **Hardness magnification passes the gate (proved).** -/
theorem magnification_passes : PassesGate .magnification := by
  simp [PassesGate, general, satSide, superpolyReach]

/-- **Magnification is the unique general lever (proved).**  Every other beat-n² candidate fails the gate:
Williams is NEXP-only (no `superpolyReach` in the NP sense), KRW is NC¹-ceilinged (no `general`), rigidity is
wrong-side (`¬ satSide`), and approximate-degree/lifting/shrinkage/fusion/GCT are restricted (`¬ general`). -/
theorem magnification_unique_lever : ∀ t : Tech, PassesGate t → t = .magnification := by
  intro t h
  cases t <;> simp_all [PassesGate, general, satSide, superpolyReach]

/-! ### The collapse: general crossing ⟺ R1 (non-natural) -/

/-- A general crossing: some technique passes the gate *and* its input is available. -/
def GeneralCrossing (Available : Tech → Prop) : Prop := ∃ t, PassesGate t ∧ Available t

/-- **R5 collapses to R1 (proved).**  Given the campaign fact that magnification's `n^{1+ε}` input is
available iff non-natural (`HardnessMagnification` / CHOPRS locality barrier), a general crossing exists iff
that input is non-natural.  The unique lever routes the whole beat-n² problem through the natural-proofs
barrier. -/
theorem general_crossing_iff_r1 (Available NonNatural : Tech → Prop)
    (magnif_fact : Available .magnification ↔ NonNatural .magnification) :
    GeneralCrossing Available ↔ NonNatural .magnification := by
  constructor
  · rintro ⟨t, hgate, havail⟩
    have ht : t = .magnification := magnification_unique_lever t hgate
    subst ht
    exact magnif_fact.mp havail
  · intro hnn
    exact ⟨.magnification, magnification_passes, magnif_fact.mpr hnn⟩

end PallLean.Paper93.DeepMath.PathB.MagnificationLever

#print axioms PallLean.Paper93.DeepMath.PathB.MagnificationLever.magnification_passes
#print axioms PallLean.Paper93.DeepMath.PathB.MagnificationLever.magnification_unique_lever
#print axioms PallLean.Paper93.DeepMath.PathB.MagnificationLever.general_crossing_iff_r1
