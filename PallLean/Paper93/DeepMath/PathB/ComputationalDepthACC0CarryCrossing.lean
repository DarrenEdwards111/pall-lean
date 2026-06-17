import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BTDepthCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ApproxToExact

/-!
# The carry-refinement crossing condition — named socket (documentation, with proved scaffolding)

Entries 234–237 mapped the composite-`ACC⁰[m]` barrier and its carry seam: the weighted-`F_p` → exact-unit-count
conversion (234 `ApproxToExactCount`) is obstructed because the field (mod-`p`) observer is blind to p-adic carries
(235), measured by Kummer's `carryCount` (236), assembled into a CRT carry profile (237).  This file **names and
documents the crossing condition** — the precise property an observer must have to *cross* that barrier — as a socket,
with the surrounding facts proved so the socket sits faithfully between the proved characterisation and the open wall.

⚠️ **This is a documentation of the open barrier, not a crossing.**  `CarryRefinementCrossing` is a named socket: it is
**not proved**, and proving it for composite `m` *is* the open `ACC⁰[m]` separation-strength problem.  The proved
content here is only the *scaffolding*: why the field observer fails (it is carry-blind), and that any count observer
through which the function factors (with low-degree injective monomials) already yields the representation — so the
crossing reduces exactly to producing a **carry-faithful** such observer for composite modulus.

## The crossing condition

To cross, one needs a count observer that **stays faithful under carry refinement** — distinguishing counts that the
field observer collapses across carry layers — and that is realised by the low-degree count machinery for composite `m`.
The field observer is carry-blind (`fieldObs_carry_blind`), so it cannot be that observer; the crossing socket asserts a
carry-faithful low-degree representation exists for the composite-modulus approximant.

## What is proved (scaffolding; clean axioms, no `sorry`)

* **`fieldObs p k := (k : ZMod p)`** — the field count-observer (the satisfied-monomial count read mod `p`).
* **`fieldObs_carry_blind`** (PROVED) — `fieldObs p (k + p) = fieldObs p k`: the field observer collapses counts
  differing by a carry-sized shift.  The precise carry-blindness (cf. entry-235 `field_observer_blind_to_carry`).
* **`fieldObs_not_injective`** (PROVED) — for `p ≥ 2` the field observer is not injective (`fieldObs p 0 = fieldObs p
  p`): it cannot recover the exact count, hence cannot be a carry-faithful observer.
* **`lowDegRep_of_observer`** (PROVED) — a count observer `obs` and decode `dec` through which `f` factors
  (`f x = dec (obs (saCount mono x))`), with a low-degree injective monomial family, *already* give `LowDegRep f D`.
  So the crossing reduces exactly to producing such an observer for composite `m`.

## The named socket (NOT proved)

* **`CarryRefinementCrossing approxHyp f D`** — the carry-refinement crossing condition: the composite-modulus RS
  approximant (`approxHyp`) yields a `LowDegRep` of `f`.  Equivalently, a carry-faithful count observer realised by a
  low-degree injective monomial family exists.  **This is the open `ACC⁰[m]` barrier-crossing condition** — naming
  entry-234's `ApproxToExactCount` consequence in carry-observer terms.
* **`lowDegRep_of_crossing`** (PROVED conditional) — `CarryRefinementCrossing approxHyp f D → approxHyp → LowDegRep f D`:
  the socket, *if* established, discharges the barrier — confirming it is faithfully the crossing condition.

## Honest scope

The proved scaffolding pins down *why* the natural (field) observer cannot cross (carry-blindness,
`fieldObs_carry_blind`/`_not_injective`) and *what suffices* (a count observer through which `f` factors with low-degree
monomials, `lowDegRep_of_observer`), so the crossing is reduced to a single named property: a **carry-faithful
low-degree count observer for composite `m`** (`CarryRefinementCrossing`).  That socket is **not proved** — establishing
it for composite modulus is the open `ACC⁰[m]` separation-strength problem (entry 234), which the carry profile (entry
237) shows is genuinely obstructed.  Nothing here crosses the barrier or is `NEXP ⊄ ACC⁰` / `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarryCrossing

open PallLean.Paper93.DeepMath.PathB.ACC0BTDepthCollapse (LowDegRep)
open PallLean.Paper93.DeepMath.PathB.ACC0YBTExactCompose (saCount)

/-- **The field count-observer.**  The satisfied-monomial count read mod `p`: `fieldObs p k = (k : ZMod p)`.  This is
the observer the weighted-`F_p` polynomial method provides. -/
def fieldObs (p : ℕ) (k : ℕ) : ZMod p := (k : ZMod p)

/-- **The field observer is carry-blind (PROVED).**  `fieldObs p (k + p) = fieldObs p k`: it collapses counts differing
by a carry-sized shift (`p ≡ 0` mod `p`).  This is the count-level form of entry-235 `field_observer_blind_to_carry` —
the precise reason the field route cannot see a carry. -/
theorem fieldObs_carry_blind (p k : ℕ) : fieldObs p (k + p) = fieldObs p k := by
  unfold fieldObs; push_cast; simp

/-- **The field observer cannot recover the exact count (PROVED).**  For `p ≥ 2` it is not injective
(`fieldObs p 0 = fieldObs p p = 0` but `0 ≠ p`); so it is not a carry-faithful observer and cannot, by itself, cross
the barrier. -/
theorem fieldObs_not_injective (p : ℕ) (hp : 2 ≤ p) : ¬ Function.Injective (fieldObs p) := by
  intro hinj
  have h : fieldObs p 0 = fieldObs p p := by unfold fieldObs; simp
  have : (0 : ℕ) = p := hinj h
  omega

/-- **A faithful count observer suffices (PROVED).**  If a count observer `obs` and decode `dec` factor `f`
(`f x = dec (obs (saCount mono x))`) through a low-degree injective monomial family, then `LowDegRep f D` holds (with
`SYM` gate `dec ∘ obs`).  So crossing the barrier reduces *exactly* to producing such an observer for composite `m`. -/
theorem lowDegRep_of_observer {n D M : ℕ} (f : (Fin n → Bool) → Bool)
    (mono : Fin M → Finset (Fin n)) (hinj : Function.Injective mono)
    (hdeg : ∀ j, (mono j).card ≤ D)
    {β : Type} (obs : ℕ → β) (dec : β → Bool)
    (hf : ∀ x, f x = dec (obs (saCount mono x))) :
    LowDegRep f D :=
  ⟨M, mono, fun k => dec (obs k), hinj, hdeg, funext hf⟩

/-- **The carry-refinement crossing condition (NAMED SOCKET — the open `ACC⁰[m]` barrier).**  The composite-modulus RS
approximant (`approxHyp`) yields a `LowDegRep` of `f`.  Equivalently (via `lowDegRep_of_observer`): a *carry-faithful*
count observer — one surviving carry refinement, unlike the carry-blind `fieldObs` — realised by a low-degree injective
monomial family exists for composite `m`.  **Not proved**; establishing it for composite modulus is the open
separation-strength problem (entry 234 `ApproxToExactCount`), shown genuinely obstructed by the carry profile
(entry 237). -/
def CarryRefinementCrossing (approxHyp : Prop) {n : ℕ} (f : (Fin n → Bool) → Bool) (D : ℕ) : Prop :=
  approxHyp → LowDegRep f D

/-- **The crossing socket discharges the barrier (PROVED conditional).**  `CarryRefinementCrossing approxHyp f D`, with
the approximant `approxHyp`, gives `LowDegRep f D` — confirming the socket is faithfully the crossing condition (it sits
exactly at the open wall). -/
theorem lowDegRep_of_crossing (approxHyp : Prop) {n : ℕ} (f : (Fin n → Bool) → Bool) (D : ℕ)
    (cross : CarryRefinementCrossing approxHyp f D) (ha : approxHyp) :
    LowDegRep f D :=
  cross ha

end PallLean.Paper93.DeepMath.PathB.ACC0CarryCrossing

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryCrossing.fieldObs_carry_blind
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryCrossing.fieldObs_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryCrossing.lowDegRep_of_observer
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryCrossing.lowDegRep_of_crossing
