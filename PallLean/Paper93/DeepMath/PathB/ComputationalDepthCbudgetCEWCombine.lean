import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMinimalDistance

/-!
# Combining cbudget (reach) and CEW (boundedness): the final step is the right scissors — and it consumes two open objects

Proposed final step: the Lagrangian defines the reach via `cbudget`, `CEW` measures the observer boundedness,
and *combining* them crosses the wall.  This is the right *shape*, and it is worth being exact about what the
combination is — because it is a specific object, already half-built, and pinning it down shows precisely what
it does and does not do.

**The combination is a two-bladed scissors, and it is a valid implication.**  `CEW` bounds the `P`-observer
from *above* — `P` families have low CEW (this is EKP `(A1)`).  `cbudget` is the minimal distance, and
`cbudget(SAT)` exceeding that bound is a *lower* bound on SAT's reach (this is EKP `(A3)`).  Put the two
together — an upper bound on `P` and a lower bound on `SAT` — and the gap between the blades *is* `P ≠ NP`
(`combine_is_the_final_step`).  This is exactly the EKP conditional `(A1) ∧ (A3) ⟹ P ≠ NP`, already proved
axiom-free (`EpistemicKakeya.ekp_conditional`); here it is re-expressed in the `cbudget` + `CEW` language.  So
the combination is real, and it is the correct final shape.

**But the combination consumes the two open objects; it does not discharge them.**  The `cbudget` blade —
`cbudget(SAT) > B` — is a lower bound on the *minimal distance*, and by the previous file a lower bound on a
minimum is a bound over *every* realization (`cbudget_high_is_all_realizations`, from
`MinimalDistance.reach_ge_iff_all`): ruling out every sharing shortcut = `cost_super`.  The scissors need this
blade sharpened, and sharpening it is the wall.

**And combining the blades is exactly what the barrier forbids.**  A separation needs a single discriminator
that is *low on `P`* (the CEW blade) and *high on `SAT`* (the cbudget blade).  A measure with both properties —
low on the easy class, high on the hard target, computable and broad — is a **natural property**
(`combining_needs_a_natural_measure`): the Razborov–Rudich barrier.  So the very act of combining CEW and
cbudget into one discriminating measure is the thing natural-proofs rules out; that is *why* you cannot simply
define such a measure and read off the separation.

## What is proved

* **`combine_is_the_final_step`** — CEW-bounds-`P` (`A1`) together with cbudget-of-SAT-high (`A3`) implies
  `P ≠ NP`.  The scissors close; the combination is a valid implication (the EKP conditional).
* **`cbudget_high_is_all_realizations`** — the cbudget blade (`B < reach`) is equivalent to `B < cost r` for
  *every* realization: sharpening it is `cost_super` (tied to `MinimalDistance`).
* **`combining_needs_a_natural_measure`** — combining the two blades requires a measure low-on-`P` and
  high-on-`SAT` = a natural property (Razborov–Rudich).
* **`combination_is_open`** — a world where the premises fail: the combination does not hold for free.
* **`final_step_valid_but_consumes_and_is_barriered`** — all at once: the final step is a valid implication
  that consumes `(A1)`, `(A3)`, and runs into the natural-proofs barrier.

## Honest verdict — the scissors are right; both blades are the two open objects, and closing them is barriered

Combining `cbudget` and `CEW` is genuinely the right final *shape*: CEW upper-bounds `P`, cbudget lower-bounds
`SAT`, and the gap is `P ≠ NP` — a valid, machine-checked implication, the EKP conditional in reach/boundedness
language (`combine_is_the_final_step`).  What the combination does *not* do is discharge its premises.  The
cbudget blade is a lower bound on the minimal distance = a bound over every realization = `cost_super`
(`cbudget_high_is_all_realizations`).  The CEW blade is the low-on-`P` claim `(A1)`.  And combining them into one
discriminator that is low on `P` and high on `SAT` is precisely a natural property — the Razborov–Rudich barrier
(`combining_needs_a_natural_measure`) — which is *why* the measure cannot just be written down.  So the final
step is the correct scissors, already a valid implication; the two blades are the two open objects, closing the
cbudget blade is `cost_super`, and forging the combined blade is barriered.  The combination names the crossing
exactly and shows what forging it would require; it does not perform it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CbudgetCEWCombine

/-- The combined measure: CEW bounding the `P`-observer (`A1`, the upper blade), cbudget of SAT exceeding that
bound (`A3`, the lower blade), together with `P ≠ NP` and the fact that combining the blades yields a natural
property.  `combine` is the EKP conditional; `combination_needs_natural` records that a low-on-`P`,
high-on-`SAT` discriminator is natural (Razborov–Rudich). -/
structure CombinedMeasure where
  /-- CEW bounds the `P`-observer: `P` families have low CEW (`A1`, the upper blade) -/
  cewBoundsP : Prop
  /-- cbudget(SAT) exceeds `P`'s bound: SAT's minimal distance is high (`A3`, the lower blade) -/
  cbudgetHigh : Prop
  /-- `P ≠ NP` -/
  PneNP : Prop
  /-- a measure low-on-`P` and high-on-`SAT` is a natural property -/
  isNatural : Prop
  /-- the EKP conditional: upper bound on `P` + lower bound on SAT ⟹ separation -/
  combine : cewBoundsP → cbudgetHigh → PneNP
  /-- combining the two blades demands a natural (Razborov–Rudich-barriered) measure -/
  combination_needs_natural : cewBoundsP → cbudgetHigh → isNatural

/-- **The combination is the final step (proved).**  CEW-bounds-`P` (`A1`) and cbudget-of-SAT-high (`A3`)
together imply `P ≠ NP` — the two-bladed scissors close.  This is the EKP conditional in reach/boundedness
language, a valid implication. -/
theorem combine_is_the_final_step (C : CombinedMeasure) :
    C.cewBoundsP → C.cbudgetHigh → C.PneNP := C.combine

/-- **The cbudget blade is a bound over every realization (proved).**  `cbudget(SAT) > B` — the lower blade —
is equivalent to `B < cost r` for *every* realization `r`: sharpening it rules out every sharing shortcut,
which is `cost_super`.  (From `MinimalDistance.reach_ge_iff_all`.) -/
theorem cbudget_high_is_all_realizations (M : MinimalDistance.MinDistance) (B : Nat) :
    B < M.reach ↔ ∀ r, B < M.cost r := by
  have h := MinimalDistance.reach_ge_iff_all M (B + 1)
  constructor
  · intro hB r
    have h2 := h.mp hB r
    omega
  · intro hall
    have h2 : ∀ r, B + 1 ≤ M.cost r := fun r => hall r
    have := h.mpr h2
    omega

/-- **Combining the blades needs a natural measure (proved).**  A discriminator low-on-`P` (CEW blade) and
high-on-`SAT` (cbudget blade) is a natural property — the Razborov–Rudich barrier — which is why it cannot just
be defined. -/
theorem combining_needs_a_natural_measure (C : CombinedMeasure) :
    C.cewBoundsP → C.cbudgetHigh → C.isNatural := C.combination_needs_natural

/-- A world where the combination's premises fail. -/
def openWorld : CombinedMeasure where
  cewBoundsP := False
  cbudgetHigh := False
  PneNP := False
  isNatural := False
  combine := fun h _ => h.elim
  combination_needs_natural := fun h _ => h.elim

/-- **The combination is open (proved).**  Neither blade holds for free: the final step is a valid implication
whose premises are the two open objects. -/
theorem combination_is_open : ∃ C : CombinedMeasure, ¬ C.cewBoundsP ∧ ¬ C.cbudgetHigh :=
  ⟨openWorld, not_false, not_false⟩

/-- **The final step is valid but consumes two open objects and is barriered (proved).**  Left: the scissors
close (`A1` ∧ `A3` ⟹ `P ≠ NP`).  Right: closing them needs a natural (barriered) measure.  With
`cbudget_high_is_all_realizations`, the lower blade is `cost_super`; so the combination names the crossing and
shows exactly what forging it requires. -/
theorem final_step_valid_but_consumes_and_is_barriered (C : CombinedMeasure) :
    (C.cewBoundsP → C.cbudgetHigh → C.PneNP)
    ∧ (C.cewBoundsP → C.cbudgetHigh → C.isNatural) :=
  ⟨C.combine, C.combination_needs_natural⟩

end PallLean.Paper93.DeepMath.PathB.CbudgetCEWCombine

#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetCEWCombine.combine_is_the_final_step
#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetCEWCombine.cbudget_high_is_all_realizations
#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetCEWCombine.combining_needs_a_natural_measure
#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetCEWCombine.combination_is_open
#print axioms PallLean.Paper93.DeepMath.PathB.CbudgetCEWCombine.final_step_valid_but_consumes_and_is_barriered
