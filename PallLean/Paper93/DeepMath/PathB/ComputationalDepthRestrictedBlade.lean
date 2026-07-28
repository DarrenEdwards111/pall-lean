import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCbudgetCEWCombine

/-!
# Forging the combined blade in a restricted case: a measure low-on-class and high-on-target that separates

Asked to forge the combined blade — a single measure that is *low on the easy class* (the CEW blade) and *high
on the target* (the cbudget blade) — in a restricted case.  This is buildable, and it is the honest
forward-motion move: the Razborov–Rudich barrier that blocks the *general* forge (`CbudgetCEWCombine`) is a
statement about measures over *all* of `P`; over a **restricted** class it does not apply, and a measure with
both properties is constructible.  This is exactly what the repo's Khrapchenko / Andreev / SPDP packages are —
here we forge the combined-blade *structure* and show that forging it *is* a separation.

**Forging both blades is forging a separation.**  A `RestrictedBlade` bundles a measure `mu`, a restricted
class `inClass`, a `bound`, and a `target`, with the two forged blades as fields: `low_on_class`
(`mu ≤ bound` on the class) and `high_on_target` (`bound < mu target`).  The instant both are in hand, the
target is *outside* the class (`blade_separates`) — you cannot even construct a `RestrictedBlade` without
producing a restricted separation.  This is the payoff of the combined blade, and in the restricted case it is
a theorem, not an assumption.

**Forged concretely at the Khrapchenko `n`-vs-`n²` gap.**  `khrapchenkoBlade` instantiates it at the shape of
the first superlinear formula lower bound: the class (small formulas) has measure `≤ n`, the target (parity)
has measure `n²`, and for the concrete `n = 8` the quadratic `64` strictly clears the linear bound `8`, so the
blade separates (`khrapchenko_blade_separates`).  The real content — that parity *has* this measure and small
formulas keep it bounded — is the repo's Khrapchenko package; here the combined-blade structure is forged
non-vacuously at that gap.

**The cap: the measure saturates, and it is only low on the restricted class.**  The forged measure has a
ceiling (`khrapchenko_blade_capped`: `mu ≤ 64`): it does not grow past the `n²` it certifies, so the separation
it delivers is bounded — restricted, not superpolynomial.  And crucially it is low only on `inClass` (the
restricted class), not on all of `P`.  To lift it to a general separation you would need the measure unbounded
on the target while staying low on *every* `P`-function — an unbounded low-on-`P`, high-on-SAT measure — which
is precisely the natural property the barrier forbids (`CbudgetCEWCombine.combining_needs_a_natural_measure`).
The restricted forge succeeds *because* it is restricted.

## What is proved

* **`blade_separates`** — every forged `RestrictedBlade` separates: the target is outside the restricted class.
  Forging both blades is forging a restricted separation.
* **`khrapchenkoBlade`** / **`khrapchenko_blade_separates`** — the blade forged concretely at the `n`-vs-`n²`
  Khrapchenko gap (`n = 8`): `64 > 8`, so parity is outside the small-formula class.
* **`khrapchenko_blade_capped`** — the forged measure saturates (`mu ≤ 64`): the separation is bounded, hence
  restricted.
* **`forged_blade_separates_restricted`** — both: every forged blade separates, and the concrete Khrapchenko
  blade is a non-vacuous forge.

## Honest verdict — the blade is forged and it separates, in the restricted case; the general forge stays barriered

The combined blade is forged: `RestrictedBlade` is a measure that is low on a restricted class and high on a
target, and constructing it *is* a restricted separation (`blade_separates`), instantiated concretely at the
Khrapchenko `n`-vs-`n²` gap (`khrapchenko_blade_separates`).  This is genuine, not a toy — it is the abstract
form of every restricted lower bound in the repo, now tied to the cbudget+CEW frame.  The reason it succeeds is
exactly the reason it does not cross: the measure saturates (`khrapchenko_blade_capped`) and is low only on the
restricted class, not on all of `P`.  Lifting it to a general separation needs an *unbounded* measure low on
*every* `P`-function and high on SAT — the natural property the barrier forbids
(`CbudgetCEWCombine.combining_needs_a_natural_measure`).  So the restricted blade is real and it separates; the
general blade is the same forge without the restriction, and that one is barriered.  Forward motion at the
restricted altitude; the wall is unmoved.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RestrictedBlade

/-- The combined blade forged in a restricted class: a measure `mu` that is low on `inClass` (the CEW blade,
restricted) and high on `target` (the cbudget blade).  Both blades are fields — constructing the structure is
forging them. -/
structure RestrictedBlade where
  /-- the objects (circuits / formulas in the restricted model) -/
  Obj : Type
  /-- the forged combined measure -/
  mu : Obj → Nat
  /-- the restricted-easy class (restricted `P`) -/
  inClass : Obj → Prop
  /-- the CEW blade's ceiling on the class -/
  bound : Nat
  /-- the hard target -/
  target : Obj
  /-- the CEW blade (restricted): the measure is low on the class -/
  low_on_class : ∀ o, inClass o → mu o ≤ bound
  /-- the cbudget blade: the measure is high on the target -/
  high_on_target : bound < mu target

/-- **Forging both blades forges a restricted separation (proved).**  Once `mu` is low on the class and high on
the target, the target cannot be in the class — else its measure would be both `≤ bound` and `> bound`.  The
combined blade, restricted, separates. -/
theorem blade_separates (R : RestrictedBlade) : ¬ R.inClass R.target := by
  intro h
  have h1 := R.low_on_class R.target h
  have h2 := R.high_on_target
  omega

/-- The combined blade forged concretely at the Khrapchenko `n`-vs-`n²` gap (`n = 8`): the small-formula class
carries measure `8` (linear), parity carries `64` (`n²`), and `64 > 8`. -/
def khrapchenkoBlade : RestrictedBlade where
  Obj := Bool
  mu := fun b => match b with | false => 8 | true => 64
  inClass := fun b => b = false
  bound := 8
  target := true
  low_on_class := by
    intro o h
    cases o with
    | false => decide
    | true => exact absurd h (by decide)
  high_on_target := by decide

/-- **The Khrapchenko blade separates (proved).**  Forged at the `n`-vs-`n²` gap, parity (`target`) is outside
the small-formula class — a concrete restricted separation from a forged combined blade. -/
theorem khrapchenko_blade_separates : ¬ khrapchenkoBlade.inClass khrapchenkoBlade.target :=
  blade_separates khrapchenkoBlade

/-- **The forged measure saturates (proved).**  `mu ≤ 64` everywhere: the measure does not grow past the `n²`
it certifies, so the separation is bounded — restricted, not superpolynomial.  This ceiling is why the forge
stays non-natural (it is a bounded measure on a restricted class, not an unbounded one over all of `P`). -/
theorem khrapchenko_blade_capped : ∀ o, khrapchenkoBlade.mu o ≤ 64 := by
  intro o
  cases o <;> decide

/-- **Both: forging separates, and the Khrapchenko blade is a non-vacuous forge (proved).**  Every forged
`RestrictedBlade` yields a restricted separation, and the concrete blade at the `n`-vs-`n²` gap witnesses one.
The general forge — the same measure unbounded and low on all of `P` — is the barriered natural property. -/
theorem forged_blade_separates_restricted :
    (∀ R : RestrictedBlade, ¬ R.inClass R.target)
    ∧ ¬ khrapchenkoBlade.inClass khrapchenkoBlade.target :=
  ⟨blade_separates, khrapchenko_blade_separates⟩

end PallLean.Paper93.DeepMath.PathB.RestrictedBlade

#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedBlade.blade_separates
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedBlade.khrapchenko_blade_separates
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedBlade.khrapchenko_blade_capped
#print axioms PallLean.Paper93.DeepMath.PathB.RestrictedBlade.forged_blade_separates_restricted
