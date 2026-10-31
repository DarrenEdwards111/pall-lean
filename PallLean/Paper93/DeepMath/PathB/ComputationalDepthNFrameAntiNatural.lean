import Mathlib

/-!
# N-Frame: scoping an anti-natural-proofs candidate

The previous scoping showed the sensitivity candidate `bdry` caps out at `AC⁰`.  That is not an accident of `bdry`: it is
forced by the **Razborov–Rudich natural-proofs barrier**.  A lower-bound "invariant" `Φ` is a *natural property* against a
class if it is

* **Constructive** — decidable in time `poly(2ⁿ)` from the truth table;
* **Large** — satisfied by a noticeable fraction of all `2^{2ⁿ}` functions;
* **Useful** — `Φ f ⇒ f ∉ class` (a lower-bound certificate).

Razborov–Rudich: if pseudorandom function generators exist, **no natural property is useful against `P/poly`**.  So any
`P/poly`-beating invariant must be **anti-natural** — it must *drop constructivity or largeness*.  This file formalises the
barrier as a constraint on candidates and derives exactly what a winning invariant must look like — and the trap it must
avoid.

  `Useful` / `Large` — the two formalisable barrier conditions (usefulness = lower-bound certificate; largeness =
        a `1/K` fraction of all functions).
  `large_useful_not_constructive` / `constructive_useful_not_large` — **PROVED (from an RR instance)**: any invariant
        useful against the class must be non-constructive *or* non-large — i.e. anti-natural.  This is the precise
        requirement on a candidate.
  `not_large_singleton` — **PROVED**: a "rarity" invariant (holds for one function) is genuinely non-large — one honest
        way to be anti-natural.
  `tautological_useful` — **PROVED**: the invariant "`f ∉ class`" is trivially useful — but it is the class complement
        itself: non-constructive *and circular* (it presupposes exactly what it must certify).  This is the trap.

## Honest scope — the frontier, stated plainly

The barrier tells us the *shape* of a winning candidate (anti-natural: non-constructive or non-large) and rules out the
obvious ones: a constructive-and-large invariant (like `bdry`/sensitivity, or raw degree) *cannot* separate `P/poly`
under standard assumptions, and the tautological anti-natural invariant is circular and proves nothing.  A genuine
candidate must be anti-natural **and** non-circular — e.g. a Kolmogorov / `MCSP`-flavoured incompressibility measure
(non-constructive) or a uniformity-based diagnostic (as in Williams' `NEXP ⊄ ACC⁰`, which evades naturalness via
diagonalisation but does not reach `P vs NP`).  **No such invariant is known** for `P vs NP`; the two other barriers
(relativisation and algebrisation) further constrain uniform/algebraic routes.  This file honestly formalises the
constraint and the trap; it does **not** exhibit a barrier-evading invariant, because none is known.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural

variable {n : ℕ}

/-- A Boolean function on the cube — a truth table. -/
abbrev BoolFn (n : ℕ) := (Fin n → Bool) → Bool

/-- A property / candidate invariant, viewed as a predicate on truth tables. -/
abbrev FnProperty (n : ℕ) := BoolFn n → Prop

/-- **Usefulness**: the property certifies non-membership in the class — a lower-bound certificate. -/
def Useful (Φ InClass : FnProperty n) : Prop := ∀ f, Φ f → ¬ InClass f

/-- **Largeness**: the property holds for at least a `1/K` fraction of all `2^{2ⁿ}` functions. -/
def Large (Φ : FnProperty n) (K : ℕ) : Prop :=
  Fintype.card (BoolFn n) ≤ K * {f | Φ f}.ncard

/-- **Anti-natural necessity (proved, from an RR instance).**  Given the Razborov–Rudich barrier `rr` (no
constructive-and-large property is useful against the class), any *large* invariant that is *useful* against the class
must be **non-constructive**.  A winning candidate cannot be a natural property. -/
theorem large_useful_not_constructive
    {Φ Ppoly : FnProperty n} {K : ℕ} {Constructive : FnProperty n → Prop}
    (rr : Constructive Φ → Large Φ K → Useful Φ Ppoly → False)
    (hlarge : Large Φ K) (huseful : Useful Φ Ppoly) :
    ¬ Constructive Φ :=
  fun hc => rr hc hlarge huseful

/-- **Dual anti-natural necessity (proved).**  Any *constructive* invariant useful against the class must be **non-large**
— the other honest way out of naturalness. -/
theorem constructive_useful_not_large
    {Φ Ppoly : FnProperty n} {K : ℕ} {Constructive : FnProperty n → Prop}
    (rr : Constructive Φ → Large Φ K → Useful Φ Ppoly → False)
    (hconstr : Constructive Φ) (huseful : Useful Φ Ppoly) :
    ¬ Large Φ K :=
  fun hl => rr hconstr hl huseful

/-- **A genuinely non-large (rare) property (proved).**  A singleton property holds for exactly one function, so it is not
large for any bound `K` below the total count `2^{2ⁿ}`.  This is one honest anti-natural direction — *rarity* — but a rare
property is useful only if its lone function is already outside the class, which is the circular trap below. -/
theorem not_large_singleton (g : BoolFn n) {K : ℕ} (hK : K < Fintype.card (BoolFn n)) :
    ¬ Large (fun f => f = g) K := by
  unfold Large
  rw [show {f : BoolFn n | f = g} = {g} from rfl, Set.ncard_singleton, mul_one]
  omega

/-- **The circularity trap (proved).**  The property "`f` is not in the class" is trivially useful — but it is literally
the class complement: it is non-constructive and *circular*, presupposing exactly the non-membership it is meant to
certify.  This is why "just use the anti-natural invariant" is not a route: the obvious anti-natural invariant proves
nothing new. -/
theorem tautological_useful (Ppoly : FnProperty n) : Useful (fun f => ¬ Ppoly f) Ppoly :=
  fun _ h => h

end PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural.large_useful_not_constructive
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural.not_large_singleton
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAntiNatural.tautological_useful
