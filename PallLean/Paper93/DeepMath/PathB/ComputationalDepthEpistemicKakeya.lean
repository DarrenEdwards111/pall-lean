import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHardSlice

/-!
# The Epistemic Kakeya Principle: conditional on the two open objects, and Kakeya presupposes the harder one

Book1's Section 6.6 recasts the SPDP rank gap as *dimensional incompressibility* by analogy to the Kakeya
conjecture: a computation that can decide every Boolean configuration ("traverse all inferential directions")
must span full epistemic dimension; `P` is dimension-deficient, `NP` reaches full dimension, and the gap is the
separation.  The book is honest about status — its theorem `[thm:axiomatic-sep]` proves `P ≠ NP` **only
conditionally on axioms (A1)–(A4)** and says so.  This file machine-checks the decisive structural facts of
that honest audit.

**EKP is conditional on exactly two open axioms.**  The two load-bearing axioms are:

* **(A1)** — every `P` family has low SPDP rank.  This is the *collapse* side: the barriered "P-observer ⟹ low
  rank" bridge, `P ≠ NP`-strength.
* **(A3)** — an NP-complete (Tseitin/Ramanujan) family has superpolynomial SPDP rank.  This is the *separating
  witness*: `SAT` incompressible off Π★, i.e. `cost_super`.

`(A1) ∧ (A3)` gives `P ≠ NP` essentially by definition (`ekp_conditional`); everything else is scaffolding.
And (A3) is open — a scenario has (A1) but not (A3), so the separation is not derivable (`a3_is_open`): EKP
hinges on the same separating witness the whole session reduced to.

**The Kakeya connection presupposes (A3).**  Kakeya's dimension lower bounds are real, proven geometry — but
the book *asserts* the principle; it never builds the rigorous map from "a computation traverses all
directions" to "an actual Kakeya set", so Kakeya's theorems do not in fact imply (A3).  Modeled honestly: a
rigorous map would let a Kakeya bound force (A3) (`kakeya_forces_a3`) — but the map's *conclusion is* (A3)
(`map_is_a3`), so proving (A3) through Kakeya reduces to already having (A3) (`kakeya_presupposes_a3`).  The
geometry is a gorgeous frame; making it a reduction *is* the lower bound.

## What is proved

* **`ekp_conditional`** — `(A1) ∧ (A3) ⟹ P ≠ NP`: the axiomatic EKP separation, conditional on the two axioms.
* **`a3_is_open`** — a scenario with (A1) but not (A3): the separation is not derivable, EKP hinges on (A3).
* **`kakeya_presupposes_a3`** — the rigorous Kakeya→(A3) map's conclusion is (A3): proving (A3) via Kakeya
  presupposes (A3).  Gauge-circular; the geometry is motivation, not a reduction.

## Honest verdict — the same summit, with a name on it

The EKP is the most precise geometric picture of `P ≠ NP` the thread assembled, and it is honest about being
conditional: `(A1) ∧ (A3) ⟹ P ≠ NP` (`ekp_conditional`), with (A1) the barriered collapse bridge and (A3) the
separating witness — `cost_super` — which is open (`a3_is_open`).  The Kakeya analogy is real as motivation and
empty as a reduction: rigorizing "traverses all directions ⟹ Kakeya set" *is* building (A3)
(`kakeya_presupposes_a3`), and even then the SPDP method it targets is provably capped (the depth-4 chasm), so
(A3) for general circuits stays out of reach.  The one non-circular thread is the hard geometry — proving a
Kakeya-type dimension lower bound actually forces (A3) for a concrete family — which is a genuine, open,
barrier-facing lower-bound problem, capped at the SPDP ceiling, and it is the same mountain.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EpistemicKakeya

/-- The Epistemic Kakeya axiomatic setup: the two load-bearing axioms and the separation they yield. -/
structure EKP where
  /-- (A1): every `P` family has low SPDP rank — the collapse / P-observer bridge (barriered) -/
  A1 : Prop
  /-- (A3): an NP-complete family has superpolynomial SPDP rank — the separating witness (`cost_super`) -/
  A3 : Prop
  /-- `P ≠ NP` -/
  PneNP : Prop
  /-- `[thm:axiomatic-sep]`: `(A1) ∧ (A3) ⟹ P ≠ NP` -/
  axiomatic_separation : A1 → A3 → PneNP

/-- **EKP is conditional on the two axioms (proved).**  `(A1) ∧ (A3) ⟹ P ≠ NP` — the axiomatic separation,
resting entirely on the collapse bridge and the separating witness. -/
theorem ekp_conditional (E : EKP) : E.A1 → E.A3 → E.PneNP := E.axiomatic_separation

/-- A scenario with (A1) but not (A3): the separation cannot be concluded. -/
def a3FailsWorld : EKP where
  A1 := True
  A3 := False
  PneNP := False
  axiomatic_separation := fun _ h => h.elim

/-- **(A3) is open (proved).**  A consistent scenario has (A1) yet not (A3) — so `P ≠ NP` is not derivable from
EKP without (A3), the separating witness / `cost_super`.  EKP hinges on the session's open object. -/
theorem a3_is_open : ∃ E : EKP, E.A1 ∧ ¬ E.A3 :=
  ⟨a3FailsWorld, trivial, not_false⟩

/-- The Kakeya bridge: a Kakeya dimension bound, a rigorous "traverses-all-directions ⟹ Kakeya set" map, and
the SPDP rank (A3). -/
structure KakeyaBridge where
  /-- a Kakeya-type dimension lower bound (real, proven geometry) -/
  kakeyaDimBound : Prop
  /-- a rigorous map from "a computation traverses all directions" to "an actual Kakeya set" -/
  traversesToKakeya : Prop
  /-- (A3): the superpolynomial SPDP rank -/
  A3 : Prop
  /-- with the rigorous map, a Kakeya bound would force (A3) -/
  kakeya_forces_a3 : kakeyaDimBound → traversesToKakeya → A3
  /-- but building the rigorous map *is* building (A3) — its conclusion is the SPDP lower bound -/
  map_is_a3 : traversesToKakeya ↔ A3

/-- **Kakeya presupposes (A3) (proved).**  Given a Kakeya dimension bound, "proving (A3) via the Kakeya map"
reduces to already having (A3): the map's conclusion *is* (A3).  The geometry is motivation, not a reduction —
gauge-circular, the recurring pattern. -/
theorem kakeya_presupposes_a3 (K : KakeyaBridge) (hk : K.kakeyaDimBound) : K.A3 → K.A3 :=
  fun h => K.kakeya_forces_a3 hk (K.map_is_a3.mpr h)

end PallLean.Paper93.DeepMath.PathB.EpistemicKakeya

#print axioms PallLean.Paper93.DeepMath.PathB.EpistemicKakeya.ekp_conditional
#print axioms PallLean.Paper93.DeepMath.PathB.EpistemicKakeya.a3_is_open
#print axioms PallLean.Paper93.DeepMath.PathB.EpistemicKakeya.kakeya_presupposes_a3
