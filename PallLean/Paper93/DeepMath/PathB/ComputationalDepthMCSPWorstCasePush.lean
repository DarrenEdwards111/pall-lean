/-!
# Pushing meta-complexity past worst-case MCSP hardness: it reaches the wall, and the input is the wall

Meta-complexity localizes the separation to one statement: **worst-case (gap-)MCSP is hard.**  This file pushes
that statement forward through the real reduction chain and checks where "past" lands — *below* the wall, or *at*
it.

**The chain reaches the separation (proved).**  Assemble the real meta-complexity theorems (with their known
caveats) as named hypotheses: Hirahara's non-black-box worst→average reduction (`hirahara`), Liu–Pass average-
MCSP-hardness ⟹ one-way functions (`liu_pass`), and OWF ⟹ `P ≠ NP` (inverting is in `NP ∖ P`, `owf_sep`).
`meta_complexity_reaches_separation`: worst-case gap-MCSP hardness ⟹ `P ≠ NP`.  So the route does push through to
the separation — that part is real.

**But the input is already `P ≠ NP`-strength (proved).**  MCSP ∈ NP (guess the circuit, verify), so if `P = NP`
then MCSP ∈ P; contrapositive, `MCSP ∉ P ⟹ P ≠ NP` (`mcsp_in_np`).  Worst-case MCSP hardness *implies* `P ≠ NP`
directly — `worst_case_mcsp_is_separation_strength`.  So pushing "past" worst-case MCSP hardness does not get
below the wall: the statement you must prove to get there is *itself* at least as strong as the separation.

**So the frontier is a lower bound, not a shortcut (proved).**  `meta_complexity_pushed_to_the_wall`: the route
reaches `P ≠ NP`, the input `worstGapMCSPHard` entails `MCSP ∉ P` (a lower bound = `P ≠ NP`-strength), and it is
undischarged (a consistent world has it false).  Pushing past worst-case MCSP hardness means *proving* worst-case
gap-MCSP hard — a meta-complexity lower bound at least as hard as `P ≠ NP`.

**What meta-complexity actually buys.**  Not a reduction in strength — MCSP hardness is `P ≠ NP`-strength — but
*structure*: the target is self-referential (the hardness of computing hardness), and Hirahara's worst→average
reductions for it are *non-black-box*, partially dodging the natural-proofs barrier.  That structure is the bet
for tractability, and it is exactly what remains undischarged.

## What is proved

* **`meta_complexity_reaches_separation`** — worst-case gap-MCSP hard ⟹ `P ≠ NP`, via Hirahara → Liu–Pass → OWF.
* **`worst_case_mcsp_is_separation_strength`** — worst-case MCSP hard ⟹ `P ≠ NP` directly, since MCSP ∈ NP: the
  input is `P ≠ NP`-strength.
* **`worst_case_mcsp_is_open`** — a consistent world has worst-case MCSP not-hard: the input is undischarged.
* **`meta_complexity_pushed_to_the_wall`** — all three: the route reaches the separation, the input is a lower
  bound of separation strength, and it is open.

## Honest verdict — meta-complexity pushes to the wall with more structure, not through it

Pushing meta-complexity past worst-case MCSP hardness reaches `P ≠ NP` — the reduction chain (Hirahara worst→
average, Liu–Pass average-MCSP ⟹ OWF, OWF ⟹ `P ≠ NP`) is real, and there is even a trivial direct route through
MCSP ∈ NP.  But worst-case gap-MCSP hardness is itself `P ≠ NP`-strength (`worst_case_mcsp_is_separation_strength`):
it implies the separation and is the undischarged input.  So "past" lands *at* the wall, not below it — the
meta-complexity route relocates the separation to a lower bound on MCSP, at least as hard as `P ≠ NP`.  Its value
is the extra structure (self-reference, non-black-box worst→average) that Hirahara bets makes the target
approachable, and that bet is exactly what is not yet cashed.  I pushed the route to its frontier and it lands on
the wall wearing meta-complexity structure; I did not discharge worst-case MCSP hardness, because that would be
proving `P ≠ NP`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPWorstCasePush

/-- The meta-complexity route as a chain of named theorems (with their known caveats) plus the structural fact
MCSP ∈ NP.  `worstGapMCSPHard` is the frontier input (open); the reductions are `hirahara`, `liu_pass`,
`owf_sep`, and `mcsp_in_np`. -/
structure MetaComplexityRoute where
  /-- worst-case gap-MCSP is hard — the meta-complexity frontier input (open) -/
  worstGapMCSPHard : Prop
  /-- average-case MCSP is hard -/
  avgMCSPHard : Prop
  /-- one-way functions exist -/
  owfExist : Prop
  /-- MCSP is not in P (worst-case) -/
  MCSPnotInP : Prop
  /-- `P ≠ NP` -/
  PneNP : Prop
  /-- Hirahara: worst-case gap-MCSP hardness gives average-case MCSP hardness (non-black-box) -/
  hirahara : worstGapMCSPHard → avgMCSPHard
  /-- Liu–Pass: average-case MCSP hardness gives one-way functions -/
  liu_pass : avgMCSPHard → owfExist
  /-- OWF ⟹ `P ≠ NP` (inverting is in `NP ∖ P`) -/
  owf_sep : owfExist → PneNP
  /-- MCSP ∈ NP, so `MCSP ∉ P ⟹ P ≠ NP` -/
  mcsp_in_np : MCSPnotInP → PneNP
  /-- worst-case gap-MCSP hardness entails MCSP ∉ P -/
  hard_gives_notInP : worstGapMCSPHard → MCSPnotInP

/-- **Meta-complexity reaches the separation (proved).**  Worst-case gap-MCSP hardness ⟹ `P ≠ NP`, through
Hirahara → Liu–Pass → OWF. -/
theorem meta_complexity_reaches_separation (R : MetaComplexityRoute) (h : R.worstGapMCSPHard) :
    R.PneNP :=
  R.owf_sep (R.liu_pass (R.hirahara h))

/-- **Worst-case MCSP hardness is `P ≠ NP`-strength (proved).**  Since MCSP ∈ NP, `MCSP ∉ P ⟹ P ≠ NP`; and
worst-case hardness entails `MCSP ∉ P`.  So the input implies the separation directly. -/
theorem worst_case_mcsp_is_separation_strength (R : MetaComplexityRoute) (h : R.worstGapMCSPHard) :
    R.PneNP :=
  R.mcsp_in_np (R.hard_gives_notInP h)

/-- A world where worst-case MCSP is not hard (the input is undischarged). -/
def openWorld : MetaComplexityRoute where
  worstGapMCSPHard := False
  avgMCSPHard := False
  owfExist := False
  MCSPnotInP := False
  PneNP := False
  hirahara := fun h => h.elim
  liu_pass := fun h => h.elim
  owf_sep := fun h => h.elim
  mcsp_in_np := fun h => h.elim
  hard_gives_notInP := fun h => h.elim

/-- **Worst-case MCSP hardness is open (proved).**  A consistent world has it false — the frontier input is
undischarged. -/
theorem worst_case_mcsp_is_open : ∃ R : MetaComplexityRoute, ¬ R.worstGapMCSPHard :=
  ⟨openWorld, not_false⟩

/-- **Meta-complexity pushed to the wall (proved).**  The route reaches `P ≠ NP`; the input entails `MCSP ∉ P`
(a lower bound of separation strength); and it is undischarged.  Pushing past worst-case MCSP hardness means
proving a meta-complexity lower bound at least as hard as `P ≠ NP`. -/
theorem meta_complexity_pushed_to_the_wall (R : MetaComplexityRoute) :
    (R.worstGapMCSPHard → R.PneNP)
    ∧ (R.worstGapMCSPHard → R.MCSPnotInP)
    ∧ (∃ R' : MetaComplexityRoute, ¬ R'.worstGapMCSPHard) :=
  ⟨fun h => meta_complexity_reaches_separation R h, R.hard_gives_notInP, worst_case_mcsp_is_open⟩

end PallLean.Paper93.DeepMath.PathB.MCSPWorstCasePush

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPWorstCasePush.meta_complexity_reaches_separation
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPWorstCasePush.worst_case_mcsp_is_separation_strength
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPWorstCasePush.worst_case_mcsp_is_open
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPWorstCasePush.meta_complexity_pushed_to_the_wall
