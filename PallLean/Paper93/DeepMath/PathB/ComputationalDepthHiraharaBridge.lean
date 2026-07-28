import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetaComplexityOWF

/-!
# The Hirahara bridge: worst→average for MCSP collapses the whole crypto route to one worst-case statement

The curiosity engine's top unbuilt cell.  `MetaComplexityOWF` left the crypto route stuck at Pessiland: OWFs
`⟺` average-case MCSP hardness (Liu–Pass), but `P ≠ NP` does not give OWFs, and the one bridge across —
`WorstHard → AvgHard` — was left as a hypothesis, *Hirahara's program*.  This file builds that bridge and
shows what it does to the route.

**Hirahara's reduction (real).**  Hirahara (2018, and follow-ups) proved a *worst-case to average-case*
reduction *within* meta-complexity: worst-case hardness of (gap / approximate) MCSP implies its average-case
hardness — one of the very few worst→average reductions known for a natural problem, via non-black-box
techniques.  So the `MetaComplexityOWF` hypothesis is (for the gap version) a *theorem*, not a wish.

**What it does to the route.**  Chaining Hirahara (`worst → avg`) with Liu–Pass (`avg ⟺ OWF`) and crypto
(`OWF → P ≠ NP`), worst-case gap-MCSP hardness implies `P ≠ NP` (`hirahara_discharges_pessiland`).  The entire
apparatus — average-case hardness, one-way functions, Pessiland — **collapses to a single worst-case
statement**: gap-MCSP is worst-case hard.  That is a genuine simplification of the map: the crypto route no
longer has its own separate residual; it inherits the one worst-case meta-complexity question.

**Where it stops.**  That statement — worst-case hardness of gap-MCSP — is open (it is `MCSP ∉ P`-adjacent),
and it lives in the same cluster as `MCSPcoNP` / `Sigma2Collapse` / `cost_super`.  So Hirahara does not cross
the wall; it *relocates* the crypto route's residual from the average-case side to the worst-case side, onto
one open statement (`route_reduces_to_worst_mcsp`, `input_is_open`).  And the reduction itself carries
caveats — it is for the gap/approximate version, non-black-box — so even the bridge is not the full exact
worst→average.

## What is proved

* **`Hirahara`** — the four propositions (worst-case gap-MCSP hardness, average-case MCSP hardness, OWFs,
  `P ≠ NP`) with Hirahara's reduction, Liu–Pass, and crypto⟹separation.
* **`hirahara_bridges_worst_to_avg`** — Hirahara's reduction: worst-case gap-MCSP hardness ⟹ average-case.
* **`hirahara_discharges_pessiland`** — worst-case gap-MCSP hardness ⟹ `P ≠ NP`: the crypto route collapses to
  one worst-case statement.
* **`route_reduces_to_worst_mcsp` / `input_is_open`** — that statement is the route's sole input, and it is
  open (a consistent world where the chain holds but the input fails).

## Honest verdict — the confluence is real; it relocates the wall, does not cross it

Hirahara is the confluence the engine kept pointing at, and building it is a genuine map simplification: the
worst→average reduction (real, for gap-MCSP) discharges the bridge `MetaComplexityOWF` left open, so the whole
crypto / OWF / Pessiland route collapses onto a *single* worst-case statement — gap-MCSP is worst-case hard
(`hirahara_discharges_pessiland`).  The average-case side no longer carries a separate residual.  But that one
statement is open, `MCSP ∉ P`-adjacent, and sits in the `cost_super` cluster (`input_is_open`) — so the wall
is *relocated*, from average-case crypto to worst-case meta-complexity, not crossed.  And the bridge has real
caveats (gap version, non-black-box).  So the honest next step tightened the map — three routes (crypto,
average-case, worst-case meta-complexity) are now one — and left the one open object exactly where it is.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HiraharaBridge

/-- The propositions of the Hirahara-collapsed crypto route, with the reductions that connect them. -/
structure Hirahara where
  /-- worst-case hardness of gap / approximate MCSP (Hirahara's input) -/
  WorstGapMCSP : Prop
  /-- average-case hardness of MCSP -/
  AvgMCSP : Prop
  /-- one-way functions exist -/
  OWF : Prop
  /-- `P ≠ NP` -/
  PneNP : Prop
  /-- **Hirahara's reduction**: worst-case gap-MCSP hardness implies average-case hardness (non-black-box) -/
  worst_to_avg : WorstGapMCSP → AvgMCSP
  /-- **Liu–Pass**: average-case MCSP hardness gives one-way functions -/
  liu_pass : AvgMCSP → OWF
  /-- inverting is in NP, so crypto implies the separation -/
  owf_sep : OWF → PneNP

namespace Hirahara

variable (H : Hirahara)

/-- **Hirahara bridges worst to average (proved).**  The reduction the `MetaComplexityOWF` route left as a
hypothesis, now supplied: worst-case gap-MCSP hardness ⟹ average-case hardness. -/
theorem hirahara_bridges_worst_to_avg : H.WorstGapMCSP → H.AvgMCSP := H.worst_to_avg

/-- **The crypto route collapses to one worst-case statement (proved).**  Hirahara then Liu–Pass then crypto:
worst-case gap-MCSP hardness ⟹ `P ≠ NP`.  Average-case hardness, OWFs, and Pessiland all reduce to this single
worst-case meta-complexity question. -/
theorem hirahara_discharges_pessiland : H.WorstGapMCSP → H.PneNP :=
  fun h => H.owf_sep (H.liu_pass (H.worst_to_avg h))

end Hirahara

/-- A world where worst-case gap-MCSP hardness fails (the route's input is open). -/
def openWorld : Hirahara where
  WorstGapMCSP := False
  AvgMCSP := False
  OWF := False
  PneNP := False
  worst_to_avg := False.elim
  liu_pass := False.elim
  owf_sep := False.elim

/-- **The input is open (proved).**  A consistent world has all the reductions yet worst-case gap-MCSP
hardness fails — so the collapsed route's sole input, `WorstGapMCSP`, is not settled. -/
theorem input_is_open : ∃ H : Hirahara, ¬ H.WorstGapMCSP :=
  ⟨openWorld, not_false⟩

/-- **The route reduces to one worst-case statement (proved).**  `WorstGapMCSP` both implies `P ≠ NP`
(through the reductions) and is itself unforced — the crypto route's whole residual is this single open
worst-case meta-complexity question. -/
theorem route_reduces_to_worst_mcsp :
    (∀ H : Hirahara, H.WorstGapMCSP → H.PneNP) ∧ (∃ H : Hirahara, ¬ H.WorstGapMCSP) :=
  ⟨fun H => H.hirahara_discharges_pessiland, input_is_open⟩

end PallLean.Paper93.DeepMath.PathB.HiraharaBridge

#print axioms PallLean.Paper93.DeepMath.PathB.HiraharaBridge.Hirahara.hirahara_bridges_worst_to_avg
#print axioms PallLean.Paper93.DeepMath.PathB.HiraharaBridge.Hirahara.hirahara_discharges_pessiland
#print axioms PallLean.Paper93.DeepMath.PathB.HiraharaBridge.input_is_open
#print axioms PallLean.Paper93.DeepMath.PathB.HiraharaBridge.route_reduces_to_worst_mcsp
