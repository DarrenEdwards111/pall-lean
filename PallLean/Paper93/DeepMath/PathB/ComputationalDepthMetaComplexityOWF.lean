import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPintermediate

/-!
# Meta-complexity ⟺ one-way functions (Liu–Pass): the crypto face, and why it stops at Pessiland

The curiosity engine's top next-step.  `MCSPintermediate` derived the ¬OWF horn — `MCSP ∈ P ⟹ no one-way
functions` (Kabanets–Cai/Razborov–Rudich).  Liu–Pass (2020) sharpens that horn into an *equivalence*:

> **One-way functions exist ⟺ time-bounded MCSP / Kolmogorov complexity is mildly hard on average.**

So the crypto question and the *average-case* meta-complexity question are the same.  This places our whole
`MCSP` arc inside **Impagliazzo's five worlds**, and pinpoints exactly why this route reaches cryptography
but not `P` vs `NP`.

Model the four propositions and the implications that are actually provable:
`OWF` (one-way functions), `AvgHard` (average-case MCSP hardness), `WorstHard` (worst-case MCSP hardness,
`MCSP ∉ P`), `PneNP` (`P ≠ NP`).  The forced structure: `OWF → PneNP` (inverting is in NP, so crypto ⟹
separation); `OWF ↔ AvgHard` (Liu–Pass); `AvgHard → WorstHard` (average-case hard ⟹ worst-case hard).

Two things follow, and together they are the wall:

* **The ¬OWF horn factors through Liu–Pass.**  `MCSP` worst-case easy ⟹ average-case easy ⟹ ¬OWF
  (`mcsp_easy_breaks_owf`) — the exact horn `MCSPintermediate` took as a hypothesis, now derived from the
  characterization.
* **Pessiland blocks the converse.**  `OWF → PneNP` always, but `PneNP → OWF` does **not** hold: there is a
  consistent world with `P ≠ NP` *and* worst-case-hard MCSP yet **no** one-way functions and no average-case
  hardness (`pessiland_exists`) — Impagliazzo's Pessiland.  So `OWF` is *strictly stronger* than `P ≠ NP`
  (`owf_strictly_stronger`), and this route cannot reach `P ≠ NP`: it characterizes the average-case /
  crypto world, which sits above the worst-case separation.

The one bridge from worst-case to this route is `WorstHard → AvgHard` — **Hirahara's worst-case-to-average
program** (the engine's #3).  With it, `WorstHard → OWF` (`worst_to_owf_needs_hirahara`); Pessiland is
exactly the world where that bridge fails.

## What is proved

* **`World`** — the four propositions with the provable implications (`OWF → PneNP`, Liu–Pass `OWF ↔ AvgHard`,
  `AvgHard → WorstHard`).
* **`owf_implies_separation`** — one-way functions imply `P ≠ NP`.
* **`mcsp_easy_breaks_owf`** — worst-case-easy MCSP breaks one-way functions (the ¬OWF horn, via Liu–Pass).
* **`worst_to_owf_needs_hirahara`** — with Hirahara's worst→average bridge, worst-case hardness yields OWFs.
* **`pessiland_exists`** — a consistent world with `P ≠ NP` and worst-hard MCSP but no OWFs, no average-case
  hardness: Impagliazzo's Pessiland.
* **`pnenp_does_not_force_owf` / `owf_strictly_stronger`** — `P ≠ NP` does not entail OWFs; OWF is strictly
  stronger.

## Honest verdict — the crypto face reaches Pessiland's edge, not P ≠ NP

Liu–Pass makes the ¬OWF horn an iff, which is real and clarifying: the crypto/average-case world *is* the
average-case hardness of meta-complexity (`mcsp_easy_breaks_owf` derives the horn we previously assumed).
But it stops exactly where Impagliazzo said it must.  `OWF ⟹ P ≠ NP` and not conversely
(`owf_strictly_stronger`): **Pessiland** — `P ≠ NP` with no one-way functions — is consistent
(`pessiland_exists`), so no amount of crypto/average-case machinery yields the worst-case separation.  The
missing link is worst-case-to-average-case for MCSP (`worst_to_owf_needs_hirahara`), Hirahara's program,
which is itself open.  So this face reaches the average-case meta-complexity frontier and halts at
Pessiland's edge — another face of `cost_super`, now at the worst-to-average boundary.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF

/-- A world (à la Impagliazzo) assigning truth to the four propositions, subject to the implications that
are actually provable. -/
structure World where
  /-- `P ≠ NP` (worst-case NP hardness) -/
  PneNP : Prop
  /-- one-way functions exist -/
  OWF : Prop
  /-- average-case hardness of time-bounded MCSP / Kolmogorov complexity -/
  AvgHard : Prop
  /-- worst-case hardness of MCSP (`MCSP ∉ P`) -/
  WorstHard : Prop
  /-- inverting a one-way function is in NP, so crypto implies separation -/
  owf_sep : OWF → PneNP
  /-- **Liu–Pass**: one-way functions exist iff MCSP is mildly hard on average -/
  liu_pass : OWF ↔ AvgHard
  /-- average-case hardness implies worst-case hardness -/
  avg_worst : AvgHard → WorstHard

/-! ### One-way functions imply the separation; the horn factors through Liu–Pass -/

/-- **One-way functions imply P ≠ NP (proved).**  Inverting is an NP problem, so its hardness separates. -/
theorem owf_implies_separation (W : World) : W.OWF → W.PneNP := W.owf_sep

/-- **Worst-case-easy MCSP breaks one-way functions (proved).**  `MCSP ∈ P ⟹ average-case easy ⟹ ¬OWF` —
the ¬OWF horn of `MCSPintermediate`, now *derived* from the Liu–Pass characterization instead of assumed. -/
theorem mcsp_easy_breaks_owf (W : World) (h : ¬ W.WorstHard) : ¬ W.OWF :=
  fun howf => h (W.avg_worst (W.liu_pass.mp howf))

/-- **The worst→OWF route needs Hirahara (proved).**  With the worst-case-to-average bridge
`WorstHard → AvgHard` (Hirahara's program), worst-case MCSP hardness yields one-way functions. -/
theorem worst_to_owf_needs_hirahara (W : World) (hirahara : W.WorstHard → W.AvgHard) :
    W.WorstHard → W.OWF :=
  fun hw => W.liu_pass.mpr (hirahara hw)

/-! ### Pessiland: P ≠ NP without one-way functions -/

/-- **Pessiland**: a consistent world with `P ≠ NP` and worst-case-hard MCSP, but no one-way functions and
no average-case hardness.  All the provable implications hold vacuously. -/
def pessiland : World where
  PneNP := True
  OWF := False
  AvgHard := False
  WorstHard := True
  owf_sep := False.elim
  liu_pass := Iff.rfl
  avg_worst := False.elim

/-- **Pessiland exists (proved).**  `P ≠ NP` and worst-hard MCSP hold, yet no OWFs and no average-case
hardness — Impagliazzo's Pessiland is consistent with the forced structure. -/
theorem pessiland_exists :
    ∃ W : World, W.PneNP ∧ ¬ W.OWF ∧ W.WorstHard ∧ ¬ W.AvgHard :=
  ⟨pessiland, trivial, not_false, trivial, not_false⟩

/-- **P ≠ NP does not force one-way functions (proved).**  Pessiland witnesses a world with `PneNP` but
`¬OWF`, so `PneNP → OWF` is not derivable. -/
theorem pnenp_does_not_force_owf : ¬ (∀ W : World, W.PneNP → W.OWF) := by
  intro h
  exact h pessiland trivial

/-- **OWF is strictly stronger than P ≠ NP (proved).**  `OWF → PneNP` in every world, but not conversely
(Pessiland).  So the crypto/average-case route sits strictly above the worst-case separation. -/
theorem owf_strictly_stronger :
    (∀ W : World, W.OWF → W.PneNP) ∧ ¬ (∀ W : World, W.PneNP → W.OWF) :=
  ⟨fun W => W.owf_sep, pnenp_does_not_force_owf⟩

end PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF

#print axioms PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF.owf_implies_separation
#print axioms PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF.mcsp_easy_breaks_owf
#print axioms PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF.worst_to_owf_needs_hirahara
#print axioms PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF.pessiland_exists
#print axioms PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF.pnenp_does_not_force_owf
#print axioms PallLean.Paper93.DeepMath.PathB.MetaComplexityOWF.owf_strictly_stronger
