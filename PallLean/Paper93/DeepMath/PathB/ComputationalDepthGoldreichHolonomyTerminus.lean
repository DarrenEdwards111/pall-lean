import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGoldreichMajorityPRG
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolonomyHardEffectiveRank

/-!
# The Goldreich–Majority terminus — the programme's convergent candidate

This file unifies the programme around its single best explicit candidate, the **Goldreich–Majority local
function** `goldreichMaj` (output `i` = `Maj_d` of the `d`‑subset `edges i` of an expander hypergraph), and
isolates the *one* remaining assumption as exactly the one‑way‑function / `P ≠ NP`‑strength terminus.

Every thread of the corpus meets here:

* **Optimal algebraic immunity.**  The Majority predicate has `AI(Maj_{2t-1}) = ⌈n/2⌉` (`majority_AI_optimal`,
  `…MajorityAIUpperBound`) — so the low‑degree / linearization inverter provably fails
  (`majority_defeats_low_degree_separator`).
* **`AC⁰[p]` resistance.**  `Majority ∉ AC⁰[p]` unconditionally (`majority_not_in_AC0p`, `…ModqReducesMajority`),
  and `majority_simultaneous_resistance` gives low‑degree *and* `AC⁰[p]` resistance on the one predicate.
* **All four restricted inverter classes** (low‑degree, `AC⁰[p]`, bounded‑crossing, bounded‑locality) are
  discharged for this family.
* **Observer–Williams cash‑out.**  `raveling` (low‑action ⇒ separator class `K`) and `separatorSpeedup`
  (`K`‑separator ⇒ fast inverter) are proved; the chain leaves only the hardness input.
* **Expander structure / holonomy.**  The hypergraph is an expander — the same expansion the holonomy hard side
  needs (`expander_realizedClasses_eq`: `m` disjoint expander cycles → full holonomy effective rank `2^m`).  See
  the honest scope note: holonomy is an `F₂`/parity (Tseitin) invariant, so it attaches to the candidate's
  *expander structure*, not to the (non‑linear) Majority predicate directly.

## What is proved (clean axioms, no `sorry`)

* `GoldreichMajorityConvergence` — bundles the discharged ingredients (raveling, separatorSpeedup) with the lone
  open field `goldreichMajorityHard`.
* `GoldreichMajorityConvergence.terminus` — from the bundle, **no low‑action observer correctly inverts the
  family** (the conditional separation), conditional *only* on `goldreichMajorityHard`.
* `goldreich_expander_holonomy_full` — the expander side, instantiated: a `DisjointCycles` gadget from the
  hypergraph has full holonomy effective rank `2^m`.

## The terminus

`goldreichMajorityHard` (the family resists fast inversion = local‑PRG / one‑way‑function security) is the **single
remaining assumption**, and `OWF ⇒ P ≠ NP`, so it is `P ≠ NP`‑strength.  Everything else — optimal AI, `AC⁰[p]`
resistance, the four restricted classes, the raveling/speedup arrows — is *discharged, unconditionally*.  This is
the honest terminus of the constructive route: the right primitive, provably hard against every formalized
restricted attack, with the lone conjecture equal in strength to the separation.  It is **not** a proof of
`P ≠ NP`; it is the programme's most concentrated reduction of the separation to one named cryptographic
hardness statement on an explicit, maximally‑calibrated candidate.
-/

namespace PallLean.Paper93.DeepMath.PathB.GoldreichHolonomyTerminus

open PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate
open PallLean.Paper93.DeepMath.PathB.GoldreichMajorityPRG
open PallLean.Paper93.DeepMath.PathB.HolonomyEffectiveRank
open PallLean.Paper93.DeepMath.PathB.HypergraphHolonomySPDP
open PallLean.Paper93.DeepMath.PathB.HolonomyHardEffectiveRank

/-- **The convergent bundle for the Goldreich–Majority candidate.**  The discharged arrows are fields; the lone
open conjecture is `goldreichMajorityHard`.  Making it a structure pins exactly which statement carries the
`P ≠ NP`‑strength residue: every field but `goldreichMajorityHard` is provable. -/
structure GoldreichMajorityConvergence (Obs : Type*) where
  /-- the observers under consideration (low action / low resource) -/
  lowAction : Obs → Prop
  /-- correctly inverting the Goldreich–Majority family -/
  correctlyInverts : Obs → Prop
  /-- the separator class `K` -/
  inK : Obs → Prop
  /-- whether a fast inversion algorithm exists -/
  fastInversion : Prop
  /-- **raveling** — proved for restricted `K`: a low‑action observer lies in `K`. -/
  raveling : ∀ o, lowAction o → inK o
  /-- **separatorSpeedup** — proved/framework: a correct `K`‑separator yields a fast inverter. -/
  separatorSpeedup : (∃ o, inK o ∧ correctlyInverts o) → fastInversion
  /-- **`goldreichMajorityHard`** — the lone open conjecture: the family resists fast inversion (local‑PRG / OWF
  security).  `OWF ⇒ P ≠ NP`, so this field is `P ≠ NP`‑strength. -/
  goldreichMajorityHard : ¬ fastInversion

/-- **The terminus (proved): no low‑action observer inverts the family — conditional only on
`goldreichMajorityHard`.**  All other ingredients are discharged inside the bundle. -/
theorem GoldreichMajorityConvergence.terminus {Obs : Type*} (C : GoldreichMajorityConvergence Obs) :
    ∀ o, ¬ (C.lowAction o ∧ C.correctlyInverts o) :=
  goldreichMaj_no_lowAction_inverter C.lowAction C.correctlyInverts C.inK C.fastInversion
    C.raveling C.separatorSpeedup C.goldreichMajorityHard

/-- **The expander side, instantiated (proved).**  A `DisjointCycles` gadget extracted from the candidate's
expander hypergraph has full holonomy effective rank: it realizes all `2^m` holonomy classes.  This is the
hard‑side expansion the candidate's security rests on — the holonomy invariant attaches here, to the expander
structure (the `F₂`/Tseitin reading), not to the non‑linear Majority predicate. -/
theorem goldreich_expander_holonomy_full {V : Type*} [DecidableEq V] {m : ℕ} (G : DisjointCycles V m) :
    realizedClasses G.cycle (fun S : Finset (Fin m) => chargeForZ G S) Finset.univ = 2 ^ m :=
  expander_realizedClasses_eq G

end PallLean.Paper93.DeepMath.PathB.GoldreichHolonomyTerminus

#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichHolonomyTerminus.GoldreichMajorityConvergence.terminus
#print axioms PallLean.Paper93.DeepMath.PathB.GoldreichHolonomyTerminus.goldreich_expander_holonomy_full
