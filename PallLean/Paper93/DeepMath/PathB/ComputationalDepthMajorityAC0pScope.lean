import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUnifiedInverterFrontier

/-!
# Option A, scoped: `Majority ∉ AC⁰[p]` reduced to the standard `MOD_q ≤ Majority` reduction

Merging the two binding faces (low‑degree algebraic + `AC⁰[p]`) onto **one** predicate needs `Majority ∉ AC⁰[p]`.
The Razborov–Smolensky corpus proves `MOD_q ∉ AC⁰[p]` (no‑approximation core is `MOD_q`‑specific, via the
`F_{p^{q-1}}` ζ‑pairing).  Majority is not a direct corollary; closing it needs either a fresh Majority
approximate‑degree lower bound, or the classical reduction `MOD_q ≤_{AC⁰[p]} Majority` (since
`MOD_q ∈ TC⁰ = AC⁰(Majority)`).

This file takes the **reduction route**, honestly: it states the reduction as a *concrete circuit‑family
hypothesis* (`AC0pReduction`, a genuine `AC⁰[p]` many‑one closure — **not** a `P ≠ NP`‑strength conjecture; it is
a known, in‑principle‑formalizable fact whose only cost is building the padded‑threshold circuit) and proves
everything that follows from it.

## Proved (clean axioms, no `sorry`)

* `majority_not_AC0p_of_reduction` — **given** `MOD_q ≤_{AC⁰[p]} Majority`, no poly‑size `AC⁰[p]` family computes
  `majorityLang` (i.e. `Majority ∉ AC⁰[p]`), via `modq_not_in_nonuniform_AC0p`.
* `majority_resists_AC0p_of_reduction` — hence (given the reduction) `majorityF2` resists the `AC⁰[p]` inverter
  class, discharging the open cell of the unified frontier.
* `majority_witnesses_simultaneous_of_reduction` — **the payoff:** given the reduction, `majorityF2` satisfies
  **both** binding resistances, so `SimultaneousAlgAC0pResistance` holds.  The wall's binding pair collapses onto
  a single predicate (Majority), modulo a *known* reduction.

## Honest scope — exactly what is left, and that it is not `P ≠ NP`

The single remaining hypothesis `AC0pReduction (modqLang q) majorityLang p` is the classical
`MOD_q ≤_{AC⁰} Majority` reduction: build, from a poly‑size `AC⁰[p]` Majority family, a poly‑size `AC⁰[p]` family
for `MOD_q` (poly‑many threshold gadgets `[#ones ≥ k]` — each a Majority on a padded input via `padTrue` — combined
by an `AC⁰` selector for the residue).  The corpus supplies the padding/composition primitives (`padInputs`,
`padTrue`); the construction + correctness proof is real circuit work, **not** done here.  Crucially this
hypothesis is a *true, non‑conjectural* statement (it is just `MOD_q ∈ TC⁰`), unlike the global
`InversionHardness` — so this conditional is qualitatively different from the `P ≠ NP` wall: discharging it is
formalization labour, not a mathematical breakthrough.

So Option A reduces to: **formalize the padded‑threshold `MOD_q ≤ Majority` circuit.**  Done, it merges the
algebraic and `AC⁰[p]` faces onto Majority and leaves only the *automatic* (crossing/locality) conjuncts and the
extension to *all* poly inverters — the genuine `P ≠ NP` residue.
-/

namespace PallLean.Paper93.DeepMath.PathB.MajorityAC0pScope

open Finset
open PallLean.Paper93.DeepMath.PathB.MajorityAI
open PallLean.Paper93.DeepMath.PathB.GoldreichMajorityCandidate
open PallLean.Paper93.DeepMath.PathB.UnifiedInverterFrontier
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer7

/-- The **Majority language** (Bool form): `true` iff the weight reaches the threshold `⌈n/2⌉ = (n+1)/2`. -/
def majorityLang : BoolLang := fun n x => decide ((n + 1) / 2 ≤ (toSupp x).card)

/-- An **`AC⁰[p]` many‑one reduction** `L ≤ L'`: every poly‑size `AC⁰[p]` family computing `L'` yields one
computing `L`.  (`AC⁰[p]` closure under the reduction — a concrete circuit‑family statement.) -/
def AC0pReduction (L L' : BoolLang) (p : ℕ) : Prop :=
  ∀ F : Layer7.AC0pFamily p, IsPolyBounded F.sizeBound → F.Computes L' →
    ∃ G : Layer7.AC0pFamily p, IsPolyBounded G.sizeBound ∧ G.Computes L

/-- **`Majority ∉ AC⁰[p]`, given the reduction (proved).**  If `MOD_q` `AC⁰[p]`‑reduces to `Majority`
(`q ≠ p` primes), no poly‑size `AC⁰[p]` family computes `majorityLang` — else, by the reduction, one would
compute `MOD_q`, contradicting Razborov–Smolensky. -/
theorem majority_not_AC0p_of_reduction (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    (hred : AC0pReduction (modqLang q) majorityLang p)
    (F : Layer7.AC0pFamily p) (hpoly : IsPolyBounded F.sizeBound) :
    ¬ F.Computes majorityLang := by
  intro hComp
  obtain ⟨G, hGpoly, hGComp⟩ := hred F hpoly hComp
  exact modq_not_in_nonuniform_AC0p p q hpq G hGpoly hGComp

/-- Bridge: the `AC⁰[p]`‑side `majorityLang` is the `toBoolLang` image of the algebraic‑side `majorityF2`. -/
theorem toBoolLang_majorityF2 : toBoolLang majorityF2 = majorityLang := by
  funext n x
  show decide (majorityF2 n (toSupp x) = 1) = majorityLang n x
  simp only [majorityF2, majorityLang]
  rw [decide_eq_decide]
  exact maj_eq_one_iff _

/-- **Majority resists the `AC⁰[p]` class, given the reduction (proved).**  Discharges the unified frontier's
open cell: with the standard reduction, `majorityF2` satisfies `ResistsAC0p`. -/
theorem majority_resists_AC0p_of_reduction (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    (hred : AC0pReduction (modqLang q) majorityLang p) :
    ResistsAC0p majorityF2 p := by
  intro F hpoly hComp
  rw [toBoolLang_majorityF2] at hComp
  exact majority_not_AC0p_of_reduction p q hpq hred F hpoly hComp

/-- **The payoff (proved): Majority witnesses both binding resistances, given the reduction.**  Combining the
unconditional `majority_resists_lowDegree` with the reduction‑conditional `majority_resists_AC0p_of_reduction`,
`majorityF2` satisfies **both** conjuncts, so `SimultaneousAlgAC0pResistance` holds — the wall's binding pair is
realized by a single predicate, modulo the *known* reduction `MOD_q ≤ Majority`. -/
theorem majority_witnesses_simultaneous_of_reduction {t : ℕ} (ht : 1 ≤ t)
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    (hred : AC0pReduction (modqLang q) majorityLang p) :
    SimultaneousAlgAC0pResistance t p :=
  ⟨majorityF2, majority_resists_lowDegree ht, majority_resists_AC0p_of_reduction p q hpq hred⟩

end PallLean.Paper93.DeepMath.PathB.MajorityAC0pScope

#print axioms PallLean.Paper93.DeepMath.PathB.MajorityAC0pScope.majority_not_AC0p_of_reduction
#print axioms PallLean.Paper93.DeepMath.PathB.MajorityAC0pScope.majority_witnesses_simultaneous_of_reduction
