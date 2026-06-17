import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RuleLookup
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PhysicalStep

/-!
# The universal lookup phase — the rule scan finds the firing rule, with scan-cost bound

Second of entry 182's four per-phase realizations (after the rewrite phase, entry 183).  The **lookup phase** scans the
machine's transition table for the rule matching the current `(state, read symbol)`.  Using the proved rule-lookup
contract (`…ACC0RuleLookup`: `matchingRules`, `mem_matchingRules`, `concreteStep_iff_matching`,
`matchingRules_length_le`), this file proves the lookup phase as an *actual* reachability: when a step exists, the lookup
**finds** a genuinely-matching rule, that rule **fires** in one physical step (reaching the next configuration), and the
scan examines **at most `M.length` rules** — the lookup's step-cost bound.

## What is proved (clean axioms, no `sorry`)

* **`lookup_fires`** — a rule found by the lookup fires in one step: `t ∈ matchingRules M c.1 (readSym c) →
  reachIn (toNTM M) 1 c (applyTrans c t)`.
* **`lookup_phase`** — the lookup phase realized: a step `concreteStep M c d` ⇒ the lookup finds a matching rule `t`
  (`t ∈ matchingRules M c.1 (readSym c)`) with `reachIn (toNTM M) 1 c (applyTrans c t)` (it fires), `d = applyTrans c t`
  (it reaches the intended config), and `(matchingRules M c.1 (readSym c)).length ≤ M.length` (the scan-cost bound).

## Honest scope

This realizes the lookup phase's **core operation**: the scan of the transition table (`matchingRules`) finds the
firing rule, the found rule advances the configuration in one step (`firing_rule_step`), and the scan cost is bounded by
the table size `M.length` — the `bLookup` of entry 182, here `≤ M.length`.  What it does **not** do is realise the scan
as the *universal* machine `U` walking the *encoded* transition table on its own tape (the `encodeTape` layout) and
matching the encoded `(state, sym)` — splicing the scan into `U`'s transition table over the encoding, with the exact
per-rule step count, is the remaining step.  This is classical Turing-machine construction, not an open problem; nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalLookupPhase

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig readSym applyTrans concreteStep toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup
  (matchingRules mem_matchingRules concreteStep_iff_matching matchingRules_length_le)
open PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep (firing_rule_step)

/-- **A rule found by the lookup fires in one step (proved).**  If `t` is in the lookup `matchingRules M c.1
(readSym c)`, then `t` genuinely matches (`mem_matchingRules`) and so fires, reaching `applyTrans c t` in one physical
step (`firing_rule_step`). -/
theorem lookup_fires (M : TMachine) (c : CConfig) (t : TMTrans)
    (ht : t ∈ matchingRules M c.1 (readSym c)) :
    reachIn (toNTM M) 1 c (applyTrans c t) := by
  obtain ⟨htM, ht1⟩ := (mem_matchingRules M c.1 (readSym c) t).mp ht
  exact firing_rule_step M c t htM ht1

/-- **The lookup phase realized (proved): the scan finds the firing rule, which advances in one step, scan `≤ M.length`.**
When a step `concreteStep M c d` exists, the rule-table scan `matchingRules M c.1 (readSym c)` contains a rule `t` that
(a) fires in one physical step `reachIn (toNTM M) 1 c (applyTrans c t)`, (b) reaches the intended `d = applyTrans c t`,
and (c) the scan examines at most `M.length` rules.  This discharges the lookup phase of entry 182 as an actual
reachability with the scan-cost bound (`bLookup ≤ M.length`). -/
theorem lookup_phase (M : TMachine) (c d : CConfig) (h : concreteStep M c d) :
    ∃ t ∈ matchingRules M c.1 (readSym c),
      reachIn (toNTM M) 1 c (applyTrans c t)
      ∧ d = applyTrans c t
      ∧ (matchingRules M c.1 (readSym c)).length ≤ M.length := by
  obtain ⟨t, ht, hd⟩ := (concreteStep_iff_matching M c d).mp h
  obtain ⟨htM, ht1⟩ := (mem_matchingRules M c.1 (readSym c) t).mp ht
  exact ⟨t, ht, firing_rule_step M c t htM ht1, hd, matchingRules_length_le M c.1 (readSym c)⟩

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalLookupPhase

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalLookupPhase.lookup_fires
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalLookupPhase.lookup_phase
