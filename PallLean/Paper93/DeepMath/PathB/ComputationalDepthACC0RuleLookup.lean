import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# The rule-lookup sub-machine — specification proved, physical tape-scan socketed

The first sub-machine of the physical universal machine: given the simulated state and the symbol under the simulated
head, find the matching transition rules of the encoded machine `M`.  This file defines the **rule-lookup** as a
function on the transition table and proves it **correct against the step relation** — `concreteStep` is exactly
"pick a matching rule and apply it".  It also bounds the lookup's work by the table length (the scan cost).  The
physical realisation — a `U`-sub-machine scanning the encoded table on the tape — is the remaining socket.

## What is proved (clean axioms, no `sorry`)

* **`matchingRules M state sym`** — the rules whose left-hand side is `(state, sym)`.
* **`mem_matchingRules`** — membership: `t ∈ matchingRules M state sym ↔ t ∈ M ∧ t.1 = (state, sym)`.
* **`concreteStep_iff_matching`** — the lookup is correct: `concreteStep M c d ↔ ∃ t ∈ matchingRules M c.1 (readSym c),
  d = applyTrans c t`.  The nondeterministic step *is* selecting a matching rule and applying it.
* **`matchingRules_length_le`** — the lookup examines at most `M.length` rules (the scan cost bound).

## Honest scope

The lookup *specification* is proved correct against `concreteStep` — the contract the physical sub-machine must meet.
Realising it as `U`-transitions that scan the encoded transition table on the tape (in `O(M.length · encoding)` steps)
is the socket.  This does **not** build the physical sub-machine.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine TMTrans CConfig readSym applyTrans concreteStep)

/-- **The rule lookup**: the transitions of `M` whose left-hand side matches `(state, sym)`. -/
def matchingRules (M : TMachine) (state : ℕ) (sym : Bool) : List TMTrans :=
  M.filter (fun t => decide (t.1 = (state, sym)))

/-- **Membership in the lookup (proved).** -/
theorem mem_matchingRules (M : TMachine) (state : ℕ) (sym : Bool) (t : TMTrans) :
    t ∈ matchingRules M state sym ↔ t ∈ M ∧ t.1 = (state, sym) := by
  simp only [matchingRules, List.mem_filter, decide_eq_true_eq]

/-- **The lookup is correct (proved): a step is exactly "pick a matching rule and apply it".**
`concreteStep M c d ↔ ∃ t ∈ matchingRules M c.1 (readSym c), d = applyTrans c t`. -/
theorem concreteStep_iff_matching (M : TMachine) (c d : CConfig) :
    concreteStep M c d ↔ ∃ t ∈ matchingRules M c.1 (readSym c), d = applyTrans c t := by
  simp only [concreteStep, matchingRules, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨t, htM, ht1, hd⟩
    exact ⟨t, ⟨htM, ht1⟩, hd⟩
  · rintro ⟨t, ⟨htM, ht1⟩, hd⟩
    exact ⟨t, htM, ht1, hd⟩

/-- **The lookup examines at most `M.length` rules (proved): the scan cost bound.** -/
theorem matchingRules_length_le (M : TMachine) (state : ℕ) (sym : Bool) :
    (matchingRules M state sym).length ≤ M.length :=
  List.length_filter_le _ M

end PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup.mem_matchingRules
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup.concreteStep_iff_matching
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup.matchingRules_length_le
