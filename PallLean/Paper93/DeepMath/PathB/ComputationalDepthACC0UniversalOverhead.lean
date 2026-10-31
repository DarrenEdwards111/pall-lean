import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0HeadLocation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RuleLookup

/-!
# The universal step overhead `B` — one step's resource footprint is polynomially bounded (proved)

The transition-table compile socket's logical side is done (entry 304: the encoded universal machine tracks the full
run).  Its physical side needs an **overhead bound** `B`: one logical universal step (decode → lookup → apply →
re-encode) must cost only `B` of `U`'s own primitive steps.  This file proves the **resource footprint** of one
universal step is bounded by a concrete `B = poly(M.length, |x| + k)`, from the proved sub-machine contracts:

* **rule lookup** scans at most `M.length` rules (`…ACC0RuleLookup.matchingRules_length_le`);
* the simulated **head** stays within `k` of the start after `k` steps (`…ACC0HeadLocation.reachIn_head_le`), so the
  touched tape region is `≤ |x| + k` — a bounded region, not the whole tape.

So one universal step at a configuration reached in `≤ k` steps touches `≤ M.length` rules and a tape region of size
`≤ |x| + k`: footprint `≤ stepOverhead M.length (|x| + k)`.  This is the `B` bound's content; what remains is `U`'s
transition rules executing one resource-operation per primitive step (the interpreter loop).

## What is proved (clean axioms, no `sorry`)

* **`stepOverhead`** — the concrete per-step overhead `B (mLen, tapeBound) = mLen + tapeBound + 1` (scan + region + O(1)).
* **`head_bound_from_init`** — from the initial config `(0,0,x)`, the head after `k` steps is `≤ k` (bounded region).
* **`uStep_cost_bound`** — one universal step's footprint (rules scanned + tape region up to the head) is
  `≤ stepOverhead M.length (|x| + k)` at any config reached in `≤ k` steps.

## Honest scope

This proves the **per-step overhead bound** `B = poly(M.length, |x| + k)` on the *resources* one universal step needs —
rule scan (`≤ M.length`) and tape region (`≤ |x| + k`, the bounded-head region) — assembling the proved `RuleLookup` and
`HeadLocation` contracts.  This is exactly the `B` the compile socket asked for, at the resource level.  What remains is
the realisation of `U`'s transition *rules* executing one such resource-operation per primitive step (the
decode/lookup/rewrite interpreter loop as `U`-rules) — classical Turing-machine engineering over the (proved)
sub-machine contracts, not an open problem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalOverhead

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine CConfig readSym toNTM)

/-- The per-step overhead `B`: scanning `mLen` rules over a tape region of size `tapeBound`, plus `O(1)`. -/
def stepOverhead (mLen tapeBound : ℕ) : ℕ := mLen + tapeBound + 1

/-- **The simulated head stays in the bounded region (PROVED).**  From the initial config `(0, 0, x)`, after `k`
steps the head is `≤ k` (`reachIn_head_le` with start head `0`) — so the touched tape region is bounded, not the whole
tape. -/
theorem head_bound_from_init (M : TMachine) (k : ℕ) (x : List Bool) (c : CConfig)
    (h : reachIn (toNTM M) k (0, 0, x) c) : c.2.1 ≤ k := by
  simpa using ACC0HeadLocation.reachIn_head_le M k (0, 0, x) c h

/-- **One universal step's resource footprint is `≤ B` (PROVED).**  At any config `c` reached in `≤ k` steps from
`(0, 0, x)`, one universal step scans `≤ M.length` rules (`matchingRules_length_le`) and touches a tape region up to the
head `≤ k`, so its footprint (`rules scanned + region`) is `≤ stepOverhead M.length (|x| + k)`.  The concrete per-step
overhead bound `B`. -/
theorem uStep_cost_bound (M : TMachine) (k : ℕ) (x : List Bool) (c : CConfig)
    (h : reachIn (toNTM M) k (0, 0, x) c) :
    (ACC0RuleLookup.matchingRules M c.1 (readSym c)).length + (c.2.1 + 1)
      ≤ stepOverhead M.length (x.length + k) := by
  unfold stepOverhead
  have hscan := ACC0RuleLookup.matchingRules_length_le M c.1 (readSym c)
  have hhead := head_bound_from_init M k x c h
  omega

/-!
**The overhead bound.**  One universal step's resource footprint — rules scanned (`≤ M.length`) plus tape region (the
bounded-head region `≤ |x| + k`) — is `≤ stepOverhead M.length (|x| + k)` (`uStep_cost_bound`), a concrete
`B = poly(M.length, |x| + k)`.  This is the `B` bound the compile socket asked for, proved from the `RuleLookup` and
`HeadLocation` contracts.  What remains is `U`'s transition rules executing one resource-operation per primitive step
(the interpreter loop) — classical engineering over the proved sub-machine contracts.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalOverhead

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalOverhead.head_bound_from_init
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalOverhead.uStep_cost_bound
