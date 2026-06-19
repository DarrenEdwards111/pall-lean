import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RuleLookup

/-!
# Phase-internal refinement — the lookup phase as primitive single-rule-comparison steps (proved)

Entry 309 built the phased physical machine `physU` at *phase* granularity (one macro-step per phase) and noted the
only refinement left: expanding a phase macro-step into primitive single-cell tape operations.  This file does that for
the representative non-trivial phase — **lookup** (rule scan) — refining its macro-step into a sequence of primitive
single-rule-comparison steps, with the *exact* step count `M.length`.

**The small-step scanner.**  A scan configuration `(remaining, acc)` carries the rules not yet examined and the matches
accumulated so far.  `scanStep` processes **one** rule per step: pop the head, append it to `acc` iff it matches.
Starting from `(M, [])`, after exactly `M.length` primitive steps it reaches `([], matchingRules M state sym)` — the
filter built one comparison at a time.

So the lookup phase's resource bound `≤ M.length` (entry 305) is realised as the *exact* primitive step count: the
macro-step is `M.length` single-rule comparisons.  Decode and re-encode are the analogous tape-cell traversals
(`|tape|` single-cell steps), and apply is `O(1)` — the same fold-as-small-steps pattern.

## What is proved (clean axioms, no `sorry`)

* **`scanStep`, `scanNTM`** — the single-rule-comparison step and its machine.
* **`scan_reaches`** — the fold: from `(rules, acc)`, in `rules.length` steps, reach `([], acc ++ rules.filter p)`
  (induction on `rules`).
* **`scan_phase_celled`** — the refinement: from `(M, [])`, in exactly `M.length` primitive steps, reach
  `([], matchingRules M state sym)` — the lookup phase as single-rule comparisons, exact step count.

## Honest scope

This refines the **lookup phase** macro-step into primitive single-rule-comparison steps with the exact count
`M.length` — matching the entry-305 resource bound, now as a literal step count.  It is the representative phase-internal
refinement; decode/re-encode (tape-cell traversal) and apply (`O(1)`) follow the same fold-as-small-steps pattern.
Pure list/automata bookkeeping, classical and mechanical, not an open problem.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ScanCellOps

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine TMTrans)
open PallLean.Paper93.DeepMath.PathB.ACC0RuleLookup (matchingRules)

/-- One primitive scan step: examine the head rule, appending it to the accumulator iff it matches. -/
def scanStep (p : TMTrans → Bool) : (List TMTrans × List TMTrans) → (List TMTrans × List TMTrans) → Prop
  | (t :: rest, acc), st => st = (rest, if p t then acc ++ [t] else acc)
  | ([], acc), st => st = ([], acc)

/-- The single-rule-comparison scan machine. -/
def scanNTM (p : TMTrans → Bool) : NTM where
  Config := List TMTrans × List TMTrans
  step := scanStep p
  init := fun _ => ([], [])
  accept := fun _ => False

/-- **The scan fold (PROVED).**  From `(rules, acc)`, in exactly `rules.length` primitive steps, the scanner reaches
`([], acc ++ rules.filter p)` — building the filtered list one comparison at a time.  Induction on `rules`. -/
theorem scan_reaches (p : TMTrans → Bool) (rules acc : List TMTrans) :
    reachIn (scanNTM p) rules.length (rules, acc) ([], acc ++ rules.filter p) := by
  induction rules generalizing acc with
  | nil => simp [reachIn]
  | cons t rest ih =>
    have hfilt : acc ++ (t :: rest).filter p
        = (if p t then acc ++ [t] else acc) ++ rest.filter p := by
      rw [List.filter_cons]
      by_cases hpt : p t <;> simp [hpt, List.append_assoc]
    rw [List.length_cons, hfilt]
    exact ⟨(rest, if p t then acc ++ [t] else acc), rfl, ih _⟩

/-- **The lookup phase, refined to primitive steps (PROVED).**  From `(M, [])`, in exactly `M.length` single-rule
comparisons, the scanner reaches `([], matchingRules M state sym)` — the lookup phase macro-step realised as `M.length`
primitive operations, the exact step count matching the entry-305 resource bound. -/
theorem scan_phase_celled (M : TMachine) (state : ℕ) (sym : Bool) :
    reachIn (scanNTM (fun t => decide (t.1 = (state, sym)))) M.length
      (M, []) ([], matchingRules M state sym) := by
  simpa [matchingRules] using scan_reaches (fun t => decide (t.1 = (state, sym))) M []

/-!
**The lookup phase, cell-refined.**  The rule scan is realised as `M.length` primitive single-rule-comparison steps
(`scan_phase_celled`), the exact count matching the entry-305 resource bound — the macro-step expanded into primitive
operations.  Decode/re-encode (tape-cell traversal) and apply (`O(1)`) follow the same fold-as-small-steps pattern.
Pure mechanical list/automata bookkeeping.  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ScanCellOps

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ScanCellOps.scan_reaches
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ScanCellOps.scan_phase_celled
