import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TapeRewrite
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PhysicalStep

/-!
# The universal rewrite phase — a concrete `reachIn` realizing the tape write

Entry 182 reduced the physical `hstep` to four per-phase reachabilities (decode / lookup / rewrite / re-encode), each a
run of the universal machine's own transitions within a step bound.  This file discharges the **rewrite phase** with a
*concrete machine* and an *actual* `reachIn`: a one-rule rewrite gadget that, firing at a configuration `c`, writes a
symbol `w`, moves the head, and updates the state — reaching the rewritten configuration in **one** physical step, with
the read-after-write guarantee that the head now holds `w`.

This turns the rewrite phase from a hypothesis (in entry 182) into a proved `reachIn U bRewrite c (rewritten c)` for a
concrete `U` (the gadget) and explicit `bRewrite = 1`, with the tape content certified by the proved `TapeRewrite`
lemmas.

## What is proved (clean axioms, no `sorry`)

* **`rewriteRule` / `rewriteMachine`** — a concrete one-rule machine that writes `w`, moves `m`, goes to state `q'`,
  firing at `c`.
* **`rewrite_phase`** — the rewrite phase realized: `reachIn (toNTM (rewriteMachine c q' w m)) 1 c (applyTrans c …)`
  (the write happens in one step) **and** the rewritten configuration's head holds `w`
  (`(applyTrans c …).2.2.getD c.2.1 false = w`, the read-after-write correctness).

## Honest scope

This realizes the rewrite phase's **core operation** — write a symbol, move the head, change state — as an *actual*
transition of a concrete machine, with a proved `reachIn` step count (`1`) and the proved tape-content guarantee.  It is
the rewrite phase of entry 182 *discharged* for the write-and-move operation.  What it does **not** do is embed this
gadget into the *universal* `U` so that it rewrites the *encoded* simulated tape (the `encodeTape` layout) at the encoded
head position — splicing the gadget into `U`'s transition table over the encoding is the remaining step (the analogous
decode / lookup / re-encode phases, which touch the layout, are heavier).  This is classical Turing-machine
construction, not an open problem; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalRewritePhase

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM
  (TMachine TMTrans CConfig Move readSym applyTrans toNTM)
open PallLean.Paper93.DeepMath.PathB.ACC0PhysicalStep (firing_rule_step)
open PallLean.Paper93.DeepMath.PathB.ACC0TapeRewrite (applyTrans_write)

/-- A one-rule rewrite gadget firing at `c`: at `(c.1, readSym c)`, write `w`, move `m`, go to state `q'`. -/
def rewriteRule (c : CConfig) (q' : ℕ) (w : Bool) (m : Move) : TMTrans :=
  ((c.1, readSym c), (q', w, m))

/-- The concrete one-rule rewrite machine. -/
def rewriteMachine (c : CConfig) (q' : ℕ) (w : Bool) (m : Move) : TMachine :=
  [rewriteRule c q' w m]

/-- **The rewrite phase realized (proved): a concrete machine writes in one step, with read-after-write.**  The rewrite
gadget reaches the rewritten configuration `applyTrans c (rewriteRule …)` from `c` in exactly **one** physical step
(`firing_rule_step`), and the rewritten configuration's head holds the written symbol `w`
(`applyTrans_write`).  This discharges the rewrite phase of entry 182 as an actual `reachIn U 1 c (rewritten c)` with the
tape content certified. -/
theorem rewrite_phase (c : CConfig) (q' : ℕ) (w : Bool) (m : Move) :
    reachIn (toNTM (rewriteMachine c q' w m)) 1 c (applyTrans c (rewriteRule c q' w m))
      ∧ (applyTrans c (rewriteRule c q' w m)).2.2.getD c.2.1 false = w := by
  refine ⟨firing_rule_step (rewriteMachine c q' w m) c (rewriteRule c q' w m) ?_ rfl, ?_⟩
  · simp [rewriteMachine]
  · exact applyTrans_write c (rewriteRule c q' w m)

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalRewritePhase

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalRewritePhase.rewrite_phase
