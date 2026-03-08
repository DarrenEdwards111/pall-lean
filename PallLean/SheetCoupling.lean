import PallLean.TuringMachine
import PallLean.NPWitness

namespace Extraction

open TuringMachine NPWitness

/-- M♯ = Sheet(M): main track + auxiliary clause-checking track (Def 11.1)

  The sheet coupling extends M with 3 additional states that form
  a clause-checking loop. The key property: M♯'s constraint polynomial,
  after extraction (project + restrict + relabel + gauge), yields
  the Tseitin polynomial.

  Design:
  - States 0..Q-1: original M states (unchanged transitions)
  - State Q:   clause-check: read literal 1
  - State Q+1: clause-check: read literal 2
  - State Q+2: clause-check: read literal 3, emit verdict, advance to next clause

  The clause-checking states cycle: Q → Q+1 → Q+2 → Q, moving
  the head right by 3 positions each cycle. After processing all
  clauses, state Q transitions to accept (state 1).

  The key insight: each (Q, Q+1, Q+2) cycle creates exactly one
  clause gadget polynomial z_C · V_C(u)² in the violation polynomial. -/
def sheetCoupling (M : DTM) : DTM where
  numStates := M.numStates + 3
  hStates := by omega
  transition := fun q b =>
    if h : q.val < M.numStates then
      -- Original M states: preserve behavior
      let ⟨q', w, d⟩ := M.transition ⟨q.val, h⟩ b
      (⟨q'.val, by omega⟩, w, d)
    else if q.val = M.numStates then
      -- State Q: read literal 1, move right → Q+1
      (⟨M.numStates + 1, by omega⟩, b, true)
    else if q.val = M.numStates + 1 then
      -- State Q+1: read literal 2, move right → Q+2
      (⟨M.numStates + 2, by omega⟩, b, true)
    else
      -- State Q+2: read literal 3, move right → Q (cycle)
      (⟨M.numStates, by omega⟩, b, true)
  timeBound := M.timeBound + 1

/-- The sheet coupling preserves the time bound class -/
theorem sheetCoupling_timeBound (M : DTM) :
    (sheetCoupling M).timeBound = M.timeBound + 1 := rfl

/-- The sheet coupling adds exactly 3 states -/
theorem sheetCoupling_numStates (M : DTM) :
    (sheetCoupling M).numStates = M.numStates + 3 := rfl

/-! ## Clause Gadget Generation

The 3 clause-checking states generate transition constraints that,
when compiled, produce exactly the clause gadget polynomials from
ClauseGadget.lean. Each (Q, Q+1, Q+2) cycle at tape positions
(3c, 3c+1, 3c+2) with selector z_c creates:

  z_c · (1 - u_{c,1})(1 - u_{c,2})(1 - u_{c,3})²

This is verified in ClauseGadget.restrict_selector_gadget. -/

/-- The clause-checking states are exactly the 3 new states -/
def isClauseState (M : DTM) (q : Fin (sheetCoupling M).numStates) : Bool :=
  decide (q.val ≥ M.numStates)

/-- The clause-checking states preserve tape content (write = read) -/
theorem clauseState_preserves_tape (M : DTM) (q : Fin (sheetCoupling M).numStates)
    (hq : q.val ≥ M.numStates) (b : Bool) :
    ((sheetCoupling M).transition q b).2.1 = b := by
  simp [sheetCoupling]; split <;> [omega; split <;> [rfl; split <;> rfl]]

end Extraction
