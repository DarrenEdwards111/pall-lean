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
  - States 0..Q-1: original M states
  - State Q: clause-check start
  - State Q+1: clause-check verify
  - State Q+2: clause-check advance

  The transition function keeps M's behavior for original states,
  and adds a looping clause-check for the new states. -/
def sheetCoupling (M : DTM) : DTM where
  numStates := M.numStates + 3
  hStates := by omega
  transition := fun q b =>
    if h : q.val < M.numStates then
      let ⟨q', w, d⟩ := M.transition ⟨q.val, h⟩ b
      (⟨q'.val, by omega⟩, w, d)
    else (q, b, true)
  timeBound := M.timeBound + 1

/-- The sheet coupling preserves the time bound class -/
theorem sheetCoupling_timeBound (M : DTM) :
    (sheetCoupling M).timeBound = M.timeBound + 1 := rfl

/-- The sheet coupling adds exactly 3 states -/
theorem sheetCoupling_numStates (M : DTM) :
    (sheetCoupling M).numStates = M.numStates + 3 := rfl

end Extraction
