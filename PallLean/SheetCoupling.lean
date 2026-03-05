import PallLean.TuringMachine

namespace Extraction

open TuringMachine

/-- M♯ = Sheet(M): main track + auxiliary clause track (Def 11.1) -/
def sheetCoupling (M : DTM) : DTM where
  numStates := M.numStates + 3
  hStates := by omega
  transition := fun q b =>
    if h : q.val < M.numStates then
      let ⟨q', w, d⟩ := M.transition ⟨q.val, h⟩ b
      (⟨q'.val, by omega⟩, w, d)
    else (q, b, true)
  timeBound := M.timeBound + 1

end Extraction
