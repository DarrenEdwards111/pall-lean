import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEq

/-!
# Kleene interpreter project — indicator Codes for branch-free handlers (PROVED)

Key simplification for the recursive handlers: with the Option encoding (`none = 0`, `some v = v+1`),
`none`-propagation and the guard become **arithmetic**, not branching.  E.g. the `pair` handler is
`[n ≤ k] · isPos(ea) · isPos(eb) · (pair(ea-1)(eb-1)+1)` (all `mulCode`), where the indicators are:

  `leqIndicatorCode` — `(pair n k) ↦ if n ≤ k then 1 else 0` (`= isZero (n - k)`).
  `isPosCode` — `e ↦ if e = 0 then 0 else 1` (the "is `some`" indicator).

## What is proved (clean axioms, no `sorry`)

* `leqIndicatorCode`, `eval_leqIndicatorCode`, `isPosCode`, `eval_isPosCode`.

## Honest scope

The indicators that make the handlers branch-free.  The recursive handlers, the per-cell body,
`spec = encoded evaln`, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- `if n ≤ k then 1 else 0`, as a `Code` on `(pair n k)`. -/
def leqIndicatorCode : Code := Code.comp isZeroCode subCode

theorem eval_leqIndicatorCode (n k : ℕ) :
    leqIndicatorCode.eval (Nat.pair n k) = Part.some (if n ≤ k then 1 else 0) := by
  rw [show leqIndicatorCode.eval (Nat.pair n k) = (subCode.eval (Nat.pair n k)).bind isZeroCode.eval from rfl,
      eval_subCode, Part.bind_some, eval_isZeroCode]
  congr 1; by_cases h : n ≤ k <;> simp [h] <;> omega

/-- `if e = 0 then 0 else 1` (the "`some`" indicator), as a `Code`. -/
def isPosCode : Code := Code.comp subCode (Code.pair (Code.const 1) isZeroCode)

theorem eval_isPosCode (e : ℕ) : isPosCode.eval e = Part.some (if e = 0 then 0 else 1) := by
  rw [show isPosCode.eval e = ((Code.pair (Code.const 1) isZeroCode).eval e).bind subCode.eval from rfl]
  rw [show (Code.pair (Code.const 1) isZeroCode).eval e = Part.some (Nat.pair 1 (if e = 0 then 1 else 0)) from by
    rw [show (Code.pair (Code.const 1) isZeroCode).eval e = Nat.pair <$> (Code.const 1).eval e <*> isZeroCode.eval e from rfl, eval_isZeroCode]; simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some]]
  rw [Part.bind_some, eval_subCode]
  congr 1; by_cases h : e = 0 <;> simp [h]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_leqIndicatorCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_isPosCode
