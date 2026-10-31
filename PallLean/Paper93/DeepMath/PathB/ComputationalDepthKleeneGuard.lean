import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCond

/-!
# Kleene interpreter project — Option-encoded guard (PROVED)

The per-cell body produces `evalnStep` results **Option-encoded** so the table can hold them
(`none = 0`, `some v = v + 1`).  `guardCode` realizes `evalnStep`'s `guard (n ≤ k)`: fed `sel = n - k`
(zero iff `n ≤ k`), it returns the encoded `some result` when the guard passes and `none` otherwise.

* `guardCode`, `eval_guardCode_le`, `eval_guardCode_gt`.

Honest scope: the guard.  The constructor handlers, the assembled per-cell body, the correctness chain, the
interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode
open Nat.Partrec

/-- Option-encoded guard: on `(result, sel)`, `sel = 0 ⇒ some result` (encoded `result+1`); `sel > 0 ⇒
none` (encoded `0`).  The per-cell body feeds `sel = n - k` (zero iff `n ≤ k`), realizing `evalnStep`'s
`guard (n ≤ k)`.  Encoding: `none = 0`, `some v = v + 1`. -/
def guardCode : Code := ifzCode Code.succ (Code.const 0)

/-- **Guard pass (`n ≤ k`, `sel = 0`): `some result` (proved).** -/
theorem eval_guardCode_le (result : ℕ) :
    guardCode.eval (Nat.pair result 0) = Part.some (result + 1) := by
  rw [guardCode, eval_ifzCode_zero]; simp [Code.eval]

/-- **Guard fail (`n > k`, `sel = t+1`): `none` (proved).** -/
theorem eval_guardCode_gt (result t : ℕ) :
    guardCode.eval (Nat.pair result (t + 1)) = Part.some 0 := by
  rw [guardCode, eval_ifzCode_pos _ _ _ (by simp [Code.eval]) (by simp [Code.eval])]; simp [Code.eval]

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_guardCode_le
