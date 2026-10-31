import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneGuard
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDecode

/-!
# Kleene interpreter project — base constructor handlers (PROVED)

The per-cell body dispatches on the simulated code's constructor; the **base** constructors
(`zero`/`succ`/`left`/`right`) need no table lookups — each computes its `evalnStep` value from `(k, n)` and
applies `guardCode` (Option-encoded, `none = 0`, `some v = v+1`).  Input `(pair k n)`; `sel = n - k`
(zero iff `n ≤ k`).

  `guard_apply` — `comp guardCode (pair resultCode (sel = n-k))` returns `if n ≤ k then res+1 else 0`.
  `zeroHandler`/`succHandler`/`leftHandler`/`rightHandler` + their `eval` lemmas.

## What is proved (clean axioms, no `sorry`)

* `guard_apply`, the four base handlers + correctness (Option-encoded `evalnStep` for base codes).

## Honest scope

Base handlers.  The recursive handlers (`pair`/`comp`/`prec`/`rfind'`, with `cfgRankCode` + `lookupCode`),
the assembled per-cell body, the correctness chain, the interpreter, and the runtime remain.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Apply `guardCode` to a result computed by `resultCode`, with `sel = n - k`. -/
theorem guard_apply (resultCode : Code) (k n res : ℕ)
    (hres : resultCode.eval (Nat.pair k n) = Part.some res) :
    (Code.comp guardCode (Code.pair resultCode
      (Code.comp subCode (Code.pair Code.right Code.left)))).eval (Nat.pair k n)
      = Part.some (if n ≤ k then res + 1 else 0) := by
  have hsel : (Code.comp subCode (Code.pair Code.right Code.left)).eval (Nat.pair k n)
      = Part.some (n - k) := by
    rw [comp_pair_eval _ _ _ _ _ _
      (show (Code.right : Code).eval (Nat.pair k n) = Part.some n from by simp [Code.eval, Nat.unpair_pair])
      (show (Code.left : Code).eval (Nat.pair k n) = Part.some k from by simp [Code.eval, Nat.unpair_pair]),
      eval_subCode]
  rw [comp_pair_eval _ _ _ _ _ _ hres hsel]
  by_cases h : n ≤ k
  · rw [if_pos h, show n - k = 0 from by omega, eval_guardCode_le]
  · obtain ⟨t, ht⟩ : ∃ t, n - k = t + 1 := ⟨n - k - 1, by omega⟩
    rw [if_neg h, ht, eval_guardCode_gt]

/-- `zero` handler. -/
def zeroHandler : Code :=
  Code.comp guardCode (Code.pair (Code.const 0) (Code.comp subCode (Code.pair Code.right Code.left)))
/-- `succ` handler. -/
def succHandler : Code :=
  Code.comp guardCode (Code.pair (Code.comp Code.succ Code.right)
    (Code.comp subCode (Code.pair Code.right Code.left)))
/-- `left` handler. -/
def leftHandler : Code :=
  Code.comp guardCode (Code.pair (Code.comp Code.left Code.right)
    (Code.comp subCode (Code.pair Code.right Code.left)))
/-- `right` handler. -/
def rightHandler : Code :=
  Code.comp guardCode (Code.pair (Code.comp Code.right Code.right)
    (Code.comp subCode (Code.pair Code.right Code.left)))

theorem eval_zeroHandler (k n : ℕ) :
    zeroHandler.eval (Nat.pair k n) = Part.some (if n ≤ k then 1 else 0) := by
  have := guard_apply (Code.const 0) k n 0 (by simp [Code.eval]); simpa [zeroHandler] using this

theorem eval_succHandler (k n : ℕ) :
    succHandler.eval (Nat.pair k n) = Part.some (if n ≤ k then (n + 1) + 1 else 0) := by
  have := guard_apply (Code.comp Code.succ Code.right) k n (n + 1)
    (by rw [comp_eval _ _ _ _ (show (Code.right : Code).eval (Nat.pair k n) = Part.some n
      from by simp [Code.eval, Nat.unpair_pair])]; simp [Code.eval])
  simpa [succHandler] using this

theorem eval_leftHandler (k n : ℕ) :
    leftHandler.eval (Nat.pair k n) = Part.some (if n ≤ k then (Nat.unpair n).1 + 1 else 0) := by
  have := guard_apply (Code.comp Code.left Code.right) k n (Nat.unpair n).1
    (by rw [comp_eval _ _ _ _ (show (Code.right : Code).eval (Nat.pair k n) = Part.some n
      from by simp [Code.eval, Nat.unpair_pair])]; simp [Code.eval])
  simpa [leftHandler] using this

theorem eval_rightHandler (k n : ℕ) :
    rightHandler.eval (Nat.pair k n) = Part.some (if n ≤ k then (Nat.unpair n).2 + 1 else 0) := by
  have := guard_apply (Code.comp Code.right Code.right) k n (Nat.unpair n).2
    (by rw [comp_eval _ _ _ _ (show (Code.right : Code).eval (Nat.pair k n) = Part.some n
      from by simp [Code.eval, Nat.unpair_pair])]; simp [Code.eval])
  simpa [rightHandler] using this

/-!
**Base handlers proved.**  Option-encoded `evalnStep` for `zero`/`succ`/`left`/`right`.  The recursive
handlers, the per-cell body, the correctness chain, the interpreter, and the runtime remain.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_zeroHandler
