import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneArith

/-!
# Kleene interpreter project — step 5: a general `prec`-step lemma + bounded subtraction (PROVED)

Two reusable control-layer pieces:

  `prec_eval_succ` — the general `prec` recursion-step: `(prec cf cg).eval (pair a (k+1)) =
    (prec cf cg).eval (pair a k) >>= fun prev => cg.eval (pair a (pair k prev))`.  This cleanly exposes the
    `prec`-recursion (the source of the contamination) for any `prec` code.
  `subCode := prec id (comp predCode (comp right right))` — bounded subtraction by iterating `predCode`:
    `subCode.eval (pair a b) = a - b`.

`subCode` iterates `predCode` `b` times over `a` (the `comp right right` body pulls the running value and
applies `predCode`).  This is the second arithmetic primitive; with `subCode` and the conditional, the
dispatch's tag-equality tests (`sub` then zero-test) are within reach.

## What is proved (clean axioms, no `sorry`)

* `prec_eval_succ` — the general `prec`-step lemma.
* `subCode`, `eval_subCode` — bounded subtraction as a concrete `Code`.

## Honest scope

The general `prec`-step lemma + bounded subtraction.  Equality test, the 8-way dispatch, and the double
recursion remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- **General `prec` recursion-step (proved).** -/
theorem prec_eval_succ (cf cg : Code) (a k : ℕ) :
    (Code.prec cf cg).eval (Nat.pair a (k + 1))
      = ((Code.prec cf cg).eval (Nat.pair a k)) >>= fun prev =>
          cg.eval (Nat.pair a (Nat.pair k prev)) := by
  simp only [Code.eval, Nat.unpaired, Nat.unpair_pair, Nat.rec_add_one]

/-- Bounded subtraction as a concrete `Code`: iterate `predCode` `b` times. -/
def subCode : Code := Code.prec Code.id (Code.comp predCode (Code.comp Code.right Code.right))

/-- **Bounded subtraction correctness (proved): `subCode.eval (pair a b) = a - b`.** -/
theorem eval_subCode (a b : ℕ) : subCode.eval (Nat.pair a b) = Part.some (a - b) := by
  induction b with
  | zero => simp [subCode, Code.eval]
  | succ k ih =>
    rw [show subCode.eval (Nat.pair a (k + 1))
          = ((subCode.eval (Nat.pair a k)) >>= fun prev =>
              (Code.comp predCode (Code.comp Code.right Code.right)).eval (Nat.pair a (Nat.pair k prev)))
        from prec_eval_succ _ _ _ _, ih]
    simp only [Part.bind_eq_bind, Part.bind_some]
    rw [show (Code.comp predCode (Code.comp Code.right Code.right)).eval (Nat.pair a (Nat.pair k (a - k)))
          = Part.some (Nat.pred (a - k)) from by simp [Code.eval, Nat.unpair_pair, eval_predCode]]
    congr 1

/-!
**Bounded subtraction proved.**  `prec_eval_succ` is the reusable `prec`-recursion-step, and `subCode`
computes truncated subtraction as a concrete `Code`.  Equality test, the 8-way dispatch, and the double
recursion remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_subCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.prec_eval_succ
