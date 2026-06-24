import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneCond

/-!
# Kleene interpreter project — step 5 (control layer): arithmetic Codes (PROVED)

Mathlib provides **no** explicit arithmetic `Code`s (it works abstractly via `Computable`/`Primrec`), but
the dispatch's tag-selection needs them.  This file builds **predecessor** as a concrete `Code` from the raw
calculus — the first of the arithmetic library the multi-way dispatch requires.

  `predCode := comp (prec (const 0) (comp left right)) (pair (const 0) id)`.
  `eval_prec_pred` — the core: `(prec (const 0) (comp left right)).eval (pair a n) = pred n`.
  `eval_predCode` — `predCode.eval n = pred n`.

The construction pairs the input with a dummy, then `prec`-recurses: at `n = k+1` the body `comp left right`
extracts the recursion index `k = pred (k+1)` (ignoring the accumulated value).  As with the conditional,
`prec`'s recursion chain is involved, but the branches (`const 0`, `comp left right`) are total, so the
result is clean.

## What is proved (clean axioms, no `sorry`)

* `predCode`, `eval_prec_pred`, `eval_predCode` — predecessor as a concrete `Code`.

## Honest scope

One arithmetic primitive (`pred`), Mathlib-absent, built from the raw calculus.  The full arithmetic library
(bounded subtraction, equality test), the 8-way dispatch using them, and the double recursion remain the
indivisible core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- **Core: `prec (const 0) (comp left right)` computes the predecessor of the second component (proved).** -/
theorem eval_prec_pred (a n : ℕ) :
    (Code.prec (Code.const 0) (Code.comp Code.left Code.right)).eval (Nat.pair a n)
      = Part.some (Nat.pred n) := by
  induction n with
  | zero => simp [Code.eval]
  | succ k ih =>
    simp only [Code.eval, Nat.unpaired, Nat.unpair_pair, Nat.rec_add_one] at ih ⊢
    rw [ih]
    simp [Code.eval, Nat.unpair_pair]

/-- Predecessor as a concrete `Code`. -/
def predCode : Code :=
  Code.comp (Code.prec (Code.const 0) (Code.comp Code.left Code.right)) (Code.pair (Code.const 0) Code.id)

/-- **Predecessor code correctness (proved): `predCode.eval n = pred n`.** -/
theorem eval_predCode (n : ℕ) : predCode.eval n = Part.some (Nat.pred n) := by
  have hpair : (Code.pair (Code.const 0) Code.id).eval n = Part.some (Nat.pair 0 n) := by
    simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some]
  have hcomp : predCode.eval n
      = ((Code.pair (Code.const 0) Code.id).eval n).bind
          (Code.prec (Code.const 0) (Code.comp Code.left Code.right)).eval := rfl
  rw [hcomp, hpair, Part.bind_some, eval_prec_pred]

/-!
**Predecessor proved.**  `predCode` computes `pred` as a concrete `Code` — the first arithmetic primitive,
which Mathlib does not provide explicitly.  The rest of the arithmetic library, the 8-way dispatch, and the
double recursion remain the indivisible core.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_predCode
