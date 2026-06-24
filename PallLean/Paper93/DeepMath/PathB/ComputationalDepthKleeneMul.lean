import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneEq

/-!
# Kleene interpreter project — multiplication Code (PROVED)

The per-cell body of the course-of-values interpreter computes sub-config ranks `cfgRank E B k ec n =
(k·(E+1)+ec)·(B+1)+n`, which needs multiplication.  Mathlib has no arithmetic `Code`s, so we build it (like
`add`/`sub`) from the raw calculus: `mul a b = a·b` by iterating `addCode`.

  `mulCode` — `mulCode.eval (pair a b) = a * b`.

## What is proved (clean axioms, no `sorry`)

* `mulCode`, `eval_mulCode`.

## Honest scope

Multiplication, for the rank arithmetic.  `div`/`mod` (rank decode), the per-cell body, the correctness
chain, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Multiplication as a concrete `Code` (iterate `addCode`). -/
def mulCode : Code :=
  Code.prec (Code.const 0) (Code.comp addCode (Code.pair (Code.comp Code.right Code.right) Code.left))

theorem mul_body (a k prev : ℕ) :
    (Code.comp addCode (Code.pair (Code.comp Code.right Code.right) Code.left)).eval
        (Nat.pair a (Nat.pair k prev)) = Part.some (prev + a) := by
  have e : (Code.comp addCode (Code.pair (Code.comp Code.right Code.right) Code.left)).eval
        (Nat.pair a (Nat.pair k prev))
      = ((Code.pair (Code.comp Code.right Code.right) Code.left).eval
          (Nat.pair a (Nat.pair k prev))).bind addCode.eval := rfl
  rw [e, show ((Code.pair (Code.comp Code.right Code.right) Code.left).eval
        (Nat.pair a (Nat.pair k prev))) = Part.some (Nat.pair prev a)
      from by simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some, Nat.unpair_pair],
    Part.bind_some, eval_addCode]

/-- **Multiplication correctness (proved): `mulCode.eval (pair a b) = a * b`.** -/
theorem eval_mulCode (a b : ℕ) : mulCode.eval (Nat.pair a b) = Part.some (a * b) := by
  induction b with
  | zero => simp [mulCode, Code.eval]
  | succ k ih =>
    rw [show mulCode.eval (Nat.pair a (k + 1))
          = ((mulCode.eval (Nat.pair a k)) >>= fun prev =>
              (Code.comp addCode (Code.pair (Code.comp Code.right Code.right) Code.left)).eval
                (Nat.pair a (Nat.pair k prev)))
        from prec_eval_succ _ _ _ _, ih]
    simp only [Part.bind_eq_bind, Part.bind_some]
    rw [mul_body]

/-!
**Multiplication proved.**  `mulCode` computes `a * b` — for the rank arithmetic.  `div`/`mod`, the per-cell
body, the correctness chain, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_mulCode
