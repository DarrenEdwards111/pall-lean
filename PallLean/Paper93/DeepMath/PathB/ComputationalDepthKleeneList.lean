import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSub

/-!
# Kleene interpreter project — list-as-number ops, piece 1: head/tail (PROVED)

The poly-`runtimeOf` interpreter is the **structural** simulator realized by course-of-values over
`encode c` (a `prec`-built table; its own `runtimeOf` is poly since `prec` is linear in the poly-size table,
and `evaln`-fuel is depth-like — `runtimeOf_compPow_le`).  Course-of-values needs a **table** = list-as-number,
and Mathlib provides list ops only at the `Primrec` level (`Primrec.list_concat`), not as explicit `Code`s.
So we build a small list-ops `Code` library from the raw calculus (as we did for arithmetic).

Encoding: `nil = 0`, `cons x xs = Nat.pair x xs + 1` (nonempty `≠ 0`).

  `headCode` / `tailCode` — destructors as concrete `Code`s.
  `eval_headCode_cons` / `eval_tailCode_cons` — `head (cons x xs) = x`, `tail (cons x xs) = xs`.

## What is proved (clean axioms, no `sorry`)

* `headCode`, `tailCode`, `eval_headCode_cons`, `eval_tailCode_cons`.

## Honest scope

First bricks of the list-ops `Code` library (head/tail).  The full library (`lookup`, `length`, `append`),
the course-of-values combinator built on it, the interpreter assembly, and the (now-straightforward) runtime
bound remain — a sizeable multi-brick grind, with no Mathlib help.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneList

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneUCode (prec_eval_succ)

/-- List head as a `Code` (encoding `cons x xs = pair x xs + 1`, `nil = 0`). -/
def headCode : Code :=
  Code.comp (Code.prec (Code.const 0) (Code.comp Code.left (Code.comp Code.left Code.right)))
    (Code.pair (Code.const 0) Code.id)

/-- List tail as a `Code`. -/
def tailCode : Code :=
  Code.comp (Code.prec (Code.const 0) (Code.comp Code.right (Code.comp Code.left Code.right)))
    (Code.pair (Code.const 0) Code.id)

/-- Core for `headCode`. -/
theorem eval_prec_head (a L : ℕ) :
    (Code.prec (Code.const 0) (Code.comp Code.left (Code.comp Code.left Code.right))).eval (Nat.pair a L)
      = Part.some (if L = 0 then 0 else (Nat.unpair (L - 1)).1) := by
  induction L with
  | zero => simp [Code.eval]
  | succ k ih =>
    rw [prec_eval_succ, ih]; simp only [Part.bind_eq_bind, Part.bind_some]
    simp [Code.eval, Nat.unpair_pair]

/-- Core for `tailCode`. -/
theorem eval_prec_tail (a L : ℕ) :
    (Code.prec (Code.const 0) (Code.comp Code.right (Code.comp Code.left Code.right))).eval (Nat.pair a L)
      = Part.some (if L = 0 then 0 else (Nat.unpair (L - 1)).2) := by
  induction L with
  | zero => simp [Code.eval]
  | succ k ih =>
    rw [prec_eval_succ, ih]; simp only [Part.bind_eq_bind, Part.bind_some]
    simp [Code.eval, Nat.unpair_pair]

/-- **`head (cons x xs) = x` (proved).** -/
theorem eval_headCode_cons (x xs : ℕ) : headCode.eval (Nat.pair x xs + 1) = Part.some x := by
  have hp : (Code.pair (Code.const 0) Code.id).eval (Nat.pair x xs + 1)
      = Part.some (Nat.pair 0 (Nat.pair x xs + 1)) := by
    simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some]
  have hc : headCode.eval (Nat.pair x xs + 1)
      = ((Code.pair (Code.const 0) Code.id).eval (Nat.pair x xs + 1)).bind
          (Code.prec (Code.const 0) (Code.comp Code.left (Code.comp Code.left Code.right))).eval := rfl
  rw [hc, hp, Part.bind_some, eval_prec_head]
  simp [Nat.unpair_pair]

/-- **`tail (cons x xs) = xs` (proved).** -/
theorem eval_tailCode_cons (x xs : ℕ) : tailCode.eval (Nat.pair x xs + 1) = Part.some xs := by
  have hp : (Code.pair (Code.const 0) Code.id).eval (Nat.pair x xs + 1)
      = Part.some (Nat.pair 0 (Nat.pair x xs + 1)) := by
    simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some]
  have hc : tailCode.eval (Nat.pair x xs + 1)
      = ((Code.pair (Code.const 0) Code.id).eval (Nat.pair x xs + 1)).bind
          (Code.prec (Code.const 0) (Code.comp Code.right (Code.comp Code.left Code.right))).eval := rfl
  rw [hc, hp, Part.bind_some, eval_prec_tail]
  simp [Nat.unpair_pair]

/-!
**List head/tail proved.**  First bricks of the list-as-number `Code` library for the course-of-values table.
`lookup`/`length`/`append`, the course-of-values combinator, the interpreter, and the runtime bound remain.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneList

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneList.eval_headCode_cons
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneList.eval_tailCode_cons
