import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneSub

/-!
# Kleene interpreter project — step 5: addition, zero-test, swap, equality (PROVED)

Completing the arithmetic library the dispatch's tag-matching needs.  All are concrete `Code`s (Mathlib has
none), proved correct.

  `addCode` — `addCode.eval (pair a b) = a + b` (iterate `succ`).
  `isZeroCode` — `isZeroCode.eval n = if n = 0 then 1 else 0`.
  `swapCode` — `swapCode.eval (pair a b) = pair b a`.
  `eqCode` — `eqCode.eval (pair a b) = if a = b then 1 else 0`, via the symmetric difference
    `isZero ((a-b) + (b-a))`.

`eqCode` is what the dispatch uses to match an extracted tag against each constructor value `0,…,7`.

## What is proved (clean axioms, no `sorry`)

* `addCode`/`eval_addCode`, `eval_prec_isZero`/`isZeroCode`/`eval_isZeroCode`, `swapCode`/`eval_swapCode`,
  `eqCode`/`eval_eqCode`.

## Honest scope

The arithmetic library (add/zero-test/swap/equality) is now complete.  The 8-way dispatch using these and
the double recursion remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Addition as a concrete `Code` (iterate `succ`). -/
def addCode : Code := Code.prec Code.id (Code.comp Code.succ (Code.comp Code.right Code.right))

/-- **Addition correctness (proved): `addCode.eval (pair a b) = a + b`.** -/
theorem eval_addCode (a b : ℕ) : addCode.eval (Nat.pair a b) = Part.some (a + b) := by
  induction b with
  | zero => simp [addCode, Code.eval]
  | succ k ih =>
    rw [show addCode.eval (Nat.pair a (k + 1))
          = ((addCode.eval (Nat.pair a k)) >>= fun prev =>
              (Code.comp Code.succ (Code.comp Code.right Code.right)).eval (Nat.pair a (Nat.pair k prev)))
        from prec_eval_succ _ _ _ _, ih]
    simp only [Part.bind_eq_bind, Part.bind_some]
    rw [show (Code.comp Code.succ (Code.comp Code.right Code.right)).eval (Nat.pair a (Nat.pair k (a + k)))
          = Part.some (a + k + 1) from by simp [Code.eval, Nat.unpair_pair]]
    congr 1

/-- **Core: `prec (const 1) (const 0)` is the zero-indicator on the second component (proved).** -/
theorem eval_prec_isZero (m : ℕ) :
    (Code.prec (Code.const 1) (Code.const 0)).eval (Nat.pair 0 m) = Part.some (if m = 0 then 1 else 0) := by
  induction m with
  | zero => simp [Code.eval]
  | succ k ih =>
    rw [prec_eval_succ, ih]; simp only [Part.bind_eq_bind, Part.bind_some]; simp [Code.eval]

/-- Zero-test as a concrete `Code`. -/
def isZeroCode : Code :=
  Code.comp (Code.prec (Code.const 1) (Code.const 0)) (Code.pair (Code.const 0) Code.id)

/-- **Zero-test correctness (proved): `isZeroCode.eval n = if n = 0 then 1 else 0`.** -/
theorem eval_isZeroCode (n : ℕ) : isZeroCode.eval n = Part.some (if n = 0 then 1 else 0) := by
  have hpair : (Code.pair (Code.const 0) Code.id).eval n = Part.some (Nat.pair 0 n) := by
    simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some]
  have hcomp : isZeroCode.eval n
      = ((Code.pair (Code.const 0) Code.id).eval n).bind (Code.prec (Code.const 1) (Code.const 0)).eval :=
    rfl
  rw [hcomp, hpair, Part.bind_some, eval_prec_isZero]

/-- Swap the two components of a pair, as a concrete `Code`. -/
def swapCode : Code := Code.pair Code.right Code.left

/-- **Swap correctness (proved): `swapCode.eval (pair a b) = pair b a`.** -/
theorem eval_swapCode (a b : ℕ) : swapCode.eval (Nat.pair a b) = Part.some (Nat.pair b a) := by
  simp [swapCode, Code.eval, Part.map_some, Seq.seq, Part.bind_some, Nat.unpair_pair]

/-- Equality test as a concrete `Code`: `isZero ((a-b) + (b-a))`. -/
def eqCode : Code :=
  Code.comp isZeroCode (Code.comp addCode (Code.pair subCode (Code.comp subCode swapCode)))

/-- **Equality test correctness (proved): `eqCode.eval (pair a b) = if a = b then 1 else 0`.** -/
theorem eval_eqCode (a b : ℕ) : eqCode.eval (Nat.pair a b) = Part.some (if a = b then 1 else 0) := by
  have h1 : (Code.comp subCode swapCode).eval (Nat.pair a b) = Part.some (b - a) := by
    have e : (Code.comp subCode swapCode).eval (Nat.pair a b)
        = (swapCode.eval (Nat.pair a b)).bind subCode.eval := rfl
    rw [e, eval_swapCode, Part.bind_some, eval_subCode]
  have hinner : (Code.pair subCode (Code.comp subCode swapCode)).eval (Nat.pair a b)
      = Part.some (Nat.pair (a - b) (b - a)) := by
    have e2 : (Code.pair subCode (Code.comp subCode swapCode)).eval (Nat.pair a b)
        = Nat.pair <$> subCode.eval (Nat.pair a b) <*> (Code.comp subCode swapCode).eval (Nat.pair a b) :=
      rfl
    rw [e2, eval_subCode, h1]
    simp [Part.map_some, Seq.seq, Part.bind_some]
  have hadd : (Code.comp addCode (Code.pair subCode (Code.comp subCode swapCode))).eval (Nat.pair a b)
      = Part.some ((a - b) + (b - a)) := by
    have e : (Code.comp addCode (Code.pair subCode (Code.comp subCode swapCode))).eval (Nat.pair a b)
        = ((Code.pair subCode (Code.comp subCode swapCode)).eval (Nat.pair a b)).bind addCode.eval := rfl
    rw [e, hinner, Part.bind_some, eval_addCode]
  have e : eqCode.eval (Nat.pair a b)
      = ((Code.comp addCode (Code.pair subCode (Code.comp subCode swapCode))).eval (Nat.pair a b)).bind
          isZeroCode.eval := rfl
  rw [e, hadd, Part.bind_some, eval_isZeroCode]
  rcases eq_or_ne a b with h | h
  · subst h; simp
  · have hne : (a - b) + (b - a) ≠ 0 := by omega
    rw [if_neg hne, if_neg h]

/-!
**Arithmetic library complete.**  `addCode`, `isZeroCode`, `swapCode`, `eqCode` are concrete `Code`s
(Mathlib provides none), proved correct.  `eqCode` matches an extracted tag against each constructor value.
The 8-way dispatch using these and the double recursion remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_eqCode
