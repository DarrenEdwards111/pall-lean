import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneList

/-!
# Kleene interpreter project — list-as-number ops, piece 2: lookup (PROVED)

The central table operation: index into the encoded list, connected to Lean `List` operations so the
course-of-values can use it cleanly.  `lookup L i = head (tail^i L)`.

  `encodeList : List ℕ → ℕ` — the list encoding (`nil = 0`, `cons x xs = pair x xs + 1`).
  `eval_headCode_list` / `eval_tailCode_list` — `head`/`tail` against `List.headD`/`List.tail`.
  `iterTailCode` — iterate `tail` `i` times; `eval_iterTail` — `= encodeList (L.drop i)`.
  `lookupCode` — `comp headCode iterTailCode`; `eval_lookupCode` — `= (L.drop i).headD 0` (the `i`-th element,
    default `0`).

So table lookup is a concrete `Code`, correct against Lean `List` indexing — the course-of-values reads
sub-results from the table this way.

## What is proved (clean axioms, no `sorry`)

* `encodeList`, `eval_headCode_list`, `eval_tailCode_list`, `iterTailCode`, `eval_iterTail`, `lookupCode`,
  `eval_lookupCode`.

## Honest scope

List ops `head`/`tail`/`lookup` are done.  `length`/`append` (table extension), the course-of-values
combinator, the interpreter assembly, and the runtime bound remain.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneList

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneUCode (prec_eval_succ)

/-- List encoding: `nil = 0`, `cons x xs = pair x xs + 1`. -/
def encodeList : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.pair x (encodeList xs) + 1

theorem eval_headCode_nil : headCode.eval 0 = Part.some 0 := by
  have hp : (Code.pair (Code.const 0) Code.id).eval 0 = Part.some (Nat.pair 0 0) := by
    simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some]
  have hc : headCode.eval 0 = ((Code.pair (Code.const 0) Code.id).eval 0).bind
      (Code.prec (Code.const 0) (Code.comp Code.left (Code.comp Code.left Code.right))).eval := rfl
  rw [hc, hp, Part.bind_some, eval_prec_head]; simp

theorem eval_tailCode_nil : tailCode.eval 0 = Part.some 0 := by
  have hp : (Code.pair (Code.const 0) Code.id).eval 0 = Part.some (Nat.pair 0 0) := by
    simp [Code.eval, Part.map_some, Seq.seq, Part.bind_some]
  have hc : tailCode.eval 0 = ((Code.pair (Code.const 0) Code.id).eval 0).bind
      (Code.prec (Code.const 0) (Code.comp Code.right (Code.comp Code.left Code.right))).eval := rfl
  rw [hc, hp, Part.bind_some, eval_prec_tail]; simp

/-- **`headCode` against `List.headD` (proved).** -/
theorem eval_headCode_list (M : List ℕ) : headCode.eval (encodeList M) = Part.some (M.headD 0) := by
  cases M with
  | nil => simpa using eval_headCode_nil
  | cons x xs => simpa [encodeList] using eval_headCode_cons x (encodeList xs)

/-- **`tailCode` against `List.tail` (proved).** -/
theorem eval_tailCode_list (M : List ℕ) :
    tailCode.eval (encodeList M) = Part.some (encodeList M.tail) := by
  cases M with
  | nil => simpa [encodeList] using eval_tailCode_nil
  | cons x xs => simpa [encodeList] using eval_tailCode_cons x (encodeList xs)

/-- Iterate `tail` `i` times, as a `Code`. -/
def iterTailCode : Code := Code.prec Code.id (Code.comp tailCode (Code.comp Code.right Code.right))

/-- **`iterTailCode` is `List.drop` (proved).** -/
theorem eval_iterTail (L : List ℕ) (i : ℕ) :
    iterTailCode.eval (Nat.pair (encodeList L) i) = Part.some (encodeList (L.drop i)) := by
  induction i with
  | zero => simp [iterTailCode, Code.eval]
  | succ k ih =>
    rw [show iterTailCode.eval (Nat.pair (encodeList L) (k + 1))
          = ((iterTailCode.eval (Nat.pair (encodeList L) k)) >>= fun prev =>
              (Code.comp tailCode (Code.comp Code.right Code.right)).eval
                (Nat.pair (encodeList L) (Nat.pair k prev)))
        from prec_eval_succ _ _ _ _, ih]
    simp only [Part.bind_eq_bind, Part.bind_some]
    have e : (Code.comp tailCode (Code.comp Code.right Code.right)).eval
          (Nat.pair (encodeList L) (Nat.pair k (encodeList (L.drop k))))
        = ((Code.comp Code.right Code.right).eval
            (Nat.pair (encodeList L) (Nat.pair k (encodeList (L.drop k))))).bind tailCode.eval := rfl
    rw [e, show ((Code.comp Code.right Code.right).eval
          (Nat.pair (encodeList L) (Nat.pair k (encodeList (L.drop k))))) = Part.some (encodeList (L.drop k))
        from by simp [Code.eval, Nat.unpair_pair], Part.bind_some, eval_tailCode_list, List.tail_drop]

/-- Table lookup as a `Code`: the `i`-th element. -/
def lookupCode : Code := Code.comp headCode iterTailCode

/-- **`lookupCode` is list indexing (proved): the `i`-th element, default `0`.** -/
theorem eval_lookupCode (L : List ℕ) (i : ℕ) :
    lookupCode.eval (Nat.pair (encodeList L) i) = Part.some ((L.drop i).headD 0) := by
  have hc : lookupCode.eval (Nat.pair (encodeList L) i)
      = (iterTailCode.eval (Nat.pair (encodeList L) i)).bind headCode.eval := rfl
  rw [hc, eval_iterTail, Part.bind_some, eval_headCode_list]

/-!
**List lookup proved.**  Table indexing is a concrete `Code` correct against Lean `List` operations — how the
course-of-values reads sub-results.  `length`/`append`, the course-of-values combinator, the interpreter, and
the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneList

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneList.eval_lookupCode
