import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookup

/-!
# Kleene interpreter project — the course-of-values table builder (PROVED)

The keystone of the explicit structural interpreter: a combinator `buildTable body` that builds the
course-of-values table by `prec`, consing each new cell `body (rank, table_so_far)` onto the front.  With the
table built (and `lookupCode` to read earlier cells via reverse-indexing), the structural recursion on
`encode c` is realized in the `Code` calculus.

  `buildTable body` — `T₀ = nil`; `T_{N+1} = cons (body (N, T_N)) T_N` (reversed table).
  `eval_buildTable_zero` — `(buildTable body).eval 0 = nil`.
  `eval_buildTable_succ` — `(buildTable body).eval (N+1) = T_N >>= fun T => body (N, T) >>= fun v => cons v T`,
    the table-extension recurrence.

The per-cell `body` is later instantiated with `evalnStep` realized via `mkDispatch` + `lookupCode`, giving
the structural interpreter; its `runtimeOf` is polynomial (the `prec` is linear in the poly-size table, and
`evaln`-fuel is depth-like).

## What is proved (clean axioms, no `sorry`)

* `buildTable`, `eval_buildTable_zero`, `eval_buildTable_succ`.

## Honest scope

The course-of-values table builder + its recurrence.  Connecting it to a Lean course-of-values spec,
instantiating `body = evalnStep`-via-dispatch, the interpreter assembly, and the runtime bound remain.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneList

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneUCode (prec_eval_succ)

/-- The per-cell `cons (body (rank, T)) T` step, simplified (proved). -/
theorem cg_body (body : Code) (a M prev : ℕ) :
    (Code.comp Code.succ
        (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right))).eval
        (Nat.pair a (Nat.pair M prev))
      = (body.eval (Nat.pair M prev)) >>= fun v => Part.some (Nat.pair v prev + 1) := by
  simp [Code.eval, Seq.seq, Part.map_eq_map, Part.bind_some, Nat.unpair_pair, Part.bind_assoc]

/-- Course-of-values table builder: `T₀ = nil`; `T_{N+1} = cons (body (N, T_N)) T_N`. -/
def buildTable (body : Code) : Code :=
  Code.comp
    (Code.prec (Code.const 0)
      (Code.comp Code.succ (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right))))
    (Code.pair (Code.const 0) Code.id)

/-- **Empty table (proved).** -/
theorem eval_buildTable_zero (body : Code) : (buildTable body).eval 0 = Part.some 0 := by
  have hp : (Code.pair (Code.const 0) Code.id).eval 0 = Part.some (Nat.pair 0 0) := by
    simp [Code.eval, Part.map_eq_map, Seq.seq, Part.bind_some]
  have hc : (buildTable body).eval 0 = ((Code.pair (Code.const 0) Code.id).eval 0).bind
      (Code.prec (Code.const 0)
        (Code.comp Code.succ (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right)))).eval :=
    rfl
  rw [hc, hp, Part.bind_some]; simp [Code.eval]

/-- **Table-extension recurrence (proved).** -/
theorem eval_buildTable_succ (body : Code) (N : ℕ) :
    (buildTable body).eval (N + 1)
      = ((buildTable body).eval N) >>= fun T =>
          (body.eval (Nat.pair N T)) >>= fun v => Part.some (Nat.pair v T + 1) := by
  have inner : ∀ a M,
      (Code.prec (Code.const 0)
          (Code.comp Code.succ
            (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right)))).eval
          (Nat.pair a (M + 1))
        = ((Code.prec (Code.const 0)
            (Code.comp Code.succ
              (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right)))).eval
            (Nat.pair a M)) >>= fun prev =>
            (body.eval (Nat.pair M prev)) >>= fun v => Part.some (Nat.pair v prev + 1) := by
    intro a M; rw [prec_eval_succ]; congr 1; funext prev; exact cg_body body a M prev
  have hcN : (buildTable body).eval (N + 1)
      = (Code.prec (Code.const 0)
          (Code.comp Code.succ
            (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right)))).eval
          (Nat.pair 0 (N + 1)) := by
    have hp : (Code.pair (Code.const 0) Code.id).eval (N + 1) = Part.some (Nat.pair 0 (N + 1)) := by
      simp [Code.eval, Part.map_eq_map, Seq.seq, Part.bind_some]
    have hc : (buildTable body).eval (N + 1) = ((Code.pair (Code.const 0) Code.id).eval (N + 1)).bind
        (Code.prec (Code.const 0)
          (Code.comp Code.succ
            (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right)))).eval := rfl
    rw [hc, hp, Part.bind_some]
  have hcNm : (buildTable body).eval N
      = (Code.prec (Code.const 0)
          (Code.comp Code.succ
            (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right)))).eval
          (Nat.pair 0 N) := by
    have hp : (Code.pair (Code.const 0) Code.id).eval N = Part.some (Nat.pair 0 N) := by
      simp [Code.eval, Part.map_eq_map, Seq.seq, Part.bind_some]
    have hc : (buildTable body).eval N = ((Code.pair (Code.const 0) Code.id).eval N).bind
        (Code.prec (Code.const 0)
          (Code.comp Code.succ
            (Code.pair (Code.comp body Code.right) (Code.comp Code.right Code.right)))).eval := rfl
    rw [hc, hp, Part.bind_some]
  rw [hcN, inner, ← hcNm]

/-!
**Table builder proved.**  `buildTable` realizes the course-of-values fill (`eval_buildTable_succ`).  With
`lookupCode`, the structural recursion on `encode c` becomes a `Code`.  Connecting to a Lean spec,
instantiating `body`, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneList

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneList.eval_buildTable_succ
