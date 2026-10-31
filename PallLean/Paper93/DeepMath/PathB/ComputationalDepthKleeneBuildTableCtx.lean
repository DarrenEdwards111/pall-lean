import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneBuildTable

/-!
# Kleene interpreter project — context-threading table builder (PROVED)

The per-cell body needs `(E, B)` (for rank decode and sub-rank computation), but `buildTable`'s body only
sees `(rank, table)`.  `buildTableCtx` threads a **context** `ctx` (which will be `pair E B`): applied to
`pair ctx N`, the `prec` "a"-parameter preserves `ctx`, so the body receives the full
`pair ctx (pair rank table)`.

  `buildTableCtx body` — `T₀ = nil`; `T_{N+1} = cons (body (ctx, N, T_N)) T_N`, with `ctx` available to `body`.
  `eval_buildTableCtx_zero` / `eval_buildTableCtx_succ` — the table-extension recurrence (ctx-threaded).

## What is proved (clean axioms, no `sorry`)

* `buildTableCtx`, `cg_body_ctx`, `eval_buildTableCtx_zero`, `eval_buildTableCtx_succ`.

## Honest scope

The ctx-threading builder.  The recursive handlers, the per-cell body, the correctness chain, the
interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec

/-- Context-threading course-of-values builder: `body` receives `pair ctx (pair rank table)`. -/
def buildTableCtx (body : Code) : Code :=
  Code.prec (Code.const 0) (Code.comp Code.succ (Code.pair body (Code.comp Code.right Code.right)))

theorem cg_body_ctx (body : Code) (ctx m prev : ℕ) :
    (Code.comp Code.succ (Code.pair body (Code.comp Code.right Code.right))).eval
        (Nat.pair ctx (Nat.pair m prev))
      = (body.eval (Nat.pair ctx (Nat.pair m prev))) >>= fun v => Part.some (Nat.pair v prev + 1) := by
  simp [Code.eval, Seq.seq, Part.map_eq_map, Part.bind_some, Nat.unpair_pair, Part.bind_assoc]

theorem eval_buildTableCtx_zero (body : Code) (ctx : ℕ) :
    (buildTableCtx body).eval (Nat.pair ctx 0) = Part.some 0 := by simp [buildTableCtx, Code.eval]

theorem eval_buildTableCtx_succ (body : Code) (ctx N : ℕ) :
    (buildTableCtx body).eval (Nat.pair ctx (N + 1))
      = ((buildTableCtx body).eval (Nat.pair ctx N)) >>= fun T =>
          (body.eval (Nat.pair ctx (Nat.pair N T))) >>= fun v => Part.some (Nat.pair v T + 1) := by
  rw [show (buildTableCtx body).eval (Nat.pair ctx (N + 1))
        = ((buildTableCtx body).eval (Nat.pair ctx N)) >>= fun prev =>
            (Code.comp Code.succ (Code.pair body (Code.comp Code.right Code.right))).eval
              (Nat.pair ctx (Nat.pair N prev))
      from prec_eval_succ _ _ _ _]
  congr 1; funext prev; exact cg_body_ctx body ctx N prev

/-!
**Context-threading builder proved.**  `body` now receives `pair ctx (pair rank table)`, giving it `(E, B)`
for decode and sub-ranks.  The recursive handlers, the per-cell body, the correctness chain, the interpreter,
and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_buildTableCtx_succ
