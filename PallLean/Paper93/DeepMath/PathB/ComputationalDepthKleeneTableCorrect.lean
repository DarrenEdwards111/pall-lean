import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneBuildTableCtx
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookup

/-!
# Kleene interpreter project — the correctness-chain core (PROVED)

The crux and the part I flagged as the genuine risk: proving the course-of-values table is correct.  It
**closes cleanly** once the table is described by a *recursive* list `tableList spec N = [spec(N-1),…,spec 0]`
(rather than reverse-index `ofFn` arithmetic) — the chain just *propagates* a per-cell `spec`, and the
reverse-index complexity is localized to a single lookup lemma.

  `tableList spec N` — the intended table contents at rank `N` (front = highest rank).
  `buildTableCtx_correct` — if the body computes `spec N` whenever fed the correct table
    `encodeList (tableList spec N)`, then `buildTableCtx body` produces exactly that table at every `N`.
    (Strong induction on `N`; the inductive step is `cons`.)
  `tableList_lookup` — the reverse-index lemma the handlers use: `((tableList spec N).drop (N-1-r)).headD 0
    = spec r` for `r < N` (so `lookupCode` at offset `N-1-r` returns the rank-`r` cell `spec r`).

So the table-correctness is settled: the remaining work (the recursive handlers) is exactly to discharge the
body's hypothesis `hbody` — i.e. compute `spec N` (encoded `evaln`) from the table, reading sub-results via
`tableList_lookup` and combining per `evalnStep`.  No reverse-index/induction snag in the chain itself.

## What is proved (clean axioms, no `sorry`)

* `tableList`, `buildTableCtx_correct`, `tableList_lookup`.

## Honest scope

The correctness-chain core (de-risked).  The recursive handlers (discharging `hbody`), the per-cell body
assembly, `spec = encoded evaln` via `evalnStep_correct`, the interpreter, and the runtime remain.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)

/-- The intended table contents at rank `N`: `[spec(N-1), …, spec 0]`. -/
def tableList (spec : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | N + 1 => spec N :: tableList spec N

/-- **Correctness-chain core (proved): a body that computes `spec N` from the correct table yields the
correct table at every `N`.** -/
theorem buildTableCtx_correct (body : Code) (ctx : ℕ) (spec : ℕ → ℕ)
    (hbody : ∀ N, body.eval (Nat.pair ctx (Nat.pair N (encodeList (tableList spec N))))
      = Part.some (spec N)) :
    ∀ N, (buildTableCtx body).eval (Nat.pair ctx N) = Part.some (encodeList (tableList spec N)) := by
  intro N
  induction N with
  | zero => rw [eval_buildTableCtx_zero]; rfl
  | succ N ih =>
    rw [eval_buildTableCtx_succ, ih]
    simp only [Part.bind_eq_bind, Part.bind_some, hbody N]
    rfl

/-- **Reverse-index lookup (proved): the rank-`r` cell sits at offset `N-1-r`.** -/
theorem tableList_lookup (spec : ℕ → ℕ) :
    ∀ N r, r < N → ((tableList spec N).drop (N - 1 - r)).headD 0 = spec r := by
  intro N
  induction N with
  | zero => intro r hr; omega
  | succ N ih =>
    intro r hr
    rcases Nat.lt_or_ge r N with h | h
    · show ((spec N :: tableList spec N).drop (N + 1 - 1 - r)).headD 0 = spec r
      rw [show N + 1 - 1 - r = (N - 1 - r) + 1 from by omega, List.drop_succ_cons]
      exact ih r h
    · have hrN : r = N := by omega
      subst hrN
      show ((spec r :: tableList spec r).drop (r + 1 - 1 - r)).headD 0 = spec r
      rw [show r + 1 - 1 - r = 0 from by omega]; rfl

/-!
**Correctness-chain core proved (de-risked).**  Table-correctness propagates through `buildTableCtx`
(`buildTableCtx_correct`) and the reverse-index lookup returns the right cell (`tableList_lookup`).  The
recursive handlers (discharging `hbody`), the per-cell body, `spec = encoded evaln`, the interpreter, and the
runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.buildTableCtx_correct
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.tableList_lookup
