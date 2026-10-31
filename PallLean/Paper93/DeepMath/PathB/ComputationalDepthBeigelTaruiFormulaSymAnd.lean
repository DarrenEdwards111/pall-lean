import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiCompose
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiToda

/-!
# Beigel–Tarui, rung 12: a concrete formula reduces to `SYM∘AND`

The whole Beigel–Tarui fold pipeline (rungs 6, 9, 10, 11) now instantiates on a concrete circuit — an `AND`/`OR`/`NOT`
formula.  Composing rung 6 (`eval_arithP`: the formula's polynomial computes it) with rung 11 (`eval_eq_repCount_cast`:
the polynomial folds to a symmetric count), **every formula's Boolean value equals a single symmetric function of the
count of satisfied replicated ANDs** — the `SYM∘AND` normal form, exactly.

  `formula_eq_symAnd` — **PROVED, the reduction**: over `F_p`, `embed(f.eval x) = ↑(repCount (arithP f) x)` — the
        formula's value is `Nat.cast` of a single count of satisfied replicated ANDs (the `SYM∘AND` form).
  `formula_iff_symAnd` — **PROVED**: the formula accepts iff that count is `1` in `F_p` (`f.eval x = true ↔
        (repCount … : ZMod p) = 1`) — the `SYM` top read off as acceptance.
  `formula_symAnd_count_le` — **PROVED**: the AND-count is `≤ (p-1) · #monomials`.

So an `AND`/`OR`/`NOT` formula is *exactly* a `SYM∘AND`: a symmetric function of the count of `≤ (p-1)·#monomials`
ANDs, each an AND of `≤ 2^depth` variables (rung 6's degree bound).  This composes the pipeline
`formula → polynomial (rung 6) → weighted sum of ANDs (rung 9) → symmetric of one count (rungs 10–11)`.

## Honest scope

This is the **exact** `SYM∘AND` reduction of an `AND`/`OR`/`NOT` *formula*: exact arithmetisation (rung 6, degree
`≤ 2^depth`, so `#monomials` up to `2^{depth}`-ish — *exponential*, not quasipolynomial).  Two things remain for the full
Beigel–Tarui theorem: (i) **`MOD` gates** — `ACC⁰` is `AND`/`OR`/`NOT`/`MOD_m`; `BForm` has no `MOD`, so extending the
formula type and arithmetising `MOD_m` over `F_p` (the repo's `omegaFn`/`modField` route) is needed; and (ii) the
**quasipolynomial** AND count — the *low-degree* Razborov–Smolensky approximation (rungs 3–8) in place of exact
arithmetisation, giving `#monomials ≤ (n+1)^{polylog}` for depth-`d` circuits.  This file supplies the exact
formula-to-`SYM∘AND` reduction, feeding the repo's `symEval`/`gateCount` count layer and
`…NFrameFastSAT.symAndModel`.  Nothing here is the Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

open scoped Classical

variable {p n : ℕ} [Fact p.Prime]

/-- **The reduction (proved)**: over `F_p`, an `AND`/`OR`/`NOT` formula's Boolean value is `Nat.cast` of the count of
satisfied replicated ANDs of its arithmetisation — the `SYM∘AND` normal form.  Composes rung 6 (`eval_arithP`) with rung
11 (`eval_eq_repCount_cast`). -/
theorem formula_eq_symAnd (f : BForm n) (x : Fin n → Bool) :
    (embed (f.eval x) : ZMod p) = (repCount (arithP (R := ZMod p) f) x : ZMod p) := by
  rw [← eval_arithP (R := ZMod p), eval_eq_repCount_cast]

/-- **Acceptance read off the `SYM` top (proved)**: the formula accepts iff its replicated-AND count is `1` in `F_p`. -/
theorem formula_iff_symAnd (f : BForm n) (x : Fin n → Bool) :
    f.eval x = true ↔ (repCount (arithP (R := ZMod p) f) x : ZMod p) = 1 := by
  rw [← formula_eq_symAnd]
  cases h : f.eval x <;> simp [embed]

/-- **The AND-count is bounded (proved)**: `≤ (p-1) · #monomials`. -/
theorem formula_symAnd_count_le (f : BForm n) (x : Fin n → Bool) :
    repCount (arithP (R := ZMod p) f) x ≤ (p - 1) * (arithP (R := ZMod p) f).support.card :=
  repCount_le _ _

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.formula_eq_symAnd
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.formula_iff_symAnd
