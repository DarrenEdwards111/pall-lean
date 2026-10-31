import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneInterpCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneTableCorrect
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneLookup

/-!
# Kleene interpreter project — the memo-table blow-up no-go (PROVED, honest negative result)

The explicit universal interpreter `universalInterp` is **correct** (`universalInterp_correct`): the memoised
DP table it builds holds `encodeOpt (Code.evaln K c0.toCode n0)` at the top cell.  This file records the
honest reason that correctness does **not** translate into an *efficient* (polynomial-runtime) simulator
under the `Code.evaln` fuel measure used by the EffSim arc.

The memo table is carried as a **single `Nat`** via `encodeList` (nested `Nat.pair`).  Since `Nat.pair a b ≥
b²` (`pair_ge_sq`), each appended cell **squares** the encoding (`encodeList_tableList_succ_ge`), so the
table-as-`Nat` is bounded **below** by `2 ^ (number of cells)` (`encodeList_tableList_exp_lower`).  At the
diagonal target the cell count is `cfgRank E B K c0.enc n0` — itself polynomial in `(K, E, B)` — so the value
`buildTableCtx interpBody` produces is `≥ 2 ^ (cfgRank …)` (`diagonal_memo_table_exp`): **exponential** in the
config-space, hence super-polynomial.

Consequence (cf. the EffSim `Manifest` caveat: the `evaln` fuel is `(iteration depth) + (max intermediate
value)`): because fuel dominates the largest intermediate value, and that value here is the encoded table
`≥ 2 ^ (cfgRank …)`, `runtimeOf universalInterp` is **not** polynomially bounded.  So this DP construction,
though a fully verified universal interpreter, does **not** by itself discharge `DiagRuntimePolyBounded`.
Closing that gap genuinely requires a different cost model (bit / RAM, table as *addressable memory* rather
than one giant `Nat`) that `Code.evaln`'s fuel does not capture — which is precisely where the difficulty of
efficient simulation lives, not in the construction.

This is an honest negative result, not `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- `Nat.pair` always dominates the square of its second component. -/
theorem pair_ge_sq (a b : ℕ) : b * b ≤ Nat.pair a b := by
  unfold Nat.pair
  split
  · omega
  · nlinarith [Nat.not_lt.mp ‹¬ a < b›]

/-- Appending one cell **squares** the encoded table (modulo `+1`). -/
theorem encodeList_tableList_succ_ge (spec : ℕ → ℕ) (N : ℕ) :
    (encodeList (tableList spec N)) * (encodeList (tableList spec N)) + 1
      ≤ encodeList (tableList spec (N + 1)) := by
  show _ ≤ encodeList (spec N :: tableList spec N)
  rw [encodeList]
  have := pair_ge_sq (spec N) (encodeList (tableList spec N))
  omega

/-- **Exponential lower bound: the memo table as a `Nat` is `≥ 2 ^ (cell count)`.** -/
theorem encodeList_tableList_exp_lower (spec : ℕ → ℕ) (N : ℕ) :
    2 ^ N ≤ encodeList (tableList spec (N + 1)) := by
  induction N with
  | zero =>
    show 1 ≤ encodeList (spec 0 :: tableList spec 0)
    rw [encodeList]; have := pair_ge_sq (spec 0) (encodeList (tableList spec 0)); omega
  | succ N ih =>
    have hstep := encodeList_tableList_succ_ge spec (N + 1)
    have hpow : (1 : ℕ) ≤ 2 ^ N := Nat.one_le_two_pow
    have : 2 ^ (N + 1)
        ≤ (encodeList (tableList spec (N + 1))) * (encodeList (tableList spec (N + 1))) + 1 := by
      nlinarith [ih, hpow, pow_succ 2 N]
    omega

/-- **The no-go: the interpreter's memo table at the diagonal target is exponential in the rank.**

`buildTableCtx interpBody` produces a value `≥ 2 ^ (cfgRank E B K c0.enc n0)` — super-polynomial in the
config-space — so under the `evaln` fuel measure (fuel `≥` max intermediate value) `universalInterp` has no
polynomial runtime bound. -/
theorem diagonal_memo_table_exp (E B K n0 : ℕ) (c0 : UCode)
    (hKB : K ≤ B) (hcE : c0.enc < E + 1) (hn0 : n0 < B + 1) :
    ∃ v, (buildTableCtx interpBody).eval (Nat.pair (Nat.pair E B) (cfgRank E B K c0.enc n0 + 1))
        = Part.some v
      ∧ 2 ^ (cfgRank E B K c0.enc n0) ≤ v :=
  ⟨_, universal_interp_table E B K n0 c0 hKB hcE hn0,
    encodeList_tableList_exp_lower (specOf E B) (cfgRank E B K c0.enc n0)⟩

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.encodeList_tableList_exp_lower
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.diagonal_memo_table_exp
