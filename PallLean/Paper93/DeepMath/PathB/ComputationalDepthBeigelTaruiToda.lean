import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBeigelTaruiSymAndFold

/-!
# Beigel–Tarui, rung 11: Toda's general-coefficient `SYM` encoding

Rung 10 gave the `SYM` top for *unit* coefficients: the fold is the count of satisfied ANDs.  For **general** `F_p`
coefficients the fold is `∑_{satisfied d} coeff(d)`, which is *not* a function of the bare count.  Toda's trick recovers
a single symmetric count: **replicate** each AND `coeff(d)` times (as a value `0..p-1`), so the total number of
satisfied *replicated* ANDs is `∑_{satisfied d} coeff(d).val`, and the fold in `F_p` is exactly that ℕ-count cast to
`ZMod p`.  The whole polynomial is thus `h(count)` with `h = Nat.cast` over a *single* count — the `SYM∘AND` normal form
for arbitrary coefficients.

  `repCount` — the Toda count: satisfied ANDs each weighted by its coefficient's value (the replicated-AND count).
  `eval_eq_repCount_cast` — **PROVED, the general `SYM` top**: over `F_p`, a polynomial's Boolean value equals
        `↑(repCount)` — a function `h(count)` of a *single* ℕ-count of satisfied replicated ANDs.
  `repCount_le` — **PROVED**: the count is bounded by `(p-1) · #monomials`, so the symmetric top reads a count in a
        bounded range.

With rung 9's `∘AND` fold, this completes the `SYM∘AND` fold for arbitrary polynomials over `F_p`: any low-degree
polynomial's Boolean value is `Nat.cast` of the number of satisfied replicated ANDs — a symmetric function of one
count of ANDs.

## Honest scope

This is the full `SYM∘AND` fold: a polynomial over `F_p` is a symmetric function (`Nat.cast`) of a single count of
`≤ (p-1)·(n+1)^D` replicated ANDs (the repo's `beigelTarui_monomial_count_le` bounds the monomials; replication
multiplies by `≤ p-1`).  This is exactly the `SYM∘AND` shape the repo's `symEval`/`gateCount` count layer consumes and
`…NFrameFastSAT.symAndModel` turns into a `FastSATModel` for the Williams route.  What remains is to instantiate the
whole pipeline (rungs 1–11) on a concrete `ACC⁰` circuit — using rungs 6–8's low-degree approximation to get the
polynomial from the circuit, then this fold to reach `SYM∘AND`.  That circuit-level instantiation is the remaining
Beigel–Tarui content.  Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

open MvPolynomial
open scoped Classical

variable {p n : ℕ} [NeZero p]

/-- **Toda's replicated-AND count**: the number of satisfied ANDs, each replicated `coeff(d).val` times. -/
def repCount (P : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool) : ℕ :=
  ∑ d ∈ P.support, (P.coeff d).val * (if (∀ i ∈ d.support, x i = true) then 1 else 0)

/-- **The general `SYM` top (proved)**: over `F_p`, a polynomial's Boolean value is `↑(repCount)` — `Nat.cast` of a
*single* count of satisfied replicated ANDs.  This is the `SYM∘AND` normal form for arbitrary coefficients: a symmetric
function of one AND-count. -/
theorem eval_eq_repCount_cast (P : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool) :
    (eval (fun i => embed (x i))) P = (repCount P x : ZMod p) := by
  rw [eval_as_weighted_ands, repCount, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id']
  simp only [id_eq]
  congr 1
  split_ifs <;> simp

/-- **The count is bounded (proved)**: `repCount ≤ (p-1) · #monomials`, so the symmetric top reads a count in a bounded
range. -/
theorem repCount_le (P : MvPolynomial (Fin n) (ZMod p)) (x : Fin n → Bool) :
    repCount P x ≤ (p - 1) * P.support.card := by
  rw [repCount]
  calc ∑ d ∈ P.support, (P.coeff d).val * (if (∀ i ∈ d.support, x i = true) then 1 else 0)
      ≤ ∑ _d ∈ P.support, (p - 1) := by
        apply Finset.sum_le_sum
        intro d _
        have hlt : (P.coeff d).val < p := ZMod.val_lt _
        split_ifs
        · simp only [mul_one]; omega
        · simp only [mul_zero]; omega
    _ = P.support.card * (p - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = (p - 1) * P.support.card := Nat.mul_comm _ _

end PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase

#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.eval_eq_repCount_cast
#print axioms PallLean.Paper93.DeepMath.PathB.BeigelTaruiBase.repCount_le
