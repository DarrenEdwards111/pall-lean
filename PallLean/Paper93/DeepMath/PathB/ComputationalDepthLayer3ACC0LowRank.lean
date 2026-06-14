import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3LowDegHolonomy

/-!
# Socket 2: `ACC⁰` is approximated by low-effective-dimension (low-rank) predictors

The agreement layer (`…Layer3Agreement`) already extracts, from the Razborov–Smolensky probabilistic approximant, a
**single** low-degree polynomial that agrees with an `AC⁰[p]` circuit on `≥ 3/4` of inputs (`exists_large_agreement_set`),
with degree `≤ ((p-1)t)^depth` (`toAgree_totalDegree_le`).  Socket 2 turns this into a statement about
**effective dimension**, connecting it to socket 1 (`…Layer3LowDegHolonomy`): the approximant's *evaluation function on
the cube* lies in the low-effective-dimension subspace `V_D = span{e_S : |S| ≤ D}` (`D = ((p-1)t)^depth`), the same
space socket 1 showed the holonomy parity target escapes.

The genuinely new step is the **multilinear reduction** `eval_mem_lowDegSpan`: a degree-`≤D` polynomial, evaluated on
`{0,1}`-inputs, is a linear combination of the squarefree monomials `e_S = ∏_{i∈S} x_i` with `|S| ≤ D` — because
`x_i^{e+1} = x_i` on the cube (`boolToZMod_pow_succ`) collapses every monomial `∏ X_i^{d_i}` to the squarefree
`e_{support d}`, whose support has size `≤ totalDegree`.  Hence the evaluation lands in `V_D`.

Composing: **an `AC⁰[p]` circuit is approximated on `≥ 3/4` of inputs by a function in `V_D`** — a low-rank
(low-effective-dimension) predictor — which is exactly the `ACC0ApproximatesByLowRankPredictors` socket.  With socket 1
(`holonomy_parity_not_lowDegEval`, `V_D` cannot *represent* parity for `D < n`) this exhibits the tension RS resolves
quantitatively (the `parity_circuit_false` band counting): the circuit's approximant is in `V_D`, yet the target it
must `3/4`-match is outside `V_D`.

## What is proved (clean axioms, no `sorry`)

* `eval_mem_lowDegSpan` — a degree-`≤D` polynomial's cube-evaluation is in `V_D` (multilinear reduction).
* `acc0_approx_by_lowRankPredictor` — **socket 2**: an `AC⁰[p]` circuit (`p^t ≥ 4·#subcircuits`) is `3/4`-approximated
  by a function in `V_D`, `D = ((p-1)t)^depth`.

## Honest scope

The exact effective-dimension membership of the approximant plus the quantitative `3/4`-agreement — the structural
input to RS.  It does **not** by itself yield the lower bound (that is the band counting in `parity_circuit_false`,
combining this with socket 1).  Classical `AC⁰[p]` regime; the `hmod` hypothesis restricts `MOD` moduli to `= p`.
**Not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3ACC0LowRank

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.Layer3
open MvPolynomial

variable {n : ℕ}

/-- **The multilinear reduction (proved).**  A polynomial `g` of `totalDegree ≤ D`, evaluated on the Boolean cube,
is a linear combination of the squarefree monomials `e_S` with `|S| ≤ D`: each monomial `∏ X_i^{d_i}` collapses on
`{0,1}` (via `x_i^{e+1} = x_i`) to `e_{support d}`, and `|support d| ≤ totalDegree d ≤ D`.  Hence the evaluation
function lies in the low-effective-dimension span `V_D`. -/
theorem eval_mem_lowDegSpan (p : ℕ) [Fact p.Prime] {D : ℕ}
    (g : MvPolynomial (Fin n) (ZMod p)) (hg : g.totalDegree ≤ D) :
    (fun x => eval (fun i => boolToZMod p (x i)) g) ∈ Submodule.span (ZMod p)
      (Set.range (fun S : {S // S ∈ lowDegMonomials n D} => squarefreeEvalMonomial p S.1)) := by
  classical
  have hfun : (fun x => eval (fun i => boolToZMod p (x i)) g)
      = ∑ d ∈ g.support, g.coeff d • squarefreeEvalMonomial p d.support := by
    funext x
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro d _
    rw [Pi.smul_apply, smul_eq_mul]
    simp only [squarefreeEvalMonomial]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    rw [he, boolToZMod_pow_succ]
  rw [hfun]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨⟨d.support, ?_⟩, rfl⟩
  rw [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.subset_univ _, le_trans ?_ hg⟩
  have hcard : d.support.card ≤ (d.sum fun _ e => e) := by
    rw [Finsupp.sum]
    calc d.support.card = ∑ _i ∈ d.support, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ i ∈ d.support, d i :=
        Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  exact le_trans hcard (MvPolynomial.le_totalDegree hd)

/-- **Socket 2 — `ACC⁰` approximated by low-rank predictors (proved).**  For an `AC⁰[p]` circuit (every `MOD` gate
`q = p`) at horizon `t` with `p^t ≥ 4·#subcircuits`, there is a function `f` in the low-effective-dimension span
`V_D` (`D = ((p-1)t)^depth`) that agrees with the circuit on `≥ 3/4` of inputs.  The circuit is captured, off a
`1/4`-fraction, by a predictor of effective dimension `≤ ∑_{k≤D} C(n,k)` — the same `V_D` socket 1 showed the
holonomy parity target escapes. -/
theorem acc0_approx_by_lowRankPredictor (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (C : BoolCircuitSyntax n)
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C → q = p)
    (hsize : 4 * (subcircuits C).toFinset.card ≤ p ^ t) :
    ∃ f : (Fin n → Bool) → ZMod p,
      f ∈ Submodule.span (ZMod p)
          (Set.range (fun S : {S // S ∈ lowDegMonomials n (((p - 1) * t) ^ C.depth)} =>
            squarefreeEvalMonomial p S.1))
        ∧ 3 * 2 ^ n
            ≤ 4 * (Finset.univ.filter
                (fun x : Fin n → Bool => f x = boolToZMod p (C.eval x))).card := by
  obtain ⟨ω, hω⟩ := exists_large_agreement_set p t C hmod hsize
  refine ⟨fun x => eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C), ?_, hω⟩
  exact eval_mem_lowDegSpan p _ (toAgree_totalDegree_le p t ht _ C)

end PallLean.Paper93.DeepMath.PathB.Layer3ACC0LowRank

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3ACC0LowRank.eval_mem_lowDegSpan
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3ACC0LowRank.acc0_approx_by_lowRankPredictor
