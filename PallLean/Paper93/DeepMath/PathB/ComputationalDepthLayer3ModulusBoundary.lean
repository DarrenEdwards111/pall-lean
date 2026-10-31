import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3ACC0LowRank

/-!
# Socket 3: the modulus boundary of the polynomial method

Sockets 1–2 work entirely over `F_p` and require every `MOD` gate to have modulus `= p` (the hypothesis `hmod` in
`parity_function_lower_bound`, `acc0_approx_by_lowRankPredictor`, …).  This file formalises **why** that hypothesis
is load-bearing — the genuine boundary of the polynomial method — and honestly locates the wall.

**The engine: Fermat linearisation.**  Over `F_p`, `1 − a^{p−1}` is the indicator `1[a = 0]`
(`fermat_indicator`, from `a^{p−1} = 1` for `a ≠ 0`).  Hence a `MOD_p` gate's detection `1[∑ x_i ≡ r (mod p)]` is
**exactly** the degree-`(p−1)` `F_p` polynomial `1 − (∑ X_i − r)^{p−1}` on the cube
(`modpIndicatorPoly_eval`), of total degree `≤ p−1` **independent of fan-in** (`modpIndicatorPoly_totalDegree_le`).
So a `MOD_p` gate lands in the low-effective-dimension span `V_{p−1}` of sockets 1–2 (`modp_eval_mem_lowDegSpan`) —
which is precisely why `MOD_p` gates compose into the degree bound `((p−1)t)^depth`.

**The wall.**  For `MOD_q` with `q ≠ p`, the `F_p` arithmetic of `∑ boolToZMod p (x_i)` only tracks the count
**mod p**, so it cannot detect the count **mod q**; there is no fan-in-independent low-degree `F_p` representation of
`MOD_q`.  In the lower-bound direction this is Smolensky's `MOD_q ∉ AC⁰[p]` (`q ≠ p` prime), already assembled in
`…Layer4ModqChar` (`mod_q_indicators_false`).  For **composite** moduli (`AC⁰[m]`, e.g. `MOD_6`) and the general
`NEXP ⊄ ACC⁰` separation the polynomial method **provably does not reach** — that is Williams' *algorithmic method*
(faster ACC⁰-SAT + the nondeterministic time hierarchy), the route the PathB switching / `NFrameACC0Master` arc
targets, **not** this `F_p`-polynomial machinery.  Socket 3 is therefore not "closed" by a composite-modulus lower
bound (that would be `NEXP ⊄ ACC⁰`-hard or open); it is *delimited*: the method extends exactly to `MOD_p` gates.

## What is proved (clean axioms, no `sorry`)

* `fermat_indicator` — `1 − a^{p−1} = 1[a = 0]` over `F_p` (the linearisation engine).
* `modpIndicatorPoly`, `modpIndicatorPoly_eval` — a `MOD_p` detector is exactly `1 − (∑X_i − r)^{p−1}` on the cube.
* `modpIndicatorPoly_totalDegree_le` — degree `≤ p−1`, **independent of fan-in**.
* `modp_eval_mem_lowDegSpan` — a `MOD_p` gate's value function lies in `V_{p−1}` (the sockets-1–2 space).

## Honest scope

The positive boundary of the polynomial method (`MOD_p` is low-degree over `F_p`), proved; the negative side
(`MOD_q`, composite `m`, `NEXP ⊄ ACC⁰`) is delimited and pointed to its proper tools, **not** faked.  Classical
`AC⁰[p]` regime; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3ModulusBoundary

open PallLean.Paper93.DeepMath.PathB.Layer3
open MvPolynomial

variable {n : ℕ}

/-- **Fermat linearisation (proved): `1 − a^{p−1} = 1[a = 0]` over `F_p`.**  The exact indicator that powers the
polynomial method: `a^{p−1} = 1` for `a ≠ 0` (Fermat), and `0^{p−1} = 0`. -/
theorem fermat_indicator (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    1 - a ^ (p - 1) = if a = 0 then 1 else 0 := by
  have hp2 := (Fact.out (p := p.Prime)).two_le
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, zero_pow (by omega : p - 1 ≠ 0), sub_zero]
  · rw [if_neg ha, ZMod.pow_card_sub_one_eq_one ha, sub_self]

/-- The exact `F_p` polynomial detecting `∑_{i∈S} x_i ≡ r (mod p)` — degree `p−1`, any fan-in. -/
noncomputable def modpIndicatorPoly (p : ℕ) (S : Finset (Fin n)) (r : ZMod p) :
    MvPolynomial (Fin n) (ZMod p) :=
  1 - (∑ i ∈ S, X i - C r) ^ (p - 1)

/-- **A `MOD_p` detector is exactly `1 − (∑X_i − r)^{p−1}` on the cube (proved).** -/
theorem modpIndicatorPoly_eval (p : ℕ) [Fact p.Prime] (S : Finset (Fin n)) (r : ZMod p)
    (x : Fin n → Bool) :
    eval (fun i => boolToZMod p (x i)) (modpIndicatorPoly p S r)
      = if (∑ i ∈ S, boolToZMod p (x i)) = r then 1 else 0 := by
  unfold modpIndicatorPoly
  rw [map_sub, map_one, map_pow, map_sub, map_sum]
  simp only [eval_X, eval_C]
  rw [fermat_indicator]
  simp only [sub_eq_zero]

/-- **The `MOD_p` detector has degree `≤ p−1`, independent of fan-in (proved).** -/
theorem modpIndicatorPoly_totalDegree_le (p : ℕ) [Fact p.Prime] (S : Finset (Fin n)) (r : ZMod p) :
    (modpIndicatorPoly p S r).totalDegree ≤ p - 1 := by
  have hp2 := (Fact.out (p := p.Prime)).two_le
  unfold modpIndicatorPoly
  have hsum : (∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
    intro i _
    rw [totalDegree_X]
  have hf : ((∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p))) - C r).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [totalDegree_C]
    exact max_le hsum (by omega)
  have hpow : (((∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p))) - C r) ^ (p - 1)).totalDegree
      ≤ p - 1 := by
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    calc (p - 1) * ((∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p))) - C r).totalDegree
        ≤ (p - 1) * 1 := by gcongr
      _ = p - 1 := mul_one _
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  exact max_le (by omega) hpow

/-- **A `MOD_p` gate's value function lies in the low-effective-dimension span `V_{p−1}` (proved).**  Via the
multilinear reduction `eval_mem_lowDegSpan` (socket 2): the degree-`(p−1)` `MOD_p` detector evaluates into the same
span sockets 1–2 use.  This is why `MOD_p` gates compose into the `((p−1)t)^depth` degree bound — and exactly the
gate class the polynomial method handles. -/
theorem modp_eval_mem_lowDegSpan (p : ℕ) [Fact p.Prime] (S : Finset (Fin n)) (r : ZMod p) :
    (fun x => eval (fun i => boolToZMod p (x i)) (modpIndicatorPoly p S r))
      ∈ Submodule.span (ZMod p)
        (Set.range (fun T : {T // T ∈ lowDegMonomials n (p - 1)} => squarefreeEvalMonomial p T.1)) :=
  Layer3ACC0LowRank.eval_mem_lowDegSpan p _ (modpIndicatorPoly_totalDegree_le p S r)

end PallLean.Paper93.DeepMath.PathB.Layer3ModulusBoundary

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3ModulusBoundary.fermat_indicator
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3ModulusBoundary.modpIndicatorPoly_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3ModulusBoundary.modpIndicatorPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3ModulusBoundary.modp_eval_mem_lowDegSpan
