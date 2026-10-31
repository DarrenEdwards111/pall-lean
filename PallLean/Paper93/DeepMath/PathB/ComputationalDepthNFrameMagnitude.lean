import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDegreeChar

/-!
# N-Frame: the magnitude ceiling — the full-AND monomial has N-Frame exactly `n`

`MOD_q` reaches N-Frame complexity `⌈n/2⌉` (linear).  This file pushes the *magnitude* to the maximum: the full-support
monomial `∏ᵢ xᵢ = sqfEval F univ` has N-Frame complexity **exactly `n`** — the largest possible value on the cube.

  `eval_Qfull` — **PROVED**: `∏ᵢ xᵢ` is the multilinear eval of the single top-degree coefficient.
  `nframeComplexity_sqfEval_univ_ge` — **PROVED**: N-Frame complexity `≥ n` (a degree-`<n` representation would, by
        `eval_injective`, force the top monomial's coefficient to both be `1` and vanish).
  `nframeComplexity_sqfEval_univ_eq` — **PROVED**: N-Frame complexity `= n`, the maximum.

## Honest scope — magnitude is not hardness

This reaches the maximal N-Frame magnitude, but it is a deliberately **cautionary** result, not progress toward the
separation.  The full-AND `∏ᵢ xᵢ` is computationally *trivial* — in unbounded-fan-in `AC⁰` it is a single gate — yet its
N-Frame magnitude is maximal (`n`).  So **high N-Frame magnitude does not certify computational hardness**: the raw
monoAND-degree proxy *inverts* the intended reading on easy high-degree functions.  Concretely, this means the capture
bridge `P ⊆ {low N-Frame}` is *false* at any bound `< n` for the raw proxy (an unbounded-fan-in `AC⁰` function has N-Frame
`n`), which is exactly why the load-bearing bridge needs a *refined* (cube-invariant / boundary) invariant rather than raw
degree.  Pushing the magnitude past linear is therefore *not* the route past the barrier — the barrier is about the
*hardness–magnitude correspondence*, not the magnitude alone.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval)
open PallLean.Paper93.DeepMath.PathB.Multilinear (eval eval_injective)

variable {n : ℕ} {F : Type*} [Field F]

/-- The coefficient function selecting only the top-degree (full-support) monomial. -/
def Qfull (F : Type*) [Field F] (n : ℕ) : Finset (Fin n) → F :=
  fun S => if S = Finset.univ then 1 else 0

/-- **The full-AND is the top monomial's eval (proved).**  `eval Qfull = ∏ᵢ xᵢ = sqfEval F univ`. -/
theorem eval_Qfull : eval (Qfull F n) = sqfEval F (Finset.univ : Finset (Fin n)) := by
  have heq : eval (Qfull F n) = ∑ S : Finset (Fin n), (Qfull F n) S • sqfEval F S := by
    funext x
    simp only [eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sqfEval_eq_monomialFn]
  rw [heq, Finset.sum_eq_single (Finset.univ : Finset (Fin n))
    (fun S _ hSne => by simp [Qfull, hSne])
    (fun hnm => absurd (Finset.mem_univ _) hnm)]
  simp [Qfull]

/-- **The full-AND has N-Frame complexity `≥ n` (proved).**  A degree-`<n` representation would equal `Qfull` by
`eval_injective`, forcing its top coefficient to vanish — contradiction. -/
theorem nframeComplexity_sqfEval_univ_ge [Fintype F] [DecidableEq F] (hn : 0 < n) :
    n ≤ NFrameComplexity F (sqfEval F (Finset.univ : Finset (Fin n))) := by
  by_contra hlt
  rw [not_le] at hlt
  have hle : NFrameComplexity F (sqfEval F (Finset.univ : Finset (Fin n))) ≤ n - 1 := by omega
  obtain ⟨Q, hQ, hQeq⟩ := (nframeComplexity_le_iff_exists_lowdeg _ (n - 1)).mp hle
  have hQQ : Q = Qfull F n := by
    apply eval_injective
    rw [← hQeq, eval_Qfull]
  have hz : Q Finset.univ = 0 :=
    hQ Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  rw [hQQ] at hz
  simp [Qfull] at hz

/-- **The full-AND has N-Frame complexity exactly `n` (proved)** — the maximal value on the cube. -/
theorem nframeComplexity_sqfEval_univ_eq [Fintype F] [DecidableEq F] (hn : 0 < n) :
    NFrameComplexity F (sqfEval F (Finset.univ : Finset (Fin n))) = n :=
  le_antisymm (nframeComplexity_le_of_mem_span (mem_sqfSpan_n _))
    (nframeComplexity_sqfEval_univ_ge hn)

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_sqfEval_univ_eq
