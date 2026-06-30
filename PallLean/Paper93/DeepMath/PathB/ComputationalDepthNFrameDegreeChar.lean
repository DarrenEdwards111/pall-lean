import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMODqHigh

/-!
# `NFrameComplexity` is exactly the minimal multilinear-representation degree

The N-Frame socket (`…NFrameACC0Socket`) defined `NFrameComplexity f` as the minimal monoAND-span degree, used as a
proxy for the literal N-Frame invariant.  This file pins down what that proxy *is*, as a literal invariant:

  `nframeComplexity_le_iff_exists_lowdeg` — `NFrameComplexity f ≤ D  ↔  f = Multilinear.eval Q` for some `Q`
        supported on degree `≤ D`.

So `NFrameComplexity f` is **exactly the minimal degree of a multilinear polynomial representing `f`** — a literal,
basis-free polynomial-degree invariant of `f` (the "boundary / observer dimension" of the cube function).  This is
the honest first rung of the bridge from the proxy into the *polynomial* world where the literal SPDP rank
(`SPDPDefs.spdpRank κ ℓ p = finrank(span{m·∂_S p})`) is defined.

## Honest scope

This characterizes the proxy as the multilinear **degree**.  The repo's two literal SPDP objects —
`SPDPDefs.spdpRank` (the derivative-span *finrank* on `MvPolynomial`) and `SPDPFeatureProjection.spdpProj` /
`pcrank` (the discrete partial-derivative *projection rank* on Boolean matrices) — are *different* invariants
(rank-of-a-derivative-span, not degree).  Reconciling the degree characterization here with those derivative-rank
objects is the genuine remaining bridge, and the SPDP/CEW route to the P-side is audited as assumed-not-derived /
barriered in the repo's own `NFrameHypercubeConstraint` / `SPDPFeatureProjection` docstrings.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (sqfGens sqfSpan_mono)
open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)
open PallLean.Paper93.DeepMath.PathB.Multilinear (eval eval_surjective)

variable {n : ℕ} {F : Type*} [Field F]

/-- **Reverse membership: a degree-`≤D` multilinear eval lives in the degree-`≤D` span (proved).** -/
theorem eval_mem_sqfSpan_of_lowdeg {D : ℕ} (Q : Finset (Fin n) → F)
    (hQ : ∀ S, D < S.card → Q S = 0) : eval Q ∈ Submodule.span F (sqfGens F n D) := by
  have heq : eval Q = ∑ S : Finset (Fin n), Q S • sqfEval F S := by
    funext x
    simp only [eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sqfEval_eq_monomialFn]
  rw [heq]
  apply Submodule.sum_mem
  intro S _
  by_cases hS : S.card ≤ D
  · apply Submodule.smul_mem
    have hSmem : S ∈ lowDegMonomials n D := by
      simp only [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ S, hS⟩
    apply Submodule.subset_span
    rw [sqfGens]
    exact ⟨⟨S, hSmem⟩, rfl⟩
  · rw [hQ S (by omega), zero_smul]
    exact Submodule.zero_mem _

/-- Every cube function lies in the full degree-`≤n` span (the monomials span the cube). -/
theorem mem_sqfSpan_n [Fintype F] [DecidableEq F] (f : (Fin n → Bool) → F) :
    f ∈ Submodule.span F (sqfGens F n n) := by
  obtain ⟨c, hc⟩ := eval_surjective f
  rw [← hc]
  exact eval_mem_sqfSpan_n c

/-- **`NFrameComplexity` is the minimal multilinear degree (proved).**  `NFrameComplexity f ≤ D` iff `f` is a
multilinear polynomial of degree `≤ D` — so the N-Frame proxy is *exactly* the minimal multilinear-representation
degree of `f`. -/
theorem nframeComplexity_le_iff_exists_lowdeg [Fintype F] [DecidableEq F]
    (f : (Fin n → Bool) → F) (D : ℕ) :
    NFrameComplexity F f ≤ D ↔
      ∃ Q : Finset (Fin n) → F, (∀ S, D < S.card → Q S = 0) ∧ f = eval Q := by
  constructor
  · intro hle
    have hne : {E | f ∈ Submodule.span F (sqfGens F n E)}.Nonempty := ⟨n, mem_sqfSpan_n f⟩
    have hmem_inf := Nat.sInf_mem hne
    exact exists_lowdeg_coef_of_mem_sqfSpan (sqfSpan_mono hle hmem_inf)
  · rintro ⟨Q, hQ, rfl⟩
    exact nframeComplexity_le_of_mem_span (eval_mem_sqfSpan_of_lowdeg Q hQ)

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_le_iff_exists_lowdeg
