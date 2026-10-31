import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDegreeChar

/-!
# N-Frame: capture beyond the de Morgan basis — the low-N-Frame class is an F-subspace

`smallTree_captures` proves capture only for individual bounded-fan-in de Morgan (AND/OR/NOT) trees.  This file extends
capture to a strictly richer, **arithmetic** class: the low-N-Frame region is an `F`-subspace of the function space, so it
is closed under `F`-linear combination.  Any weighted sum of captured functions — an arithmetic (ΣΠ) combination, not a
Boolean de Morgan formula — is still captured.

  `mem_sqfSpan_of_nframeComplexity_le` — **PROVED**: low N-Frame ⇒ membership in the degree-`≤B` monoAND span (via the
        degree characterisation).
  `nframeComplexity_add_le` / `nframeComplexity_smul_le` / `nframeComplexity_linComb_le` — **PROVED**: the captured region
        is closed under `+`, scalar `•`, and hence any `F`-linear combination `a·f + b·g`.

So capture is not confined to the de Morgan basis: it covers the whole `F`-linear span of small trees — arithmetic circuits
over them — at the same bound `B`.  This widens the observer class the beam separates against, without touching the
composite-`MOD` barrier (which is about *nonlinear*/gate composition, not linear combination).

## Honest scope

This extends the *proved* low side to the `F`-linear closure of captured functions — genuinely beyond Boolean de Morgan
formulas.  It does **not** extend capture to composite-`MOD` gates or to the general P-time model (the load-bearing
capture bridge), which remain the barrier and the open `P ≠ NP`-strength member.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (sqfGens)

variable {n : ℕ} {F : Type*} [Field F]

/-- **Low N-Frame ⇒ span membership (proved).**  If `NFrameComplexity f ≤ B` then `f` lies in the degree-`≤B` monoAND
span — the membership form of the degree characterisation. -/
theorem mem_sqfSpan_of_nframeComplexity_le [Fintype F] [DecidableEq F]
    {f : (Fin n → Bool) → F} {B : ℕ} (h : NFrameComplexity F f ≤ B) :
    f ∈ Submodule.span F (sqfGens F n B) := by
  obtain ⟨Q, hQ, hf⟩ := (nframeComplexity_le_iff_exists_lowdeg f B).mp h
  rw [hf]
  exact eval_mem_sqfSpan_of_lowdeg Q hQ

/-- **Capture is closed under sums (proved).**  If `f` and `g` are captured at `B`, so is `f + g`. -/
theorem nframeComplexity_add_le [Fintype F] [DecidableEq F]
    {f g : (Fin n → Bool) → F} {B : ℕ}
    (hf : NFrameComplexity F f ≤ B) (hg : NFrameComplexity F g ≤ B) :
    NFrameComplexity F (f + g) ≤ B :=
  nframeComplexity_le_of_mem_span
    (Submodule.add_mem _ (mem_sqfSpan_of_nframeComplexity_le hf)
      (mem_sqfSpan_of_nframeComplexity_le hg))

/-- **Capture is closed under scalar multiples (proved).**  If `f` is captured at `B`, so is `a • f`. -/
theorem nframeComplexity_smul_le [Fintype F] [DecidableEq F]
    {f : (Fin n → Bool) → F} {B : ℕ} (a : F) (hf : NFrameComplexity F f ≤ B) :
    NFrameComplexity F (a • f) ≤ B :=
  nframeComplexity_le_of_mem_span
    (Submodule.smul_mem _ a (mem_sqfSpan_of_nframeComplexity_le hf))

/-- **Capture is closed under `F`-linear combination (proved).**  Any `a·f + b·g` of two captured functions is captured
at the same bound — the low-N-Frame region is an `F`-subspace, so the captured class contains the whole linear span of
small trees, an arithmetic class strictly beyond the de Morgan basis. -/
theorem nframeComplexity_linComb_le [Fintype F] [DecidableEq F]
    {f g : (Fin n → Bool) → F} {B : ℕ} (a b : F)
    (hf : NFrameComplexity F f ≤ B) (hg : NFrameComplexity F g ≤ B) :
    NFrameComplexity F (a • f + b • g) ≤ B :=
  nframeComplexity_add_le (nframeComplexity_smul_le a hf) (nframeComplexity_smul_le b hg)

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_add_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_linComb_le
