import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameACC0Socket
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthModQReduction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTailBound

/-!
# `MOD_q` has high N-Frame complexity (the `target_has_high_nframe` side)

The mirror of the `acc0_implies_low_nframe` socket (`ComputationalDepthNFrameACC0Socket`): the `MOD_q` object — the
full `q`-ary product `omegaFn ω univ = ω^{∑xᵢ}` for a primitive `q`-th root of unity `ω ∈ F` (`q ≥ 2`, `q ≠ char F`)
— has **high** N-Frame complexity (`≥ ⌈n/2⌉`), so it cannot sit in any low-degree monomial-`AND` span.

The mechanism is the q-ary Razborov–Smolensky boosting (`omega_boosting_le_multilinear`): if a degree-`≤D` multilinear
polynomial equals `omegaFn ω univ` on a set `G`, then `|G| ≤ ∑_{i≤n/2+D} C(n,i)`.  Applied at `G = univ` (all `2^n`
inputs), a degree-`≤D` representation forces `2^n ≤ ∑_{i≤n/2+D} C(n,i)`, which `Dimension.sum_choose_lt` refutes
whenever `n/2+D < n`, i.e. `D < ⌈n/2⌉`.  Hence:

  `omegaFn_univ_not_mem_sqfSpan` — `omegaFn ω univ ∉ span(sqfGens F n D)` for every `D < n − n/2`;
  `nframeComplexity_omegaFn_univ_ge` — `NFrameComplexity (omegaFn ω univ) ≥ n − n/2` (`= ⌈n/2⌉`).

Together with the socket's `nframeComplexity_le_two_pow_depth` (AC⁰ ⇒ `≤ 2^depth·width`), this is the two-sided
shape of the N-Frame separation skeleton — *against the monoAND-span-degree proxy*: the hard function has linear
N-Frame complexity, bounded-fan-in AC⁰ has `2^O(depth)·width` complexity.

## Honest scope

This is `target_has_high_nframe` **for the proxy** (`NFrameComplexity` = minimal monoAND-span degree).  The genuine
open pieces are unchanged: (1) tie the proxy to the *literal* N-Frame invariant; (2) the high bound here is against
the *polynomial-method* degree, valid for `MOD_q` over a field of characteristic `≠ q` — extending the LOW side to
full ACC⁰ with *unbounded composite `MOD`* is the composite-`MOD` barrier.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (sqfGens)
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn omega_boosting_le_multilinear)
open PallLean.Paper93.DeepMath.PathB.Layer4 (sqfEval boolToField)
open PallLean.Paper93.DeepMath.PathB.Layer3 (lowDegMonomials)
open PallLean.Paper93.DeepMath.PathB.Multilinear (eval monomialFn eval_surjective)
open PallLean.Paper93.DeepMath.PathB.Dimension (sum_choose_lt)

variable {n : ℕ} {F : Type*} [Field F]

/-- The squarefree gate-eval is the multilinear monomial: both are `∏_{i∈S}(if xᵢ then 1 else 0)`. -/
theorem sqfEval_eq_monomialFn (S : Finset (Fin n)) :
    sqfEval F S = monomialFn (F := F) S := by
  funext x
  simp only [sqfEval, monomialFn, boolToField]

/-- **Extraction: a low-degree span element is a low-degree multilinear eval.**  If `f ∈ span(sqfGens F n D)` then
`f = eval Q` for a `Q` supported on `|S| ≤ D` — the bridge from the monoAND span into the q-ary boosting bound. -/
theorem exists_lowdeg_coef_of_mem_sqfSpan {f : (Fin n → Bool) → F} {D : ℕ}
    (h : f ∈ Submodule.span F (sqfGens F n D)) :
    ∃ Q : Finset (Fin n) → F, (∀ S, D < S.card → Q S = 0) ∧ f = eval Q := by
  rw [sqfGens, Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨fun T => if hT : T ∈ lowDegMonomials n D then c ⟨T, hT⟩ else 0, ?_, ?_⟩
  · intro S hScard
    have hnot : S ∉ lowDegMonomials n D := by
      simp only [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
        true_and, not_le]
      omega
    show (if hT : S ∈ lowDegMonomials n D then c ⟨S, hT⟩ else 0) = 0
    rw [dif_neg hnot]
  · funext x
    rw [← hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eval, sqfEval_eq_monomialFn]
    symm
    calc ∑ T : Finset (Fin n),
            (if hT : T ∈ lowDegMonomials n D then c ⟨T, hT⟩ else 0) * monomialFn T x
        = ∑ T ∈ lowDegMonomials n D,
            (if hT : T ∈ lowDegMonomials n D then c ⟨T, hT⟩ else 0) * monomialFn T x := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro T _ hT
          rw [dif_neg hT, zero_mul]
      _ = ∑ S : ↥(lowDegMonomials n D), c S * monomialFn (S : Finset (Fin n)) x := by
          rw [← Finset.sum_coe_sort (lowDegMonomials n D)
            (fun T => (if hT : T ∈ lowDegMonomials n D then c ⟨T, hT⟩ else 0) * monomialFn T x)]
          apply Finset.sum_congr rfl
          intro S _
          rw [dif_pos S.2, Subtype.coe_eta]

/-- Every function is in the full degree-`≤n` monomial-`AND` span (the monomials span the cube). -/
theorem eval_mem_sqfSpan_n (Q : Finset (Fin n) → F) :
    eval Q ∈ Submodule.span F (sqfGens F n n) := by
  have heq : eval Q = ∑ S : Finset (Fin n), Q S • sqfEval F S := by
    funext x
    simp only [eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sqfEval_eq_monomialFn]
  rw [heq]
  apply Submodule.sum_mem
  intro S _
  apply Submodule.smul_mem
  have hSmem : S ∈ lowDegMonomials n n := by
    simp only [lowDegMonomials, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ S, (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)⟩
  apply Submodule.subset_span
  rw [sqfGens]
  exact ⟨⟨S, hSmem⟩, rfl⟩

/-- `omegaFn ω univ` lies in the full degree-`≤n` span (so its N-Frame complexity set is nonempty). -/
theorem omegaFn_univ_mem_sqfSpan_n [Fintype F] [DecidableEq F] (ω : F) :
    omegaFn ω (Finset.univ : Finset (Fin n)) ∈ Submodule.span F (sqfGens F n n) := by
  obtain ⟨c, hc⟩ := eval_surjective (omegaFn ω (Finset.univ : Finset (Fin n)))
  rw [← hc]
  exact eval_mem_sqfSpan_n c

/-- **`MOD_q` is not low-degree (proved).**  For a primitive `q`-th root `ω` (`q ≥ 2`), the full product
`omegaFn ω univ` is in no degree-`<⌈n/2⌉` monomial-`AND` span: a degree-`D` representation would, by q-ary boosting
at `G = univ`, force `2^n ≤ ∑_{i≤n/2+D} C(n,i)`, contradicting `sum_choose_lt` when `n/2+D < n`. -/
theorem omegaFn_univ_not_mem_sqfSpan [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) {D : ℕ} (hD : D < n - n / 2) :
    omegaFn ω (Finset.univ : Finset (Fin n)) ∉ Submodule.span F (sqfGens F n D) := by
  intro hmem
  obtain ⟨Q, hQdeg, hQeq⟩ := exists_lowdeg_coef_of_mem_sqfSpan hmem
  have hcard := omega_boosting_le_multilinear ω hω hq2 Q hQdeg Finset.univ
    (fun b _ => by rw [← hQeq])
  have hcard2 : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
  rw [Finset.card_univ, hcard2] at hcard
  have hlt : ∑ i ∈ Finset.range (n / 2 + D + 1), n.choose i < 2 ^ n := sum_choose_lt (by omega)
  omega

/-- **`MOD_q` has high N-Frame complexity (proved).**  `NFrameComplexity (omegaFn ω univ) ≥ n − n/2 = ⌈n/2⌉` — the
`target_has_high_nframe` side, against the monoAND-span-degree proxy. -/
theorem nframeComplexity_omegaFn_univ_ge [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) :
    n - n / 2 ≤ NFrameComplexity F (omegaFn ω (Finset.univ : Finset (Fin n))) := by
  by_contra hlt
  rw [not_le] at hlt
  have hne : {D | omegaFn ω (Finset.univ : Finset (Fin n)) ∈ Submodule.span F (sqfGens F n D)}.Nonempty :=
    ⟨n, omegaFn_univ_mem_sqfSpan_n ω⟩
  have hmem := Nat.sInf_mem hne
  exact omegaFn_univ_not_mem_sqfSpan ω hω hq2 hlt hmem

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.omegaFn_univ_not_mem_sqfSpan
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.nframeComplexity_omegaFn_univ_ge
