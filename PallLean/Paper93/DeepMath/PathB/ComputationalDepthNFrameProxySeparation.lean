import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMODqHigh

/-!
# `acc0_proxy_separation`: the contradiction skeleton instantiated at the N-Frame proxy

This file assembles the two sides of the N-Frame separation skeleton into a single named theorem, at the level of the
`NFrameComplexity` proxy (= minimal monoAND-span degree):

* **low side** (`nframeComplexity_le_two_pow_depth`, the `acc0_implies_low_nframe` socket): every bounded-fan-in AC⁰
  (de Morgan basis) circuit `t : AndOrTree` has `NFrameComplexity (evalT F t) ≤ 2^{depth t}·leafWidth t`;
* **high side** (`nframeComplexity_omegaFn_univ_ge`, the `target_has_high_nframe` lemma): the `MOD_q` object
  `omegaFn ω univ` has `NFrameComplexity ≥ ⌈n/2⌉`.

These are in genuine tension: a bounded-fan-in constant-depth circuit's `2^{depth}·width` cannot reach `⌈n/2⌉`.

  `andOrTree_computing_modq_large` — any AC⁰ circuit computing `MOD_q` has `2^{depth}·leafWidth ≥ ⌈n/2⌉`;
  `acc0_proxy_separation` — no AC⁰ circuit with `2^{depth}·leafWidth < ⌈n/2⌉` computes `MOD_q` (`False`);
  `modq_not_computable_by_small_tree` — for fixed depth `d`, width `w` and `2^d·w < ⌈n/2⌉` (true for large `n`),
        `MOD_q` is not computed by any depth-`≤d`, width-`≤w` AC⁰ circuit.

This is `MOD_q ∉ AC⁰` (bounded-fan-in, de Morgan basis) re-expressed in the N-Frame invariant — the polynomial-method
separation, end to end, at the proxy level.

## Honest scope

The whole statement is **at the proxy** (`NFrameComplexity` = monoAND-span degree) and for the **bounded-fan-in de
Morgan basis** (no `MOD` gates).  The two open pieces are unchanged: (1) tie the proxy to the *literal* N-Frame
invariant; (2) extend the low side to full ACC⁰ with *unbounded composite `MOD`* (the composite-`MOD` barrier).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameACC0

open PallLean.Paper93.DeepMath.PathB.ACC0ModFieldExact (AndOrTree)
open PallLean.Paper93.DeepMath.PathB.ModQReduction (omegaFn)

variable {n : ℕ} {F : Type*} [Field F]

/-- **Any AC⁰ circuit computing `MOD_q` is large (proved).**  If a bounded-fan-in de Morgan circuit `t` computes
`omegaFn ω univ`, then `2^{depth t}·leafWidth t ≥ ⌈n/2⌉` — the low side meets the high side. -/
theorem andOrTree_computing_modq_large [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (t : AndOrTree n)
    (hcomputes : AndOrTree.evalT F t = omegaFn ω (Finset.univ : Finset (Fin n))) :
    n - n / 2 ≤ 2 ^ treeDepth t * treeLeafWidth t := by
  have hlow : NFrameComplexity F (omegaFn ω (Finset.univ : Finset (Fin n)))
      ≤ 2 ^ treeDepth t * treeLeafWidth t := by
    rw [← hcomputes]
    exact nframeComplexity_le_two_pow_depth t
  exact le_trans (nframeComplexity_omegaFn_univ_ge ω hω hq2) hlow

/-- **The contradiction skeleton (proved).**  No AC⁰ circuit with `2^{depth}·leafWidth < ⌈n/2⌉` computes `MOD_q`. -/
theorem acc0_proxy_separation [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) (t : AndOrTree n)
    (hcomputes : AndOrTree.evalT F t = omegaFn ω (Finset.univ : Finset (Fin n)))
    (hsmall : 2 ^ treeDepth t * treeLeafWidth t < n - n / 2) : False := by
  have := andOrTree_computing_modq_large ω hω hq2 t hcomputes
  omega

/-- **`MOD_q ∉ AC⁰` at the proxy (proved).**  For a fixed depth `d`, leaf-width `w` with `2^d·w < ⌈n/2⌉` (which holds
for all large `n`), no depth-`≤d`, width-`≤w` bounded-fan-in de Morgan circuit computes `MOD_q`. -/
theorem modq_not_computable_by_small_tree [Fintype F] [DecidableEq F] {q : ℕ} (ω : F)
    (hω : orderOf ω = q) (hq2 : 2 ≤ q) {d w : ℕ} (t : AndOrTree n)
    (hd : treeDepth t ≤ d) (hw : treeLeafWidth t ≤ w) (hn : 2 ^ d * w < n - n / 2)
    (hcomputes : AndOrTree.evalT F t = omegaFn ω (Finset.univ : Finset (Fin n))) : False := by
  have hlarge := andOrTree_computing_modq_large ω hω hq2 t hcomputes
  have hmono : 2 ^ treeDepth t * treeLeafWidth t ≤ 2 ^ d * w :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hd) hw
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameACC0

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.acc0_proxy_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameACC0.modq_not_computable_by_small_tree
