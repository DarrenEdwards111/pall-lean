import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BeigelTaruiSparsity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Multilinearisation

/-!
# The RS agreement/error bound for the approximant — the correctness half, assembled

Entry 176 proved the *size* half of the BT residual `hSize` (the RS approximant has quasipolynomial `SYM∘AND` size) and
named the **correctness/error** half as residual (1): that the bounded-size `SYM∘AND` actually *computes* (or
`1/poly`-approximates) the circuit.  This file discharges that half for the AC⁰[p] route by assembling the repo's
proved agreement machinery into the **complete RS Beigel–Tarui representation** of the agreement-side approximant
`toAgree` (`…Layer3.toAgree`): low degree **and** quasipoly count **and** bounded error, together, for one form choice.

The two ingredients are both already proved in `…Layer3`:

* **degree** — `…Layer3.toAgree_totalDegree_le : (toAgree p t R C).totalDegree ≤ ((p−1)·t)^{depth}` (any form `R`);
* **error** — `…Layer3.composed_error_le`: for an AC⁰[p] circuit (every `MOD` gate has `q = p`), there is a form choice
  `ω` whose approximant `toAgree (oracleOf p t C ω) C` disagrees with the circuit on a set of size `s` with
  `s · p^t ≤ (#subcircuits) · 2^n` — the Razborov–Smolensky agreement guarantee, error rate `≤ (#subcircuits)·p^{-t}`.

This file bundles them (with the entry-173 sparse count) into a single theorem.

## What is proved (clean axioms, no `sorry`)

* **`rs_agreement_BT`** — for an AC⁰[p] circuit `C`, there is a form choice `ω` such that the approximant
  `toAgree p t (oracleOf p t C ω) C` simultaneously has (a) total degree `≤ ((p−1)·t)^{depth}`, (b) `SYM∘AND` size
  (distinct `AND`-features) `≤ (n+1)^{((p−1)·t)^{depth}}`, and (c) error `· p^t ≤ (#subcircuits)·2^n`.  The complete RS
  BT representation — low degree, quasipoly size, bounded error — together.

## Honest scope

This discharges the **correctness/error half** (residual (1) of entry 176) for the AC⁰[p] / prime route, by assembling
the proved `composed_error_le` (the full RS agreement guarantee) with the proved degree bound and the sparse count.
So for AC⁰[p] circuits the RS approximant has a *genuinely complete* BT representation: low degree, quasipoly size, and
small error, all proved together.  The remaining residual is purely (2): **composite / prime-power modulus** — the
prime-`p` agreement (`composed_error_le`'s `hmod : every MOD gate has q = p`) covers only `MOD_p`; squarefree composite
runs per prime over `∏ F_p` (entry 171), and prime-power `MOD` uses the exact mixed-radix `SYM∘AND` (entry 174) whose
quasipoly size is the BT mixed-radix analysis.  Beigel–Tarui and `NEXP ⊄ ACC⁰` (Williams 2011) are proven classical
theorems ⇒ formalisation, not an open problem.  NOT a new separation, NOT `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RSAgreementBound

open scoped Classical
open MvPolynomial Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0BeigelTaruiSparsity (beigelTarui_monomial_count_le)
open PallLean.Paper93.DeepMath.PathB.ACC0Multilinearisation (support_mem_lowDeg)

/-- **The complete RS Beigel–Tarui representation (proved): degree + quasipoly size + bounded error, together.**  For
an AC⁰[p] circuit `C` (every `MOD` gate has modulus `p`), there is a form choice `ω` such that the Razborov–Smolensky
approximant `toAgree p t (oracleOf p t C ω) C` simultaneously has:
* **(a) low degree** — `≤ ((p−1)·t)^{depth}` (polylog for polylog `t`, constant depth);
* **(b) quasipoly `SYM∘AND` size** — `≤ (n+1)^{((p−1)·t)^{depth}}` distinct `AND`-features;
* **(c) bounded error** — disagrees with the circuit on a set of size `s` with `s · p^t ≤ (#subcircuits)·2^n` (error
  rate `≤ (#subcircuits)·p^{-t}`).

This is the correctness half of the BT residual: the bounded-size, low-degree `SYM∘AND` genuinely `1/poly`-approximates
the circuit (`composed_error_le`), bundled with the degree (`toAgree_totalDegree_le`) and sparse count
(`beigelTarui_monomial_count_le`). -/
theorem rs_agreement_BT (p t : ℕ) [Fact p.Prime] {n : ℕ} (ht : 1 ≤ t) (C : BoolCircuitSyntax n)
    (hmod : ∀ q r cs, (BoolCircuitSyntax.modGate q r cs : BoolCircuitSyntax n) ∈ subcircuits C → q = p) :
    ∃ ω : FormSpace p t C,
      (toAgree p t (oracleOf p t C ω) C).totalDegree ≤ ((p - 1) * t) ^ C.depth
      ∧ ((toAgree p t (oracleOf p t C ω) C).support.image (fun d => d.support)).card
          ≤ (n + 1) ^ (((p - 1) * t) ^ C.depth)
      ∧ (Finset.univ.filter (fun x : Fin n → Bool =>
            eval (fun i => boolToZMod p (x i)) (toAgree p t (oracleOf p t C ω) C)
              ≠ boolToZMod p (C.eval x))).card * p ^ t
          ≤ (subcircuits C).toFinset.card * Fintype.card (Fin n → Bool) := by
  obtain ⟨ω, herr⟩ := composed_error_le p t C hmod
  refine ⟨ω, toAgree_totalDegree_le p t ht _ C, ?_, herr⟩
  refine le_trans (Finset.card_le_card ?_) (beigelTarui_monomial_count_le n (((p - 1) * t) ^ C.depth))
  intro S hS
  rw [Finset.mem_image] at hS
  obtain ⟨d, hd, rfl⟩ := hS
  exact support_mem_lowDeg _ (toAgree_totalDegree_le p t ht _ C) hd

end PallLean.Paper93.DeepMath.PathB.ACC0RSAgreementBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RSAgreementBound.rs_agreement_BT
