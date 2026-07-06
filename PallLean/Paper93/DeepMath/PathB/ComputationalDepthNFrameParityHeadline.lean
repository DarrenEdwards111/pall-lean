import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityAssembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSlotConnectivity

/-!
# N-Frame: the parity headline — the conditional `(2+c)N` conversion

Rung 29 of the arc (… → parity assembly → **parity headline**).  The final conversion:
essential variables from the detection machinery at the SINGLETON cut (a structural
simplification found in the design round: with `S = {p*}` everything else is probe-side, so
the liveness classes become PROVABLE and the essentiality witness pair is just the two mixes
of the assembled pair theorem), composed with the frozen `connectivity_fanout` ledger and the
assembled drag into the honest conditional headline.

  `parity_essential` — **PROVED**: any priced-shaped position with a per-target layout
        package is an ESSENTIAL variable of `parityFamilyBits` — in `connectivity_fanout`'s
        exact witness shape.  `hlive`/`hTautProbe` are DISCHARGED here (singleton cut).
  `parity_cbudget_conditional` — **PROVED, THE CONDITIONAL HEADLINE**: for every circuit
        computing `parityFamilyBits`, essential set `ESS`, and cut package with a drag
        supply:  `2·|ESS| + |V| ≤ length + 2`.  With `|ESS| = Θ(N)` (essential positions),
        `|V| = Θ(T) = Θ(N)` (Markov mass + kill-accounting at ratio `1 + c_d·d`), and
        `j ≤ coneExcess + 1` (the wire-extraction mirror), this reads
        `cbudget(sat3X⊕) ≥ 2N + Θ(N) = (2+c)N`.

## Honest scope — the named conditions

The headline is CONDITIONAL on exactly three deferred families of facts, all named:
(i) the codebook-enumeration hypotheses (`hcode*`, `hscaffold`, pin indices — discharged by
instantiating the explicit singleton+edge codebook); (ii) the liveness/kill-accounting at
REAL balanced cuts (`hlive`, `hTautProbe`, scaffold availability, `|V| = Θ(T)` — the
expander long-pole; the kill-cost scout lemmas and the counting-round constants are frozen
for it); (iii) the wire-extraction mirror for the parity family (`hj : j ≤ coneExcess + 1` —
the root-shape analogue, mechanical).  Honest claim: a restricted-model lower bound for an
explicit ⊕P-shaped family, conditional on (i)–(iii).  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityHeadline

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 3200000 in
/-- **The essential variables (proved)**: a priced-shaped position with a per-target layout
package is an essential variable of the parity family — via the assembled pair at the
SINGLETON cut, where the liveness classes are provable. -/
theorem parity_essential (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (RS : Finset (Fin m))
    (qstar : Fin m × Fin L)
    (pinIdxQ : Fin m → Fin L) (SCQ : Finset (Fin L))
    (jstarQ : Fin v) (bstarQ : ZMod 2) (KQ : Finset (Fin v)) (bvalQ : Fin v → ZMod 2)
    -- layout at the target
    (hVt : qstar.2 ≠ tautIdx)
    (hVRS : qstar.1 ∉ RS)
    (hcodeTaut : code tautIdx = tautLit v)
    (hcodeStar : code qstar.2 = (single v jstarQ, bstarQ))
    (hKstar : jstarQ ∉ KQ)
    (hpinCode : ∀ c ∈ RS, ∃ j' ∈ KQ, code (pinIdxQ c) = (single v j', bvalQ j' + 1))
    (hpinCover : ∀ j' ∈ KQ, ∃ c ∈ RS, code (pinIdxQ c) = (single v j', bvalQ j' + 1))
    (hSCQne : qstar.2 ∉ SCQ)
    (hSCQblock : ∀ i ∈ SCQ, i ≠ qstar.2)
    (hscaffoldQ : SCQ.image code
      = ((Finset.univ : Finset (Fin v)) \ insert jstarQ KQ).image
          (fun j' => ((single v j', (1 : ZMod 2)) : Lit v))) :
    ∃ x₁ x₀ : Fin N → Bool,
      (∀ b : Fin N, x₁ b ≠ x₀ b → b = xbit hfit qstar.1 qstar.2)
      ∧ parityFamilyBits code hfit x₁ ≠ parityFamilyBits code hfit x₀ := by
  classical
  set pstar : Fin N := xbit hfit qstar.1 qstar.2 with hpstar
  set S : Finset (Fin N) := {pstar} with hS
  set Vq : Finset (Fin m × Fin L) := {qstar} with hVq
  -- the two liveness classes are PROVABLE at the singleton cut
  have hTautProbe : ∀ q ∈ Vq, xbit hfit q.1 tautIdx ∈ Sᶜ := by
    intro q hq
    rw [hVq, Finset.mem_singleton] at hq
    subst hq
    rw [Finset.mem_compl, hS, Finset.mem_singleton]
    intro hcon
    exact hVt (xbit_inj hfit (hcon.symm ▸ rfl : xbit hfit q.1 tautIdx = pstar)).2.symm
  have hlive : ∀ q ∈ Vq, ∀ c ∈ RS, xbit hfit c (pinIdxQ c) ∈ Sᶜ := by
    intro q hq c hc
    rw [Finset.mem_compl, hS, Finset.mem_singleton]
    intro hcon
    have h1 := (xbit_inj hfit (hcon : xbit hfit c (pinIdxQ c) = pstar)).1
    apply hVRS
    rw [← h1]
    exact hc
  -- side placements
  have hVS : ∀ q ∈ Vq, xbit hfit q.1 q.2 ∉ Sᶜ := by
    intro q hq
    rw [hVq, Finset.mem_singleton] at hq
    subst hq
    rw [Finset.mem_compl, hS]
    intro hcon
    exact hcon (Finset.mem_singleton_self _)
  -- the pair via the assembled machinery
  have hpair := parity_assembled_pair code hfit tautIdx RS
    (∅ : Finset (Fin m × Fin L)) Vq S
    (fun _ => pinIdxQ) (fun _ => SCQ) (fun _ => jstarQ) (fun _ => bstarQ)
    (fun _ => KQ) (fun _ => bvalQ)
    (by
      intro q hq
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      exact hVt)
    (by
      intro q _
      exact Finset.notMem_empty q)
    (by
      intro q hq
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      exact hVRS)
    (by
      intro q hq
      exact absurd hq (Finset.notMem_empty q))
    hVS
    (by
      intro q hq
      exact absurd hq (Finset.notMem_empty q))
    hTautProbe
    hcodeTaut
    (by
      intro q hq
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      exact hcodeStar)
    (by
      intro q hq
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      exact hKstar)
    (by
      intro q hq i hi hne
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      rw [hVq, Finset.mem_singleton] at hi
      exfalso
      apply hne
      have := congrArg Prod.snd hi
      exact this)
    (by
      intro q hq
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      exact hpinCode)
    (by
      intro q hq
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      exact hpinCover)
    (by
      intro q hq
      rw [hVq, Finset.mem_singleton] at hq
      subst hq
      -- the row scaffold is empty; the probe scaffold filter keeps everything
      have hfilter : SCQ.filter (fun i => xbit hfit q.1 i ∈ Sᶜ) = SCQ := by
        apply Finset.filter_true_of_mem
        intro i hi
        rw [Finset.mem_compl, hS, Finset.mem_singleton]
        intro hcon
        exact (hSCQblock i hi)
          (xbit_inj hfit (hcon : xbit hfit q.1 i = pstar)).2
      have hscr : ((∅ : Finset (Fin m × Fin L)).filter
          (fun r => r.1 = q.1)).image Prod.snd = ∅ := by
        rw [Finset.filter_empty, Finset.image_empty]
      rw [hfilter, hscr, Finset.union_empty]
      exact hscaffoldQ)
    hlive
    (∅ : Finset (Fin m × Fin L)) Vq
    (Finset.empty_subset _) (Finset.Subset.refl _)
    qstar (Finset.mem_singleton_self _) (Finset.mem_singleton_self _)
    (Finset.notMem_empty _)
  -- package the essentiality witnesses
  refine ⟨mixOn Sᶜ (probeOn hfit tautIdx pinIdxQ SCQ
      ((Finset.univ \ RS).erase qstar.1) RS qstar.1)
      (rowOf hfit tautIdx RS ∅ Vq),
    mixOn Sᶜ (probeOn hfit tautIdx pinIdxQ SCQ
      ((Finset.univ \ RS).erase qstar.1) RS qstar.1)
      (rowOf hfit tautIdx RS ∅ (∅ : Finset (Fin m × Fin L))), ?_, ?_⟩
  · intro b hb
    by_cases hbmem : b ∈ Sᶜ
    · exfalso
      apply hb
      rw [mix_read_probe _ _ hbmem, mix_read_probe _ _ hbmem]
    · have : b ∈ S := by
        by_contra hcon
        exact hbmem (Finset.mem_compl.mpr hcon)
      rw [hS, Finset.mem_singleton] at this
      exact this
  · exact hpair.symm

set_option maxHeartbeats 1600000 in
/-- **THE CONDITIONAL HEADLINE (proved)**: for every circuit computing the parity family,
`2·|ESS| + |V| ≤ length + 2` — the `(2+c)N` conversion, conditional on the named
enumeration/liveness/extraction inputs. -/
theorem parity_cbudget_conditional (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (cc : List (CGate N))
    (hcomp : computes cc (parityFamilyBits code hfit))
    (ESS : Finset (Fin N))
    (hess : ∀ p ∈ ESS, ∃ x₁ x₀ : Fin N → Bool,
      (∀ b : Fin N, x₁ b ≠ x₀ b → b = p)
      ∧ parityFamilyBits code hfit x₁ ≠ parityFamilyBits code hfit x₀)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (parityFamilyBits code hfit) S j)
    (hj : j ≤ coneExcess cc (cc.length - 1) + 1)
    (tautIdx : Fin L) (RS : Finset (Fin m)) (SCR : Finset (Fin m × Fin L))
    (V : Finset (Fin m × Fin L))
    (pinIdxF : Fin m × Fin L → Fin m → Fin L)
    (SCF : Fin m × Fin L → Finset (Fin L))
    (jstarF : Fin m × Fin L → Fin v) (bstarF : Fin m × Fin L → ZMod 2)
    (KF : Fin m × Fin L → Finset (Fin v)) (bvalF : Fin m × Fin L → Fin v → ZMod 2)
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx)
    (hVSCR : ∀ q ∈ V, q ∉ SCR)
    (hVRS : ∀ q ∈ V, q.1 ∉ RS)
    (hSCRRS : ∀ q ∈ SCR, q.1 ∉ RS)
    (hVS : ∀ q ∈ V, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hSCRS : ∀ q ∈ SCR, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hTautProbe : ∀ q ∈ V, xbit hfit q.1 tautIdx ∈ Sᶜ)
    (hcodeTaut : code tautIdx = tautLit v)
    (hcodeStar : ∀ q ∈ V, code q.2 = (single v (jstarF q), bstarF q))
    (hKstar : ∀ q ∈ V, jstarF q ∉ KF q)
    (hcodeV : ∀ q ∈ V, ∀ i : Fin L, (q.1, i) ∈ V → i ≠ q.2 →
      ∃ j' ∈ KF q, code i = (single v j', bvalF q j'))
    (hpinCode : ∀ q ∈ V, ∀ c ∈ RS,
      ∃ j' ∈ KF q, code (pinIdxF q c) = (single v j', bvalF q j' + 1))
    (hpinCover : ∀ q ∈ V, ∀ j' ∈ KF q,
      ∃ c ∈ RS, code (pinIdxF q c) = (single v j', bvalF q j' + 1))
    (hscaffold : ∀ q ∈ V,
      (((SCF q).filter (fun i => xbit hfit q.1 i ∈ Sᶜ))
        ∪ (SCR.filter (fun r => r.1 = q.1)).image Prod.snd).image code
      = ((Finset.univ : Finset (Fin v)) \ insert (jstarF q) (KF q)).image
          (fun j' => ((single v j', (1 : ZMod 2)) : Lit v)))
    (hlive : ∀ q ∈ V, ∀ c ∈ RS, xbit hfit c (pinIdxF q c) ∈ Sᶜ) :
    2 * ESS.card + V.card ≤ cc.length + 2 := by
  have hfan := connectivity_fanout (parityFamilyBits code hfit) ESS hess cc hcomp
  have hdrag := parity_assembled_drag code hfit tautIdx RS SCR V hcut
    pinIdxF SCF jstarF bstarF KF bvalF
    hVt hVSCR hVRS hSCRRS hVS hSCRS hTautProbe
    hcodeTaut hcodeStar hKstar hcodeV hpinCode hpinCover hscaffold hlive
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameParityHeadline

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityHeadline.parity_essential
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityHeadline.parity_cbudget_conditional
