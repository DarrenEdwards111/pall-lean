import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityCodebook

/-!
# N-Frame: the parity thread — the supply wired into the pair discharge

Rung 28e of the arc (… → parity codebook → **parity thread**).  The explicit
`singleton_supply` package is threaded into every linear slot of the rung-28c pair
discharge, through codebook-layout hypotheses: the target position codes a singleton
literal, the pair's other priced positions code singleton literals on the dedup'd
coordinate set `K`, the pins code the complements, and the effective scaffold codes the
remaining coordinates at value `1`.

  `parity_pair_dist_singleton` — **PROVED, THE THREADED DISCHARGE**: layout + structure +
        liveness + row design ⇒ the two tuple rows' mixes get DIFFERENT family values,
        with `(w, a₀)` supplied by `singleton_supply` — no linear hypotheses remain.

## Honest scope

The hypotheses now split cleanly by provenance: LAYOUT (`hcode*`, `hscaffold` — discharged
by the codebook enumeration at assembly time), STRUCTURE/ROW DESIGN (discharged by the row
family construction), and LIVENESS (`hlive` — the expander-dependent slot, kept
hypothetical per the skeleton-first plan).  Remaining: the Markov mass theorem, the
assembly of the drag over these pieces, and rung 29.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityThread

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParitySupply
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **THE THREADED DISCHARGE (proved)**: the explicit supply package wired into every linear
slot of the pair discharge — layout + structure + liveness + row design suffice. -/
theorem parity_pair_dist_singleton (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m) (istar : Fin L)
    (S : Finset (Fin N)) (y y' : Fin N → Bool)
    (E E' : Finset (Fin m × Fin L)) (SCrow : Finset (Fin L))
    (jstar : Fin v) (bstar : ZMod 2) (K : Finset (Fin v)) (bval : Fin v → ZMod 2)
    -- codebook layout at the relevant indices
    (hcodeTaut : code tautIdx = tautLit v)
    (hcodeStar : code istar = (single v jstar, bstar))
    (hKstar : jstar ∉ K)
    (hcodeE : ∀ i : Fin L, (cstar, i) ∈ E → ∃ j ∈ K, code i = (single v j, bval j))
    (hcodeE' : ∀ i : Fin L, (cstar, i) ∈ E' → i ≠ istar →
      ∃ j ∈ K, code i = (single v j, bval j))
    (hpinCode : ∀ c ∈ PB, ∃ j ∈ K, code (pinIdx c) = (single v j, bval j + 1))
    (hpinCover : ∀ j ∈ K, ∃ c ∈ PB, code (pinIdx c) = (single v j, bval j + 1))
    (hscaffold : ((SC.filter (fun i => xbit hfit cstar i ∈ Sᶜ)) ∪ SCrow).image code
      = ((Finset.univ : Finset (Fin v)) \ insert jstar K).image
          (fun j => ((single v j, (1 : ZMod 2)) : Lit v)))
    -- structure and liveness
    (hcover : ∀ c, c ≠ cstar → c ∈ KB ∨ c ∈ PB)
    (hKP : ∀ c ∈ PB, c ∉ KB)
    (hKnc : cstar ∉ KB)
    (hPnc : cstar ∉ PB)
    (hlive : ∀ c ∈ PB, xbit hfit c (pinIdx c) ∈ Sᶜ)
    -- row design
    (hyKit : ∀ c ∈ KB, y (xbit hfit c tautIdx) = true)
    (hyKit' : ∀ c ∈ KB, y' (xbit hfit c tautIdx) = true)
    (hyPin : ∀ c ∈ PB, ∀ i : Fin L, y (xbit hfit c i) = false)
    (hyPin' : ∀ c ∈ PB, ∀ i : Fin L, y' (xbit hfit c i) = false)
    (hEside : ∀ i : Fin L, (cstar, i) ∈ E → xbit hfit cstar i ∉ Sᶜ)
    (hE'side : ∀ i : Fin L, (cstar, i) ∈ E' → xbit hfit cstar i ∉ Sᶜ)
    (hSCrow : ∀ i ∈ SCrow, xbit hfit cstar i ∉ Sᶜ)
    (hyE : ∀ i : Fin L, xbit hfit cstar i ∉ Sᶜ →
      (y (xbit hfit cstar i) = true ↔ ((cstar, i) ∈ E ∨ i ∈ SCrow)))
    (hyE' : ∀ i : Fin L, xbit hfit cstar i ∉ Sᶜ →
      (y' (xbit hfit cstar i) = true ↔ ((cstar, i) ∈ E' ∨ i ∈ SCrow)))
    -- the target
    (htarE' : (cstar, istar) ∈ E') :
    parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y)
    ≠ parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar) y') := by
  classical
  obtain ⟨w, a₀, hs1, hs2, hs3, hs4, hs5, hs6⟩ :=
    singleton_supply v jstar bstar K hKstar bval
  apply parity_pair_dist code hfit tautIdx pinIdx SC KB PB cstar istar S y y'
    E E' SCrow w a₀ hcodeTaut hcover hKP hKnc hPnc hlive
    hyKit hyKit' hyPin hyPin' hEside hE'side hSCrow hyE hyE' htarE'
  -- hlw
  · rw [hcodeStar]
    exact hs1
  -- ha₀E
  · intro i hi
    obtain ⟨j, hjK, hci⟩ := hcodeE i hi
    rw [hci]
    exact hs4 j hjK
  -- ha₀E'
  · intro i hi
    by_cases his : i = istar
    · subst his
      rw [hcodeStar]
      exact hs3
    · obtain ⟨j, hjK, hci⟩ := hcodeE' i hi his
      rw [hci]
      exact hs4 j hjK
  -- hwE
  · intro i hi
    obtain ⟨j, hjK, hci⟩ := hcodeE i hi
    rw [hci]
    exact hs2 j hjK
  -- hpairPin
  · intro a
    rw [hscaffold]
    constructor
    · rintro ⟨hp, hsc⟩
      apply (hs6 a).mp
      constructor
      · intro j hjK
        obtain ⟨c, hcPB, hcode⟩ := hpinCover j hjK
        have h := hp c hcPB
        rw [hcode] at h
        exact h
      · intro j hjK hjs
        apply hsc
        apply Finset.mem_image_of_mem
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hcon
        rcases Finset.mem_insert.mp hcon with h | h
        · exact hjs h
        · exact hjK h
    · intro h
      obtain ⟨hpins, hscaf⟩ := (hs6 a).mpr h
      constructor
      · intro c hcPB
        obtain ⟨j, hjK, hcode⟩ := hpinCode c hcPB
        rw [hcode]
        exact hpins j hjK
      · intro ℓ hℓ
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hℓ
        rw [Finset.mem_sdiff] at hj
        have hjs : j ≠ jstar := fun hcon =>
          hj.2 (Finset.mem_insert.mpr (Or.inl hcon))
        have hjK : j ∉ K := fun hcon =>
          hj.2 (Finset.mem_insert.mpr (Or.inr hcon))
        exact hscaf j hjK hjs

end PallLean.Paper93.DeepMath.PathB.NFrameParityThread

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityThread.parity_pair_dist_singleton
