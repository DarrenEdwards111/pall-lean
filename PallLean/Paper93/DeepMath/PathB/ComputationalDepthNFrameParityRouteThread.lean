import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityRouteSupply

/-!
# N-Frame: the route thread — the generalized supply wired into the pair discharge

Expander-discharge arc, rung E2a (… → route supply → **route thread**).  The route-general
mirror of rung 28e: the `route_supply` package is threaded into every linear slot of the
rung-28c pair discharge.  The ONLY change against `parity_pair_dist_singleton` is the pin
layout: the pins code ROUTES (`code (pinIdx c) = r j` — direct complement singletons or
edge literals with scaffold-covered companions) instead of complement singletons; the
target and the priced companions remain singleton-coded, and every other hypothesis is
verbatim.  Rung 28c (`parity_pair_dist`) was already pin-literal-generic — the pins enter
it only through `litHolds a (code (pinIdx c))` — so no re-proof of the pair machinery is
needed, only the re-threading.

  `parity_pair_dist_route` — **PROVED, THE ROUTE-THREADED DISCHARGE**: layout + structure +
        liveness + row design ⇒ the two tuple rows' mixes get DIFFERENT family values, with
        `(w, a₀)` supplied by `route_supply` — no linear hypotheses remain, edge-mediated
        pins admitted.

## Honest scope

The circulant framing (ratified): the critical Lean path uses an explicit
circulant/elementary graph; Ramanujan remains the flagship/canonical upgrade — the proof
interface never needed spectral optimality, only enough certified incident-edge mass.
Remaining: the route assembly (E2b), the extended codebook (E3), the graph layer (E4), the
kill-accounting (E5), the headline (E6).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityRouteThread

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParitySupply
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **THE ROUTE-THREADED DISCHARGE (proved)**: the generalized supply package wired into
every linear slot of the pair discharge — pins may be direct complement singletons or edge
literals with scaffold-covered companions. -/
theorem parity_pair_dist_route (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar : Fin m) (istar : Fin L)
    (S : Finset (Fin N)) (y y' : Fin N → Bool)
    (E E' : Finset (Fin m × Fin L)) (SCrow : Finset (Fin L))
    (jstar : Fin v) (bstar : ZMod 2) (K : Finset (Fin v)) (bval : Fin v → ZMod 2)
    (r : Fin v → Lit v)
    -- the route assignment
    (hroute : RouteAssignment v jstar K bval r)
    -- codebook layout at the relevant indices
    (hcodeTaut : code tautIdx = tautLit v)
    (hcodeStar : code istar = (single v jstar, bstar))
    (hKstar : jstar ∉ K)
    (hcodeE : ∀ i : Fin L, (cstar, i) ∈ E → ∃ j ∈ K, code i = (single v j, bval j))
    (hcodeE' : ∀ i : Fin L, (cstar, i) ∈ E' → i ≠ istar →
      ∃ j ∈ K, code i = (single v j, bval j))
    (hpinCode : ∀ c ∈ PB, ∃ j ∈ K, code (pinIdx c) = r j)
    (hpinCover : ∀ j ∈ K, ∃ c ∈ PB, code (pinIdx c) = r j)
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
  obtain ⟨w, a₀, hs1, hs2, hs2b, hs3, hs4, hs5, hs6⟩ :=
    route_supply v jstar bstar K hKstar bval r hroute
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
  -- hwE (the priced companions are singleton-coded: the singleton kernels)
  · intro i hi
    obtain ⟨j, hjK, hci⟩ := hcodeE i hi
    rw [hci]
    exact hs2b j hjK
  -- hpairPin (the pins are route-coded: the route ↔)
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

end PallLean.Paper93.DeepMath.PathB.NFrameParityRouteThread

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityRouteThread.parity_pair_dist_route
