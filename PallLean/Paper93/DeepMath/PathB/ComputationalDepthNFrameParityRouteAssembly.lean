import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityRouteThread

/-!
# N-Frame: the route assembly — the drag with edge-mediated pins

Expander-discharge arc, rung E2b (… → route thread → **route assembly**).  The
route-general mirror of rung 28g: the SAME row family (`rowOf`) and its proved reads, the
SAME probe, and the assembled drag — with the pin layout generalized from complement
singletons to ROUTES (per-target route assignments `rF`, direct or edge with
scaffold-covered companions).  Everything except the two pin-layout hypotheses is verbatim
28g; the composition now goes through `parity_pair_dist_route`.

  `parity_route_pair` — **PROVED**: tuples differing at a target are distinguished by the
        constructed probe, with route-coded pins.
  `parity_route_drag` — **PROVED, THE ROUTE DRAG**: under a cut factorization of the parity
        family, `V.card ≤ j` — the E5 kill-accounting's consumption point: at a real cut
        the designer may route each priced coordinate through whichever selector column
        (direct or edge) survives, which is what makes the kill cost the full
        incident-edge-column mass.
  `parity_route_drag_direct` — **PROVED, THE SPECIALIZATION CHECK**: the all-direct route
        instantiation reproduces `parity_assembled_drag`'s exact hypothesis shape — the
        re-threading strictly generalizes rung 28g.

The two NAMED liveness classes (`hlive`, `hTautProbe`) keep their exact 28g shape; under
the ratified circulant framing their discharge (E5) needs only the explicit graph layer
(E4), no spectral input.

## Honest scope

Remaining: the extended codebook with edge columns (E3), the circulant layer (E4), the
kill-accounting at real cuts (E5), the headline (E6).  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityRouteAssembly

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParitySupply
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityDrag
open PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly
open PallLean.Paper93.DeepMath.PathB.NFrameParityRouteSupply
open PallLean.Paper93.DeepMath.PathB.NFrameParityRouteThread
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 3200000 in
/-- **The route pair (proved)**: tuples differing at a target are distinguished by the
constructed probe — the full composition through the route-threaded discharge. -/
theorem parity_route_pair (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (RS : Finset (Fin m)) (SCR : Finset (Fin m × Fin L))
    (V : Finset (Fin m × Fin L)) (S : Finset (Fin N))
    -- per-target supply data (functions over targets)
    (pinIdxF : Fin m × Fin L → Fin m → Fin L)
    (SCF : Fin m × Fin L → Finset (Fin L))
    (jstarF : Fin m × Fin L → Fin v) (bstarF : Fin m × Fin L → ZMod 2)
    (KF : Fin m × Fin L → Finset (Fin v)) (bvalF : Fin m × Fin L → Fin v → ZMod 2)
    (rF : Fin m × Fin L → Fin v → Lit v)
    -- the per-target route assignments
    (hrF : ∀ q ∈ V, RouteAssignment v (jstarF q) (KF q) (bvalF q) (rF q))
    -- positional discipline
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx)
    (hVSCR : ∀ q ∈ V, q ∉ SCR)
    (hVRS : ∀ q ∈ V, q.1 ∉ RS)
    (hSCRRS : ∀ q ∈ SCR, q.1 ∉ RS)
    (hVS : ∀ q ∈ V, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hSCRS : ∀ q ∈ SCR, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hTautProbe : ∀ q ∈ V, xbit hfit q.1 tautIdx ∈ Sᶜ)
    -- codebook layout
    (hcodeTaut : code tautIdx = tautLit v)
    (hcodeStar : ∀ q ∈ V, code q.2 = (single v (jstarF q), bstarF q))
    (hKstar : ∀ q ∈ V, jstarF q ∉ KF q)
    (hcodeV : ∀ q ∈ V, ∀ i : Fin L, (q.1, i) ∈ V → i ≠ q.2 →
      ∃ j ∈ KF q, code i = (single v j, bvalF q j))
    (hpinCode : ∀ q ∈ V, ∀ c ∈ RS,
      ∃ j ∈ KF q, code (pinIdxF q c) = rF q j)
    (hpinCover : ∀ q ∈ V, ∀ j ∈ KF q,
      ∃ c ∈ RS, code (pinIdxF q c) = rF q j)
    (hscaffold : ∀ q ∈ V,
      (((SCF q).filter (fun i => xbit hfit q.1 i ∈ Sᶜ))
        ∪ (SCR.filter (fun r => r.1 = q.1)).image Prod.snd).image code
      = ((Finset.univ : Finset (Fin v)) \ insert (jstarF q) (KF q)).image
          (fun j => ((single v j, (1 : ZMod 2)) : Lit v)))
    -- THE LIVENESS CLASS
    (hlive : ∀ q ∈ V, ∀ c ∈ RS, xbit hfit c (pinIdxF q c) ∈ Sᶜ)
    -- the pair
    (E E' : Finset (Fin m × Fin L)) (hE : E ⊆ V) (hE' : E' ⊆ V)
    (q₀ : Fin m × Fin L) (hq₀V : q₀ ∈ V) (hq₀E' : q₀ ∈ E') (hq₀E : q₀ ∉ E) :
    parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1)
        (rowOf hfit tautIdx RS SCR E))
    ≠ parityFamilyBits code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1)
        (rowOf hfit tautIdx RS SCR E')) := by
  classical
  set KB : Finset (Fin m) := (Finset.univ \ RS).erase q₀.1 with hKB
  have hq₀RS : q₀.1 ∉ RS := hVRS q₀ hq₀V
  apply parity_pair_dist_route code hfit tautIdx (pinIdxF q₀) (SCF q₀)
    KB RS q₀.1 q₀.2 S
    (rowOf hfit tautIdx RS SCR E) (rowOf hfit tautIdx RS SCR E')
    E E' ((SCR.filter (fun r => r.1 = q₀.1)).image Prod.snd)
    (jstarF q₀) (bstarF q₀) (KF q₀) (bvalF q₀) (rF q₀)
    (hrF q₀ hq₀V)
    hcodeTaut
    (by
      have h := hcodeStar q₀ hq₀V
      exact h)
    (hKstar q₀ hq₀V)
    (by
      intro i hi
      have hne : i ≠ q₀.2 := by
        intro hcon
        apply hq₀E
        have : ((q₀.1, i) : Fin m × Fin L) = q₀ := by
          rw [hcon]
        rw [← this]
        exact hi
      exact hcodeV q₀ hq₀V i (hE hi) hne)
    (by
      intro i hi hne
      exact hcodeV q₀ hq₀V i (hE' hi) hne)
    (hpinCode q₀ hq₀V)
    (hpinCover q₀ hq₀V)
    (hscaffold q₀ hq₀V)
    (by
      intro c hc
      by_cases hcRS : c ∈ RS
      · exact Or.inr hcRS
      · exact Or.inl (Finset.mem_erase.mpr ⟨hc,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcRS⟩⟩))
    (by
      intro c hc
      intro hcKB
      have := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hcKB)).2
      exact this hc)
    (by
      intro hcon
      exact (Finset.ne_of_mem_erase hcon) rfl)
    hq₀RS
    (hlive q₀ hq₀V)
    (by
      intro c hc
      have hcRS : c ∉ RS := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hc)).2
      exact rowOf_read_kit hfit tautIdx RS SCR E hcRS)
    (by
      intro c hc
      have hcRS : c ∉ RS := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hc)).2
      exact rowOf_read_kit hfit tautIdx RS SCR E' hcRS)
    (by
      intro c hc i
      exact rowOf_read_reserve hfit tautIdx RS SCR V hVRS hSCRRS E hE hc i)
    (by
      intro c hc i
      exact rowOf_read_reserve hfit tautIdx RS SCR V hVRS hSCRRS E' hE' hc i)
    (by
      intro i hi
      exact hVS (q₀.1, i) (hE hi))
    (by
      intro i hi
      exact hVS (q₀.1, i) (hE' hi))
    (by
      intro i hi
      obtain ⟨q', hq', hsnd⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_filter] at hq'
      have := hSCRS q' hq'.1
      rw [hq'.2, hsnd] at this
      exact this)
    (by
      intro i hi
      exact rowOf_read_target hfit tautIdx RS SCR V S hVt E hE
        (hTautProbe q₀ hq₀V) i hi)
    (by
      intro i hi
      exact rowOf_read_target hfit tautIdx RS SCR V S hVt E' hE'
        (hTautProbe q₀ hq₀V) i hi)
    (by
      show ((q₀.1, q₀.2) : Fin m × Fin L) ∈ E'
      rw [show ((q₀.1, q₀.2) : Fin m × Fin L) = q₀ from rfl]
      exact hq₀E')

set_option maxHeartbeats 3200000 in
/-- **THE ROUTE DRAG (proved)**: under a cut factorization of the parity family,
`V.card ≤ j` — with route-coded pins; the E5 kill-accounting's consumption point. -/
theorem parity_route_drag (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (RS : Finset (Fin m)) (SCR : Finset (Fin m × Fin L))
    (V : Finset (Fin m × Fin L))
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (parityFamilyBits code hfit) S j)
    (pinIdxF : Fin m × Fin L → Fin m → Fin L)
    (SCF : Fin m × Fin L → Finset (Fin L))
    (jstarF : Fin m × Fin L → Fin v) (bstarF : Fin m × Fin L → ZMod 2)
    (KF : Fin m × Fin L → Finset (Fin v)) (bvalF : Fin m × Fin L → Fin v → ZMod 2)
    (rF : Fin m × Fin L → Fin v → Lit v)
    (hrF : ∀ q ∈ V, RouteAssignment v (jstarF q) (KF q) (bvalF q) (rF q))
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
      ∃ j' ∈ KF q, code (pinIdxF q c) = rF q j')
    (hpinCover : ∀ q ∈ V, ∀ j' ∈ KF q,
      ∃ c ∈ RS, code (pinIdxF q c) = rF q j')
    (hscaffold : ∀ q ∈ V,
      (((SCF q).filter (fun i => xbit hfit q.1 i ∈ Sᶜ))
        ∪ (SCR.filter (fun r => r.1 = q.1)).image Prod.snd).image code
      = ((Finset.univ : Finset (Fin v)) \ insert (jstarF q) (KF q)).image
          (fun j' => ((single v j', (1 : ZMod 2)) : Lit v)))
    (hlive : ∀ q ∈ V, ∀ c ∈ RS, xbit hfit c (pinIdxF q c) ∈ Sᶜ) :
    V.card ≤ j := by
  classical
  apply parity_tuple_drag code hfit hcut V (rowOf hfit tautIdx RS SCR)
  · intro E hE q hq
    exact rowOf_read_V hfit tautIdx RS SCR V hVt hVSCR E
      (Finset.mem_powerset.mp hE) hq
  · intro E hE E' hE' hne
    have hEsub := Finset.mem_powerset.mp hE
    have hE'sub := Finset.mem_powerset.mp hE'
    -- a differing position exists
    have hdiff : ∃ q, (q ∈ E' ∧ q ∉ E) ∨ (q ∈ E ∧ q ∉ E') := by
      by_contra hcon
      push_neg at hcon
      apply hne
      ext q
      have h := hcon q
      constructor
      · intro hq
        exact h.2 hq
      · intro hq
        exact h.1 hq
    obtain ⟨q₀, hcase⟩ := hdiff
    rcases hcase with ⟨hq₀E', hq₀E⟩ | ⟨hq₀E, hq₀E'⟩
    · have hq₀V : q₀ ∈ V := hE'sub hq₀E'
      exact ⟨probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1,
        parity_route_pair code hfit tautIdx RS SCR V S
          pinIdxF SCF jstarF bstarF KF bvalF rF hrF
          hVt hVSCR hVRS hSCRRS hVS hSCRS hTautProbe
          hcodeTaut hcodeStar hKstar hcodeV hpinCode hpinCover hscaffold hlive
          E E' hEsub hE'sub q₀ hq₀V hq₀E' hq₀E⟩
    · have hq₀V : q₀ ∈ V := hEsub hq₀E
      refine ⟨probeOn hfit tautIdx (pinIdxF q₀) (SCF q₀)
        ((Finset.univ \ RS).erase q₀.1) RS q₀.1, ?_⟩
      exact (parity_route_pair code hfit tautIdx RS SCR V S
        pinIdxF SCF jstarF bstarF KF bvalF rF hrF
        hVt hVSCR hVRS hSCRRS hVS hSCRS hTautProbe
        hcodeTaut hcodeStar hKstar hcodeV hpinCode hpinCover hscaffold hlive
        E' E hE'sub hEsub q₀ hq₀V hq₀E hq₀E').symm

set_option maxHeartbeats 1600000 in
/-- **THE SPECIALIZATION CHECK (proved)**: the all-direct route instantiation reproduces
`parity_assembled_drag`'s exact hypothesis shape — the re-threading strictly generalizes
rung 28g. -/
theorem parity_route_drag_direct (code : Fin L → Lit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (RS : Finset (Fin m)) (SCR : Finset (Fin m × Fin L))
    (V : Finset (Fin m × Fin L))
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (parityFamilyBits code hfit) S j)
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
    V.card ≤ j := by
  apply parity_route_drag code hfit tautIdx RS SCR V hcut
    pinIdxF SCF jstarF bstarF KF bvalF
    (fun q => fun j' => ((single v j', bvalF q j' + 1) : Lit v))
    (fun q _ => direct_routes_are_routes v (jstarF q) (KF q) (bvalF q))
    hVt hVSCR hVRS hSCRRS hVS hSCRS hTautProbe
    hcodeTaut hcodeStar hKstar hcodeV hpinCode hpinCover hscaffold hlive

end PallLean.Paper93.DeepMath.PathB.NFrameParityRouteAssembly

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityRouteAssembly.parity_route_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityRouteAssembly.parity_route_drag
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityRouteAssembly.parity_route_drag_direct
