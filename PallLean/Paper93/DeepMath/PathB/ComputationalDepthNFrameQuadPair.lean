import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameQuadTarget

/-!
# N-Frame: the discharged quadratic drag — `gParity_quad_pair` fed to `gParity_tuple_drag`

Route H drag rung (… → target decode → **discharged drag**).  The final composition: the
per-pair distinguishing on the concrete `rowOf`/`probeOn` construction, and the drag it feeds.
All reads are now in hand — kit blanket, reserve identity, origin cut, target decode — and
this threads them through the multi-difference engine.

  `gParity_quad_pair` — **PROVED, THE DISCHARGED PAIR**: on the concrete construction, two
        tuples whose target-block restrictions are `∅` and `{istar}` get different family
        parities — the per-pair `hdist` of `gParity_tuple_drag`, discharged.
  `gParity_quad_drag` — **PROVED, THE DISCHARGED DRAG**: with one priced position per block,
        the product tuple family prices `V.card ≤ j` against a cut factorization — the
        quadratic drag run on the explicit `rowOf`/`probeOn` construction.

## Honest scope — what this closes (Route H)

`gParity_quad_drag` runs the multi-difference quadratic drag end to end on the concrete
construction: `V.card ≤ j` follows from a cut factorization, given the placement hypotheses
(`hTautProbe`/`hlive`/`hpos`, which positions the cut puts on which side) and the scaffold
realization (the codebook maps the target's ON positions to the off-support scaffold).  The
placement class is exactly the concentration-conditional assumption.  The concentration
analysis at the raised local rank — whether the priced mass `|V|` is `Θ(N)` at a real balanced
cut — is the open gate.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadPair

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameParityFlipScout
open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityProbe
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityAssembly
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTwoPoint
open PallLean.Paper93.DeepMath.PathB.NFrameQuadLayout
open PallLean.Paper93.DeepMath.PathB.NFrameQuadAssembly
open PallLean.Paper93.DeepMath.PathB.NFrameQuadSupply
open PallLean.Paper93.DeepMath.PathB.NFrameQuadHpair
open PallLean.Paper93.DeepMath.PathB.NFrameQuadRowOf
open PallLean.Paper93.DeepMath.PathB.NFrameQuadTarget
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {v m L N : ℕ}

set_option maxHeartbeats 3200000 in
/-- **THE DISCHARGED PAIR (proved)**: on the concrete construction, two tuples whose
target-block restrictions are `∅` and `{istar}` get different family parities. -/
theorem gParity_quad_pair (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (KB PB : Finset (Fin m)) (cstar c₀ : Fin m) (istar : Fin L) (i j : Fin v) (hij : i ≠ j)
    (S : Finset (Fin N)) (V E E' : Finset (Fin m × Fin L))
    (hcodeTaut : code tautIdx = GLit.aff 0 0)
    (hcode : code istar = GLit.quad i j 1)
    (hpinCode : ∀ c, c ∈ PB → code (pinIdx c) = GLit.aff (single v i + single v j) 0)
    (hcover : ∀ c, c ≠ cstar → c ∈ KB ∨ c ∈ PB)
    (hKP : ∀ c, c ∈ PB → c ∉ KB) (hKnc : cstar ∉ KB) (hPnc : cstar ∉ PB)
    (hc₀ : c₀ ∈ PB)
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx) (hVRS : ∀ q ∈ V, q.1 ∉ PB)
    (hE : E ⊆ V) (hE' : E' ⊆ V)
    (hEcstar : ∀ k, (cstar, k) ∉ E)
    (hE'sel : Finset.univ.filter (fun k => (cstar, k) ∈ E') = {istar})
    (hTautProbe : xbit hfit cstar tautIdx ∈ Sᶜ)
    (hlive : ∀ c, c ∈ PB → xbit hfit c (pinIdx c) ∈ Sᶜ)
    (hpos : xbit hfit cstar istar ∉ Sᶜ)
    (hScaf : (((SC.filter (fun k => xbit hfit cstar k ∈ Sᶜ))
        ∪ ((∅ : Finset (Fin m × Fin L)).filter (fun r => r.1 = cstar)).image Prod.snd)
        ∪ (Finset.univ.filter (fun k => (cstar, k) ∈ E))).image code
      = (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1)) :
    gParityFamilyBits code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
          (rowOf hfit tautIdx PB ∅ E))
      ≠ gParityFamilyBits code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
          (rowOf hfit tautIdx PB ∅ E')) := by
  classical
  have hc₀cs : c₀ ≠ cstar := fun h => hPnc (h ▸ hc₀)
  set SCrow0 : Finset (Fin L) :=
    ((∅ : Finset (Fin m × Fin L)).filter (fun r => r.1 = cstar)).image Prod.snd with hSCrow0
  -- side conditions on the target block
  have hEside : ∀ k : Fin L, (cstar, k) ∈ E → xbit hfit cstar k ∉ Sᶜ :=
    fun k hk => absurd hk (hEcstar k)
  have hE'side : ∀ k : Fin L, (cstar, k) ∈ E' → xbit hfit cstar k ∉ Sᶜ := by
    intro k hk
    have hkm : k ∈ Finset.univ.filter (fun k => (cstar, k) ∈ E') :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    rw [hE'sel, Finset.mem_singleton] at hkm
    rw [hkm]; exact hpos
  have hSCrow : ∀ k ∈ SCrow0, xbit hfit cstar k ∉ Sᶜ := by
    intro k hk
    rw [hSCrow0] at hk
    simp at hk
  -- the row reads at the target block
  have hyE : ∀ k : Fin L, xbit hfit cstar k ∉ Sᶜ →
      (rowOf hfit tautIdx PB ∅ E (xbit hfit cstar k) = true
        ↔ ((cstar, k) ∈ E ∨ k ∈ SCrow0)) := by
    intro k hk
    exact rowOf_read_target hfit tautIdx PB ∅ V S hVt E hE hTautProbe k hk
  have hyE' : ∀ k : Fin L, xbit hfit cstar k ∉ Sᶜ →
      (rowOf hfit tautIdx PB ∅ E' (xbit hfit cstar k) = true
        ↔ ((cstar, k) ∈ E' ∨ k ∈ SCrow0)) := by
    intro k hk
    exact rowOf_read_target hfit tautIdx PB ∅ V S hVt E' hE' hTautProbe k hk
  -- the target decodes
  have hdE := gDecode_target code hfit tautIdx pinIdx SC KB PB cstar S
    (rowOf hfit tautIdx PB ∅ E) E SCrow0 hKnc hPnc hEside hSCrow hyE
  have hdE' := gDecode_target code hfit tautIdx pinIdx SC KB PB cstar S
    (rowOf hfit tautIdx PB ∅ E') E' SCrow0 hKnc hPnc hE'side hSCrow hyE'
  have hEfilter : Finset.univ.filter (fun k : Fin L => (cstar, k) ∈ E) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k _
    exact hEcstar k
  -- hBk'
  have hBk' : gDecodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
          (rowOf hfit tautIdx PB ∅ E')) cstar
      = gDecodeBlock code hfit
          (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
            (rowOf hfit tautIdx PB ∅ E)) cstar ∪ {GLit.quad i j 1} := by
    rw [hdE, hdE', hEfilter, hE'sel, Finset.union_empty, Finset.image_union,
      Finset.image_union, Finset.image_singleton, hcode]
  -- the reserve blocks decode identically (both to the singleton pin)
  have hpinDecode : ∀ (E₀ : Finset (Fin m × Fin L)), E₀ ⊆ V → ∀ c, c ∈ PB →
      gDecodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
          (rowOf hfit tautIdx PB ∅ E₀)) c
      = {GLit.aff (single v i + single v j) 0} := by
    intro E₀ hE₀ c hc
    have hcs : c ≠ cstar := fun h => hPnc (h ▸ hc)
    rw [gDecode_pin_eq code hfit tautIdx pinIdx SC KB PB cstar S
        (rowOf hfit tautIdx PB ∅ E₀) hc (hKP c hc) hcs (hlive c hc)
        (fun k => rowOf_read_reserve hfit tautIdx PB ∅ V hVRS
          (fun q hq => absurd hq (Finset.notMem_empty q)) E₀ hE₀ hc k)]
    rw [hpinCode c hc]
  have hres : ∀ c, c ∈ PB →
      gDecodeBlock code hfit
          (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
            (rowOf hfit tautIdx PB ∅ E')) c
      = gDecodeBlock code hfit
          (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
            (rowOf hfit tautIdx PB ∅ E)) c := by
    intro c hc
    rw [hpinDecode E' hE' c hc, hpinDecode E hE c hc]
  -- kit blanket
  have hkit : ∀ (E₀ : Finset (Fin m × Fin L)), ∀ c, c ≠ cstar → c ∉ PB →
      GLit.aff 0 0 ∈ gDecodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
          (rowOf hfit tautIdx PB ∅ E₀)) c := by
    intro E₀ c hcs hcPB
    have hcKB : c ∈ KB := (hcover c hcs).resolve_right hcPB
    exact gDecode_kit_mem code hfit tautIdx pinIdx SC KB PB cstar S
      (rowOf hfit tautIdx PB ∅ E₀) hcKB hcodeTaut
      (rowOf_read_kit hfit tautIdx PB ∅ E₀ hcPB)
  -- hpair
  have hpair : ∀ a : Fin v → ZMod 2,
      ((∀ c, c ≠ cstar → gBlockSat a (gDecodeBlock code hfit
          (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
            (rowOf hfit tautIdx PB ∅ E)) c))
        ∧ ∀ ℓ ∈ gDecodeBlock code hfit
            (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
              (rowOf hfit tautIdx PB ∅ E)) cstar, ¬ gLitHolds a ℓ)
        ↔ (a = 0 ∨ a = single v i + single v j) := by
    intro a
    have hTsh : gDecodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
          (rowOf hfit tautIdx PB ∅ E)) cstar
      = (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1) := by
      rw [hdE]; exact hScaf
    rw [hTsh]
    exact homogeneous_hpair_kit i j hij cstar PB c₀ hc₀ hc₀cs
      (fun c => gDecodeBlock code hfit
        (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
          (rowOf hfit tautIdx PB ∅ E)) c)
      (fun c hc => hpinDecode E hE c hc)
      (fun c hcs hcPB => hkit E c hcs hcPB) a
  -- h0t'
  have h0t' : ∀ ℓ ∈ ({GLit.quad i j 1} : Finset (GLit v)), ¬ gLitHolds 0 ℓ := by
    intro ℓ hℓ
    rw [Finset.mem_singleton] at hℓ
    subst hℓ
    change ¬ ((0 : Fin v → ZMod 2) i * (0 : Fin v → ZMod 2) j = 1)
    simp
  exact gParity_pair_dist_multi code hfit S
    (probeOn hfit tautIdx pinIdx SC KB PB cstar)
    (rowOf hfit tautIdx PB ∅ E) (rowOf hfit tautIdx PB ∅ E')
    cstar i j (single v i + single v j)
    (gDecodeBlock code hfit
      (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC KB PB cstar)
        (rowOf hfit tautIdx PB ∅ E)) cstar)
    ∅ {GLit.quad i j 1} PB
    (origin_w_flip i j hij)
    (Finset.union_empty _).symm hBk' (Finset.mem_singleton_self _)
    (fun ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ)) h0t'
    (fun ℓ hℓ => absurd hℓ (Finset.notMem_empty ℓ))
    hres
    (fun c hcs hcPB => hkit E c hcs hcPB)
    (fun c hcs hcPB => hkit E' c hcs hcPB)
    hpair

set_option maxHeartbeats 3200000 in
/-- **THE DISCHARGED DRAG (proved)**: with one priced position per block, the product tuple
family prices `V.card ≤ j` against a cut factorization of the concrete construction. -/
theorem gParity_quad_drag (code : Fin L → GLit v) (hfit : m * L ≤ N)
    (tautIdx : Fin L) (pinIdx : Fin m → Fin L) (SC : Finset (Fin L))
    (PB : Finset (Fin m)) (c₀ : Fin m) (istar0 : Fin L) (i j : Fin v) (hij : i ≠ j)
    {S : Finset (Fin N)} {jj : ℕ}
    (hcut : CutFactorization (gParityFamilyBits code hfit) S jj)
    (V : Finset (Fin m × Fin L))
    (hcodeTaut : code tautIdx = GLit.aff 0 0)
    (hcodeStar : ∀ q ∈ V, code q.2 = GLit.quad i j 1)
    (hpinCode : ∀ c, c ∈ PB → code (pinIdx c) = GLit.aff (single v i + single v j) 0)
    (hc₀ : c₀ ∈ PB)
    (hVt : ∀ q ∈ V, q.2 ≠ tautIdx) (hVRS : ∀ q ∈ V, q.1 ∉ PB)
    (hVone : ∀ q ∈ V, ∀ q' ∈ V, q.1 = q'.1 → q = q')
    (hTautProbeAll : ∀ c, xbit hfit c tautIdx ∈ Sᶜ)
    (hlive : ∀ c, c ∈ PB → xbit hfit c (pinIdx c) ∈ Sᶜ)
    (hVS : ∀ q ∈ V, xbit hfit q.1 q.2 ∉ Sᶜ)
    (hScafAll : ∀ c, (SC.filter (fun k => xbit hfit c k ∈ Sᶜ)).image code
      = (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1)) :
    V.card ≤ jj := by
  classical
  apply gParity_tuple_drag code hfit hcut V (fun E => rowOf hfit tautIdx PB ∅ E)
  · -- hrow_read
    intro E hE q hq
    exact rowOf_read_V hfit tautIdx PB ∅ V hVt
      (fun q hq => Finset.notMem_empty q) E (Finset.mem_powerset.mp hE) hq
  · -- hdist, via gParity_quad_pair
    intro E hEpow E' hE'pow hne
    have hEsub := Finset.mem_powerset.mp hEpow
    have hE'sub := Finset.mem_powerset.mp hE'pow
    -- a differing position
    have hdiff : ∃ q, (q ∈ E' ∧ q ∉ E) ∨ (q ∈ E ∧ q ∉ E') := by
      by_contra hcon
      push_neg at hcon
      apply hne
      ext q
      exact ⟨fun hq => (hcon q).2 hq, fun hq => (hcon q).1 hq⟩
    -- the per-target discharge, given the roles
    have core : ∀ (A B : Finset (Fin m × Fin L)) (hA : A ⊆ V) (hB : B ⊆ V)
        (q₀ : Fin m × Fin L) (hq₀B : q₀ ∈ B) (hq₀A : q₀ ∉ A) (hq₀V : q₀ ∈ V),
        gParityFamilyBits code hfit
            (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC ((Finset.univ \ PB).erase q₀.1) PB q₀.1)
              (rowOf hfit tautIdx PB ∅ A))
          ≠ gParityFamilyBits code hfit
            (mixOn Sᶜ (probeOn hfit tautIdx pinIdx SC ((Finset.univ \ PB).erase q₀.1) PB q₀.1)
              (rowOf hfit tautIdx PB ∅ B)) := by
      intro A B hA hB q₀ hq₀B hq₀A hq₀V
      have hq₀PB : q₀.1 ∉ PB := hVRS q₀ hq₀V
      have hAcstar : ∀ k, (q₀.1, k) ∉ A := by
        intro k hk
        have hmem : (q₀.1, k) ∈ V := hA hk
        have := hVone q₀ hq₀V (q₀.1, k) hmem rfl
        exact hq₀A (this ▸ hk)
      have hBsel : Finset.univ.filter (fun k => (q₀.1, k) ∈ B) = {q₀.2} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hk
          have hmem : (q₀.1, k) ∈ V := hB hk
          have := hVone q₀ hq₀V (q₀.1, k) hmem rfl
          exact (congrArg Prod.snd this).symm
        · intro hk
          rw [hk]
          exact hq₀B
      have hScaf : (((SC.filter (fun k => xbit hfit q₀.1 k ∈ Sᶜ))
          ∪ ((∅ : Finset (Fin m × Fin L)).filter (fun r => r.1 = q₀.1)).image Prod.snd)
          ∪ (Finset.univ.filter (fun k => (q₀.1, k) ∈ A))).image code
        = (Finset.univ \ {i, j}).image (fun k => GLit.aff (single v k) 1) := by
        have hAf : Finset.univ.filter (fun k : Fin L => (q₀.1, k) ∈ A) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro k _; exact hAcstar k
        rw [hAf]
        simp only [Finset.filter_empty, Finset.image_empty, Finset.union_empty]
        exact hScafAll q₀.1
      exact gParity_quad_pair code hfit tautIdx pinIdx SC
        ((Finset.univ \ PB).erase q₀.1) PB q₀.1 c₀ q₀.2 i j hij S V A B
        hcodeTaut (hcodeStar q₀ hq₀V) hpinCode
        (by
          intro c hc
          by_cases hcPB : c ∈ PB
          · exact Or.inr hcPB
          · exact Or.inl (Finset.mem_erase.mpr ⟨hc,
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcPB⟩⟩))
        (by
          intro c hc hcKB
          exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hcKB)).2 hc)
        (Finset.notMem_erase _ _) hq₀PB hc₀
        hVt hVRS hA hB hAcstar hBsel
        (hTautProbeAll q₀.1) hlive (hVS q₀ hq₀V) hScaf
    obtain ⟨q₀, hcase⟩ := hdiff
    rcases hcase with ⟨hq₀E', hq₀E⟩ | ⟨hq₀E, hq₀E'⟩
    · exact ⟨probeOn hfit tautIdx pinIdx SC ((Finset.univ \ PB).erase q₀.1) PB q₀.1,
        core E E' hEsub hE'sub q₀ hq₀E' hq₀E (hE'sub hq₀E')⟩
    · exact ⟨probeOn hfit tautIdx pinIdx SC ((Finset.univ \ PB).erase q₀.1) PB q₀.1,
        (core E' E hE'sub hEsub q₀ hq₀E hq₀E' (hEsub hq₀E)).symm⟩

end PallLean.Paper93.DeepMath.PathB.NFrameQuadPair

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadPair.gParity_quad_pair
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadPair.gParity_quad_drag
